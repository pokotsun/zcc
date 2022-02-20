// This file contains a recursive descent parser for C.
//
// Most functions in this file are named after the symbols they are
// supposed to read from an input token list. For example, stmt() is
// responsible for reading a statement from a token list. The function
// then construct an AST representing a statement.
//
// Each function conceptually returns two values, an AST node and
// remaining part of the input tokens. Since C doesn't support
// multiple return values, the remaining tokens are returned to the
// caller via a pointer argument.
//
// Input tokens are represented by a linked list. Unlike many recursive
// descent parsers, we don't have the notion of the "input token stream".
// Most parsing functions don't change the global state of the parser.
// So it is very easy to lookahead arbitrary number of tokens in this parser.

use crate::tokenize::error_tok;
use crate::tokenize::{consume, is_typename, next_equal, skip, Token, TokenKind};
use crate::types::{FuncParam, Type, TypeKind};
use crate::util::align_to;
use crate::{
    node::{BinOp, Member, Node, NodeKind, TagScope, UnaryOp, Var, VarType},
    util::LabelCounter,
};
use std::cell::RefCell;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::slice::Iter;
use std::{iter::Peekable, rc::Rc, unimplemented};

pub struct Function {
    pub name: String,
    pub params: VecDeque<Rc<Var>>,
    pub body: Node, // Block or statement expression
    #[allow(dead_code)]
    locals: VecDeque<Rc<Var>>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(name: String, params: VecDeque<Rc<Var>>, body: Node, locals: VecDeque<Rc<Var>>) -> Self {
        let mut offset = 32;
        for local in locals.iter() {
            offset = align_to(offset, local.ty.borrow().align);
            offset += local.ty.borrow().size;
            if let VarType::Local(var_offset) = local.var_ty.clone() {
                var_offset.set(offset);
            }
        }
        let stack_size = align_to(offset, 16);

        Self {
            name,
            params,
            body,
            locals,
            stack_size,
        }
    }
}

pub struct Program {
    pub fns: Vec<Function>,
    pub globals: VecDeque<Rc<Var>>,
}

impl Program {
    fn new(fns: Vec<Function>, globals: VecDeque<Rc<Var>>) -> Self {
        Self { fns, globals }
    }
}

pub struct Parser<'a> {
    tok_peek: Peekable<Iter<'a, Token>>,
    locals: VecDeque<Rc<Var>>,
    // Likewise, global variables are accumulated to this list.
    globals: VecDeque<Rc<Var>>,
    // C has two block scopes; one is for variables and the other is
    // for struct tags.
    var_scope: VecDeque<Rc<Var>>,
    tag_scope: VecDeque<Rc<TagScope>>,
    scope_depth: usize,
    data_idx: LabelCounter,
}

impl<'a> Parser<'a> {
    fn new(tok_peek: Peekable<Iter<'a, Token>>) -> Self {
        Self {
            tok_peek,
            locals: VecDeque::new(),
            globals: VecDeque::new(),
            var_scope: VecDeque::new(),
            tag_scope: VecDeque::new(),
            scope_depth: 0,
            data_idx: LabelCounter::new(),
        }
    }

    fn new_unique_name(&mut self) -> String {
        let idx = self.data_idx.next().unwrap();
        format!(".L.data.{}", idx)
    }

    fn find_var(&self, name: &str) -> Option<Rc<Var>> {
        self.var_scope
            .iter()
            .find(|x| x.name == name && x.scope_depth <= self.scope_depth)
            .map(|var| var.clone())
    }

    fn find_tag(&self, name: &str) -> Option<Rc<TagScope>> {
        self.tag_scope
            .iter()
            .find(|x| x.name == name && x.scope_depth <= self.scope_depth)
            .map(|var| var.clone())
    }

    fn enter_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn leave_scope(&mut self) {
        self.scope_depth -= 1;

        while let Some(_) = self
            .var_scope
            .get(0)
            .filter(|x| x.scope_depth > self.scope_depth)
        {
            self.var_scope.pop_front();
        }

        while let Some(_) = self
            .tag_scope
            .get(0)
            .filter(|x| x.scope_depth > self.scope_depth)
        {
            self.tag_scope.pop_front();
        }
    }

    // program = (funcdef | global-var)*
    pub fn parse(tok_peek: Peekable<Iter<Token>>) -> Program {
        // All local variable instances created during parsing are
        // accumulated to this list.
        let mut parser = Parser::new(tok_peek);
        let mut funcs = Vec::new();
        while let Some(_) = parser.tok_peek.peek() {
            let basety = Rc::new(RefCell::new(parser.typespec()));
            let (mut ty, mut name) = parser.declarator(basety);

            let ty_kind = ty.borrow().kind.clone();
            match &*ty_kind {
                TypeKind::Func { .. } => {
                    if consume(&mut parser.tok_peek, ";") {
                        continue;
                    }
                    let func = parser.typed_funcdef(ty, name);
                    funcs.push(func);
                }
                _ => {
                    // Global variable
                    loop {
                        let var = Var::new_gvar(name, ty.clone(), Vec::new());
                        let var = Rc::new(var);
                        parser.var_scope.push_front(var.clone());
                        parser.globals.push_front(var);
                        if consume(&mut parser.tok_peek, ";") {
                            break;
                        } else {
                            skip(&mut parser.tok_peek, ",");
                            let declare = parser.declarator(ty);
                            ty = declare.0;
                            name = declare.1;
                        }
                    }
                }
            }
        }
        Program::new(funcs, parser.globals)
    }

    // funcdef = typespec declarator compound-stmt
    #[allow(dead_code)]
    fn funcdef(&mut self) -> Function {
        let ty = Rc::new(RefCell::new(self.typespec()));
        let (ty, func_name) = self.declarator(ty);

        self.typed_funcdef(ty, func_name)
    }

    // 既に関数の返り値と関数名が得られた場合の関数の中身を取り出す
    // 主にcompoud-stmtの処理を行う
    // typed-funcdef = typespec declarator compound-stmt
    fn typed_funcdef(&mut self, ty: Rc<RefCell<Type>>, func_name: String) -> Function {
        self.enter_scope();

        let mut var_params = VecDeque::new();
        if let TypeKind::Func {
            return_ty: _,
            params,
        } = ty.borrow().kind.as_ref()
        {
            for (ty, var_name) in params.iter() {
                // offsetは関数内の全変数が出揃わないとoffsetを用意できないため
                // 一旦無効な値0を入れる
                let var = Var::new_lvar(var_name.clone(), 0, ty.clone(), self.scope_depth);
                let var = Rc::new(var);
                var_params.push_front(var.clone());
                self.var_scope.push_front(var.clone());
                self.locals.push_front(var);
            }
        }

        skip(&mut self.tok_peek, "{");
        let body = self.compound_stmt();
        self.leave_scope();

        Function::new(func_name, var_params, body, self.locals.clone())
    }

    // typespec = typename typename*
    // typename = "void" | "char" | "short" | "int" | "long"
    //          | struct-decl | union-decl
    //
    // The order of typenames in a type-specifier doesn't matter. For
    // example, `int long static` means the same as `static long int`.
    // That can also be written as `static long` because you can omit
    // `int` if `long` or `short` are specified. However, something like
    // `char int` is no a valid type specifier. We have to accept only a
    // limited combinations of the typenames.
    //
    // In this function, we count the number of occurrences of each typename
    // while keeping the "current" type object that the typenames up
    // until that point represent. When we reach a non-typename token,
    // we returns the current type object.
    fn typespec(&mut self) -> Type {
        #[derive(PartialEq, Eq, Hash)]
        enum TypeSpec {
            Void,
            Char,
            Short,
            Int,
            Long,
            Other,
        }
        let mut rtn_ty: Option<Type> = None;
        let mut type_counter = HashSet::new();
        while is_typename(&mut self.tok_peek) {
            // Handle user-defined types.
            // NOTE. なんでOtherの情報も保持しないといけないのか謎
            if consume(&mut self.tok_peek, "struct") {
                rtn_ty = Some(self.struct_decl());
                type_counter.insert(TypeSpec::Other);
                continue;
            }
            if consume(&mut self.tok_peek, "union") {
                rtn_ty = Some(self.union_decl());
                type_counter.insert(TypeSpec::Other);
                continue;
            }

            // Handle built-in types.
            if consume(&mut self.tok_peek, "void") {
                type_counter.insert(TypeSpec::Void);
            } else if consume(&mut self.tok_peek, "char") {
                type_counter.insert(TypeSpec::Char);
            } else if consume(&mut self.tok_peek, "short") {
                type_counter.insert(TypeSpec::Short);
            } else if consume(&mut self.tok_peek, "int") {
                type_counter.insert(TypeSpec::Int);
            } else if consume(&mut self.tok_peek, "long") {
                type_counter.insert(TypeSpec::Long);
            } else {
                unimplemented!("internal error.");
            }

            rtn_ty = if type_counter.contains(&TypeSpec::Void) {
                Some(Type::new_void())
            } else if type_counter.contains(&TypeSpec::Char) {
                Some(Type::new_char())
            } else if type_counter.contains(&TypeSpec::Short)
                || (type_counter.contains(&TypeSpec::Short)
                    && type_counter.contains(&TypeSpec::Int))
            {
                Some(Type::new_short())
            } else if type_counter.contains(&TypeSpec::Long)
                || (type_counter.contains(&TypeSpec::Long) && type_counter.contains(&TypeSpec::Int))
            {
                Some(Type::new_long())
            } else if type_counter.contains(&TypeSpec::Int) {
                Some(Type::new_int())
            } else {
                unimplemented!("invalid type");
            };
        }

        return match rtn_ty {
            Some(ty) => ty,
            None => unimplemented!("not gained any type"),
        };
    }

    // func-params = (param ("," param)*)? ")"
    // param = typespec declarator
    fn func_params(&mut self, ty: Rc<RefCell<Type>>) -> Type {
        let mut params = Vec::new();
        while !next_equal(&mut self.tok_peek, ")") {
            if params.len() > 0 {
                skip(&mut self.tok_peek, ",");
            }
            let basety = Rc::new(RefCell::new(self.typespec()));
            let (ty, var_name) = self.declarator(basety);
            params.push((ty, var_name));
        }
        skip(&mut self.tok_peek, ")");
        return Type::new_func(ty.borrow().kind.clone(), params);
    }

    // type-suffix = "(" func-params
    //             | "[" num "]"
    //             | "[" num "]" type-suffix
    //             | sigma
    fn type_suffix(&mut self, ty: Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        if next_equal(&mut self.tok_peek, "(") {
            skip(&mut self.tok_peek, "(");
            return Rc::new(RefCell::new(Self::func_params(self, ty)));
        }
        if next_equal(&mut self.tok_peek, "[") {
            skip(&mut self.tok_peek, "[");
            if let Some(size) = self.tok_peek.next().and_then(|tok| tok.get_number()) {
                skip(&mut self.tok_peek, "]");
                let ty = self.type_suffix(ty);
                return Rc::new(RefCell::new(Type::array_of(ty, size as usize)));
            } else {
                unimplemented!("Array length is not specified.");
            }
        }
        ty
    }

    // declarator = "*"* ("(" declarator ")" | ident) type-suffix
    fn declarator(&mut self, mut ty: Rc<RefCell<Type>>) -> FuncParam {
        // FIXME なんか凄く汚い
        while consume(&mut self.tok_peek, "*") {
            ty = Rc::new(RefCell::new(Type::pointer_to(ty)));
        }
        if next_equal(&mut self.tok_peek, "(") {
            skip(&mut self.tok_peek, "(");
            // とりあえず適当な値を入れておく
            let mut place_holder = Rc::new(RefCell::new(Type::new_dummy()));

            let new_ty = self.declarator(place_holder.clone());
            skip(&mut self.tok_peek, ")");

            // 最後に型の中身を置き換える
            while let TypeKind::Ptr(child) = (place_holder.clone()).borrow().kind.as_ref() {
                place_holder = child.clone();
            }
            *place_holder.borrow_mut() = self.type_suffix(ty).borrow().clone();

            return new_ty;
        }

        let tok = self.tok_peek.next().unwrap();
        if !matches!(tok.kind, TokenKind::Ident(_)) {
            error_tok(tok, "invalid pointer dereference");
        }
        ty = self.type_suffix(ty);
        (ty, tok.word.clone())
    }

    // declaration = typespec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self) -> Node {
        let basety = Rc::new(RefCell::new(self.typespec()));

        let mut is_already_declared = false;
        let mut nodes = Vec::new();
        while !next_equal(&mut self.tok_peek, ";") {
            if is_already_declared {
                skip(&mut self.tok_peek, ",");
            }
            is_already_declared = true;

            let (ty, name) = Self::declarator(self, basety.clone());
            if let TypeKind::Void = ty.borrow().kind.as_ref() {
                unimplemented!("variable declared void");
            }
            // offsetは関数内の全変数が出揃わないとoffsetを用意できないため
            // 一旦無効な値0を入れる
            let var = Var::new_lvar(name, 0, ty, self.scope_depth);
            let var = Rc::new(var);
            let rcvar = var.clone();
            self.var_scope.push_front(var.clone());
            self.locals.push_front(var);

            if !next_equal(&mut self.tok_peek, "=") {
                continue;
            }
            let lhs = Node::new_var_node(rcvar);
            self.tok_peek.next(); // "=" tokenを飛ばす
            let rhs = Self::assign(self);
            let node = Node::new_bin(BinOp::Assign, lhs, rhs);
            let node = Node::new_unary(UnaryOp::ExprStmt, node);
            nodes.push(node);
        }
        let node = Node::new_block_node(nodes);
        node
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(&mut self) -> Node {
        if next_equal(&mut self.tok_peek, "return") {
            self.tok_peek.next();
            let node = Node::new_unary(UnaryOp::Return, Self::expr(self));
            skip(&mut self.tok_peek, ";");
            return node;
        }

        if next_equal(&mut self.tok_peek, "if") {
            self.tok_peek.next();
            skip(&mut self.tok_peek, "(");
            let cond = Self::expr(self);
            skip(&mut self.tok_peek, ")");
            let then = Self::stmt(self);

            let els = self
                .tok_peek
                .peek()
                .and_then(|next_tok| Some(next_tok.clone()))
                .filter(|next_tok| next_tok.equal("else"))
                .map(|_| {
                    self.tok_peek.next();
                    self.stmt()
                });
            return Node::new_if(cond, then, els);
        }

        if next_equal(&mut self.tok_peek, "for") {
            self.tok_peek.next();
            skip(&mut self.tok_peek, "(");

            let init = Self::expr_stmt(self);

            let next_tok = self.tok_peek.peek().map(|x| (*x).clone());
            let cond = next_tok
                .filter(|tok| !tok.equal(";"))
                .map(|_| Self::expr(self));
            skip(&mut self.tok_peek, ";");

            let next_tok = self.tok_peek.peek().map(|x| (*x).clone());
            let inc = next_tok
                .filter(|tok| !tok.equal(")"))
                .map(|_| Self::expr(self));
            skip(&mut self.tok_peek, ")");

            let then = Self::stmt(self);
            return Node::new_for(cond, then, init, inc);
        }

        if next_equal(&mut self.tok_peek, "while") {
            self.tok_peek.next();
            skip(&mut self.tok_peek, "(");
            let cond = Self::expr(self);
            skip(&mut self.tok_peek, ")");
            let then = Self::stmt(self);
            return Node::new_while(cond, then);
        }

        if next_equal(&mut self.tok_peek, "{") {
            self.tok_peek.next();
            return self.compound_stmt();
        }
        Self::expr_stmt(self)
    }

    // compound-stmt = (declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Node {
        let mut nodes = vec![];

        self.enter_scope();

        while !next_equal(&mut self.tok_peek, "}") {
            let node = if is_typename(&mut self.tok_peek) {
                Self::declaration(self)
            } else {
                Self::stmt(self)
            };
            nodes.push(node);
        }

        skip(&mut self.tok_peek, "}");

        self.leave_scope();

        Node::new_block_node(nodes)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(&mut self) -> Node {
        // FIXME Nullのため, OptionかNoneという処理を入れたほうが良い?
        if next_equal(&mut self.tok_peek, ";") {
            self.tok_peek.next();
            return Node::new_block_node(vec![]);
        }

        let node = Node::new_unary(UnaryOp::ExprStmt, Self::expr(self));
        skip(&mut self.tok_peek, ";");
        return node;
    }

    // expr = assign ("," expr)?
    fn expr(&mut self) -> Node {
        let node = self.assign();
        while next_equal(&mut self.tok_peek, ",") {
            self.tok_peek.next();
            return Node::new_bin(BinOp::Comma, node, self.expr());
        }
        node
    }

    // assign = equality ("=" assign)?
    fn assign(&mut self) -> Node {
        let mut node = Self::equality(self);
        let tok = self.tok_peek.peek().unwrap();
        if tok.equal("=") {
            self.tok_peek.next();
            node = Node::new_bin(BinOp::Assign, node, Self::assign(self));
        }
        node
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(&mut self) -> Node {
        let mut node = Self::relational(self);

        loop {
            let tok = self.tok_peek.peek().unwrap();
            if tok.equal("==") {
                self.tok_peek.next();
                let rhs = Self::relational(self);
                node = Node::new_bin(BinOp::Equal, node, rhs);
                continue;
            }
            if tok.equal("!=") {
                self.tok_peek.next();
                let rhs = Self::relational(self);
                node = Node::new_bin(BinOp::NEqual, node, rhs);
                continue;
            }
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(&mut self) -> Node {
        let mut node = Self::add(self);

        loop {
            let tok = self.tok_peek.peek().unwrap();
            if tok.equal("<") {
                self.tok_peek.next();
                let rhs = Self::add(self);
                node = Node::new_bin(BinOp::Lt, node, rhs);
                continue;
            }

            if tok.equal("<=") {
                self.tok_peek.next();
                let rhs = Self::add(self);
                node = Node::new_bin(BinOp::Le, node, rhs);
                continue;
            }
            if tok.equal(">") {
                self.tok_peek.next();
                let rhs = Self::add(self);
                node = Node::new_bin(BinOp::Lt, rhs, node);
                continue;
            }
            if tok.equal(">=") {
                self.tok_peek.next();
                let rhs = Self::add(self);
                node = Node::new_bin(BinOp::Le, rhs, node);
                continue;
            }
            return node;
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(&mut self) -> Node {
        let mut node = self.mul();
        loop {
            let tok = self.tok_peek.peek().unwrap();
            if tok.equal("+") {
                self.tok_peek.next();
                let rhs = Self::mul(self);
                node = Node::new_add(node, rhs);
                continue;
            }
            if tok.equal("-") {
                self.tok_peek.next();
                let rhs = Self::mul(self);
                node = Node::new_sub(node, rhs);
                continue;
            }
            return node;
        }
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(&mut self) -> Node {
        let mut node = self.unary();

        loop {
            let tok = self.tok_peek.peek().unwrap();
            if tok.equal("*") {
                self.tok_peek.next();
                let rhs = Self::unary(self);
                node = Node::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                self.tok_peek.next();
                let rhs = Self::unary(self);
                node = Node::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // unary = ("+" | "-" | "*" | "&") unary
    //       | postfix
    fn unary(&mut self) -> Node {
        let tok = self.tok_peek.peek().unwrap();
        if tok.equal("+") {
            self.tok_peek.next();
            return Self::unary(self);
        }
        if tok.equal("-") {
            self.tok_peek.next();
            return Node::new_bin(BinOp::Sub, Node::new(NodeKind::Num(0)), Self::unary(self));
        }
        if tok.equal("&") {
            self.tok_peek.next();
            return Node::new_unary(UnaryOp::Addr, Self::unary(self));
        }

        if tok.equal("*") {
            self.tok_peek.next();
            return Node::new_unary(UnaryOp::Deref, Self::unary(self));
        }

        return Self::postfix(self);
    }

    // struct-members = (typespec declarator ("," declarator)* ";")*
    fn struct_members(&mut self) -> Vec<Member> {
        let mut members = Vec::new();
        while !next_equal(&mut self.tok_peek, "}") {
            let basety = Rc::new(RefCell::new(self.typespec()));
            let mut is_first_member = true;

            while !consume(&mut self.tok_peek, ";") {
                if !is_first_member {
                    skip(&mut self.tok_peek, ",");
                }
                is_first_member = false;

                let (ty, name) = self.declarator(basety.clone());
                // とりあえずoffsetには適当な値を入れておく
                // TODO ここはその場でoffsetを入れられそう
                let member = Member::new(ty, name, 0);
                members.push(member);
            }
        }
        skip(&mut self.tok_peek, "}");
        members
    }

    // struct-union-decl = ident? ("{" struct-members)?
    fn struct_union_decl(&mut self, member_align: fn(&mut Vec<Member>) -> (usize, usize)) -> Type {
        // Read struct tag.

        let tag_name = self
            .tok_peek
            .peek()
            .filter(|x| x.word != "{")
            .map(|x| x.word.clone())
            .and_then(|x| {
                // identifierかつ"{"じゃないことが確定
                // よって, struct tagのはずなので, skip.
                self.tok_peek.next();
                Some(x)
            });

        // tag_nameが有効かつ, 次のtokenが'{'でなければ, 定義済みのtagを指しているはずなので
        // find_tagで探し, 見つからなければunimplemented!を返す.
        if let Some(tag_scope) = tag_name
            .as_ref()
            .filter(|_| !next_equal(&mut self.tok_peek, "{"))
            .map(|x| self.find_tag(x))
        {
            match tag_scope {
                Some(tag_scope) => return tag_scope.ty.clone(),
                None => unimplemented!("tag: '{}' is unknown struct type.", tag_name.unwrap()),
            }
        }

        skip(&mut self.tok_peek, "{");

        // Construct a struct object.
        let mut members = self.struct_members();

        let (offset, struct_align) = member_align(&mut members);

        let members_ty = Type::new_struct(members, align_to(offset, struct_align), struct_align);

        // Register the struct / union type if a name was given.
        if let Some(tag_name) = tag_name {
            let tag_scope = TagScope::new(tag_name, self.scope_depth, members_ty.clone());
            self.tag_scope.push_front(Rc::new(tag_scope));
        }

        members_ty
    }

    // struct-decl
    // closure returns (struct total size, struct total align size)
    fn struct_decl(&mut self) -> Type {
        let member_align = |members: &mut Vec<Member>| {
            // If struct, we have to assign offsets.
            // and we need to compute the alignment and the size.
            let mut offset: usize = 0;
            members.iter().for_each(|member| {
                offset = align_to(offset, member.ty.borrow().align);
                member.offset.set(offset);
                offset += member.ty.borrow().size;
            });

            let struct_align = members
                .iter()
                .max_by_key(|member| member.ty.borrow().align)
                .map_or(0, |x| x.ty.borrow().align);

            (offset, struct_align)
        };

        let member_ty = self.struct_union_decl(member_align);

        member_ty
    }

    // union-decl
    // closure returns (struct total size, struct total align size)
    fn union_decl(&mut self) -> Type {
        // If union, we don't have to assign offsets because they
        // are already initialized to zero.
        // We need to compute the alignment and the size though.

        let member_align = |members: &mut Vec<Member>| {
            let union_align = members
                .iter()
                .max_by_key(|member| member.ty.borrow().align)
                .map_or(0, |x| x.ty.borrow().align);
            let union_size = members
                .iter()
                .max_by_key(|member| member.ty.borrow().size)
                .map_or(0, |x| x.ty.borrow().size);

            let union_size = align_to(union_size, union_align);

            (union_size, union_align)
        };

        let member_ty = self.struct_union_decl(member_align);

        member_ty
    }

    // TODO この2つの関数はparserの中に無くても良いかも
    fn get_struct_member(members: Vec<Member>, member_name: String) -> Member {
        members
            .iter()
            .find(|x| x.name == member_name)
            .expect("no such member.")
            .clone()
    }

    fn struct_ref(node: Node, member_name: String) -> Node {
        if let TypeKind::Struct { members } = node.get_type_ref().borrow().kind.as_ref().clone() {
            let member = Self::get_struct_member(members, member_name);
            return Node::new_unary(UnaryOp::Member(member), node);
        }
        unimplemented!("struct_ref is not struct:\n{:#?}", node);
    }

    // postfix = primary ("[" expr "]" | "." ident | "->" ident)*
    fn postfix(&mut self) -> Node {
        let mut node = self.primary();

        loop {
            if next_equal(&mut self.tok_peek, "[") {
                skip(&mut self.tok_peek, "[");
                // x[idx] is *(x + idx)
                let idx = Self::expr(self);
                skip(&mut self.tok_peek, "]");
                node = Node::new_unary(UnaryOp::Deref, Node::new_add(node, idx));
                continue;
            }
            if next_equal(&mut self.tok_peek, ".") {
                skip(&mut self.tok_peek, ".");
                let tok = self.tok_peek.next().unwrap();
                let member_name = tok.word.clone();
                node = Self::struct_ref(node, member_name);
                continue;
            }

            if next_equal(&mut self.tok_peek, "->") {
                // x->y is short for (*x).y
                skip(&mut self.tok_peek, ".");
                let tok = self.tok_peek.next().unwrap();
                let member_name = tok.word.clone();
                node = Self::struct_ref(Node::new_unary(UnaryOp::Deref, node), member_name);
                continue;
            }
            return node;
        }
    }

    // funcall = ident "(" (assign (",", assign)*)? ")"
    //
    // foo(a,b,c) is compiled to (t1=a, t2=b, t3=c, foo(t1, t2, t3))
    // where t1, t2 and t3 are fresh temporal local variables
    fn funcall(&mut self, func_name: String) -> Node {
        skip(&mut self.tok_peek, "(");

        let mut node = Node::new(NodeKind::NullExpr);
        let mut args = Vec::new();
        while !next_equal(&mut self.tok_peek, ")") {
            if args.len() > 0 {
                skip(&mut self.tok_peek, ",");
            }
            let arg = Self::assign(self);
            let mut base = arg.get_type_ref();

            if base.borrow().is_ptr() {
                base = Rc::new(RefCell::new(Type::pointer_to(base)));
            }

            let var = Var::new_lvar("".to_string(), 0, base, self.scope_depth);
            let var = Rc::new(var);
            let expr = Node::new_bin(BinOp::Assign, Node::new_var_node(var.clone()), arg);
            args.push(var.clone());
            self.locals.push_front(var);
            node = Node::new_bin(BinOp::Comma, node, expr);
        }

        skip(&mut self.tok_peek, ")");

        let funcall = Node::new(NodeKind::FunCall {
            name: func_name.to_string(),
            args,
        });
        Node::new_bin(BinOp::Comma, node, funcall)
    }

    // primary = "(" "{" stmt stmt* "}" ")"
    //         | "(" expr ")"
    //         | "sizeof" unary
    //         | ident func-args?
    //         | str
    //         | num
    fn primary(&mut self) -> Node {
        let tok = self.tok_peek.next().unwrap();
        if tok.equal("(") && next_equal(&mut self.tok_peek, "{") {
            skip(&mut self.tok_peek, "{");
            // This is a GNU statement expression.
            let body = self.compound_stmt();
            let node = Node::new_unary(UnaryOp::StmtExpr, body);
            skip(&mut self.tok_peek, ")");
            return node;
        }
        if tok.equal("(") {
            let node = Self::expr(self);
            skip(&mut self.tok_peek, ")");
            return node;
        }
        if tok.equal("sizeof") {
            let node = Self::unary(self);
            return Node::new(NodeKind::Num(node.get_type_ref().borrow().size));
        }
        match &tok.kind {
            TokenKind::Ident(name) => {
                // Function call
                if next_equal(&mut self.tok_peek, "(") {
                    return Self::funcall(self, name.to_string());
                }

                // variable
                let var = if let Some(x) = self.find_var(&name) {
                    x
                } else {
                    error_tok(tok, "undefined variable");
                    // FIXME 綺麗にする
                    self.locals[0].clone()
                };
                Node::new_var_node(var)
            }
            TokenKind::Str(words) => {
                let name = self.new_unique_name();
                let gvar = Var::new_string_literal(name, words.clone());
                let gvar = Rc::new(gvar);
                let rgvar = gvar.clone();
                self.var_scope.push_front(gvar.clone());
                self.globals.push_front(gvar);
                Node::new_var_node(rgvar)
            }
            _ => {
                // TODO ここの処理をもう少し綺麗にする
                let x = if let Some(x) = tok.get_number() {
                    x
                } else {
                    let msg = format!("token number parse error: {:?}", tok);
                    unimplemented!("{}", msg);
                };
                Node::new(NodeKind::Num(x))
            }
        }
    }
}
