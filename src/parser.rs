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
    node::{BinOp, Member, Node, NodeKind, UnaryOp, Var, VarType},
    util::LabelCounter,
};
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
            offset += local.ty.size;
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
    globals: VecDeque<Rc<Var>>,
    var_scope: VecDeque<Rc<Var>>,
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
            scope_depth: 0,
            data_idx: LabelCounter::new(),
        }
    }

    fn new_unique_name(&mut self) -> String {
        let idx = self.data_idx.next().unwrap();
        format!(".L.data.{}", idx)
    }

    fn find_var(&self, name: String) -> Option<Rc<Var>> {
        self.var_scope
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
    }

    // program = (funcdef | global-var)*
    pub fn parse(tok_peek: Peekable<Iter<Token>>) -> Program {
        // All local variable instances created during parsing are
        // accumulated to this list.
        let mut parser = Parser::new(tok_peek);
        let mut funcs = Vec::new();
        while let Some(_) = parser.tok_peek.peek() {
            let basety = parser.typespec();
            let (mut ty, mut name) = parser.declarator(basety);

            match ty.kind.as_ref() {
                TypeKind::Func { .. } => {
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
        let ty = self.typespec();
        let (ty, func_name) = self.declarator(ty);

        self.typed_funcdef(ty, func_name)
    }

    // 既に関数の返り値と関数名が得られた場合の関数の中身を取り出す
    // 主にcompoud-stmtの処理を行う
    // typed-funcdef = typespec declarator compound-stmt
    fn typed_funcdef(&mut self, ty: Type, func_name: String) -> Function {
        self.enter_scope();

        let mut var_params = VecDeque::new();
        if let TypeKind::Func {
            return_ty: _,
            params,
        } = ty.kind.as_ref()
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

    // typespec = "char" | "int" | struct-decl
    fn typespec(&mut self) -> Type {
        if next_equal(&mut self.tok_peek, "char") {
            skip(&mut self.tok_peek, "char");
            return Type::new_char();
        }
        if next_equal(&mut self.tok_peek, "int") {
            skip(&mut self.tok_peek, "int");
            return Type::new_int();
        }
        if next_equal(&mut self.tok_peek, "struct") {
            skip(&mut self.tok_peek, "struct");
            return self.struct_decl();
        }
        unimplemented!("Undefined typespec: {}", self.tok_peek.next().unwrap().word);
    }

    // func-params = (param ("," param)*)? ")"
    // param = typespec declarator
    fn func_params(&mut self, ty: Type) -> Type {
        let mut params = Vec::new();
        while !next_equal(&mut self.tok_peek, ")") {
            if params.len() > 0 {
                skip(&mut self.tok_peek, ",");
            }
            let basety = Self::typespec(self);
            let (ty, var_name) = self.declarator(basety.clone());
            params.push((ty, var_name));
        }
        skip(&mut self.tok_peek, ")");
        return Type::new_func(ty.kind, params);
    }

    // type-suffix = "(" func-params
    //             | "[" num "]"
    //             | "[" num "]" type-suffix
    //             | sigma
    fn type_suffix(&mut self, ty: Type) -> Type {
        if next_equal(&mut self.tok_peek, "(") {
            skip(&mut self.tok_peek, "(");
            return Self::func_params(self, ty);
        }
        if next_equal(&mut self.tok_peek, "[") {
            skip(&mut self.tok_peek, "[");
            if let Some(size) = self.tok_peek.next().and_then(|tok| tok.get_number()) {
                skip(&mut self.tok_peek, "]");
                let ty = self.type_suffix(ty);
                let ty = Rc::new(ty);
                return Type::array_of(ty, size as usize);
            } else {
                unimplemented!("Array length is not specified.");
            }
        }
        ty
    }

    // declarator = "*"* ident type-suffix
    fn declarator(&mut self, mut ty: Type) -> FuncParam {
        // FIXME なんか凄く汚い
        while consume(&mut self.tok_peek, "*") {
            ty = Type::pointer_to(Rc::new(ty));
        }
        let tok = self.tok_peek.next().unwrap();
        if !matches!(tok.kind, TokenKind::Ident(_)) {
            error_tok(tok, "invalid pointer dereference");
        }
        ty = Self::type_suffix(self, ty);
        (ty, tok.word.clone())
    }

    // declaration = typespec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(&mut self) -> Node {
        let basety = self.typespec();

        let mut is_already_declared = false;
        let mut nodes = Vec::new();
        while !next_equal(&mut self.tok_peek, ";") {
            if is_already_declared {
                skip(&mut self.tok_peek, ",");
            }
            is_already_declared = true;

            let (ty, name) = Self::declarator(self, basety.clone());
            // offsetは関数内の全変数が出揃わないとoffsetを用意できないため
            // 一旦無効な値0を入れる
            let var = Var::new_lvar(name, 0, ty.clone(), self.scope_depth);
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
            let basety = self.typespec();
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

    // struct-decl = "{" struct-members
    fn struct_decl(&mut self) -> Type {
        skip(&mut self.tok_peek, "{");

        // Construct a struct object.
        let members = self.struct_members();

        let mut offset: usize = 0;
        members.iter().for_each(|member| {
            member.offset.set(offset);
            offset += member.ty.size;
        });
        Type::new_struct(members, offset)
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
        if let TypeKind::Struct { members } = node.get_type().kind.as_ref().clone() {
            let member = Self::get_struct_member(members, member_name);
            return Node::new_unary(UnaryOp::Member(member), node);
        }
        unimplemented!("struct_ref is not struct:\n{:#?}", node);
    }

    // postfix = primary ("[" expr "]" | "." ident)*
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
            let mut base = arg.get_type();

            if base.is_ptr() {
                base = Type::pointer_to(Rc::new(base));
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
            return Node::new(NodeKind::Num(node.get_type().size as i64));
        }
        match &tok.kind {
            TokenKind::Ident(name) => {
                // Function call
                if next_equal(&mut self.tok_peek, "(") {
                    return Self::funcall(self, name.to_string());
                }

                // variable
                let var = if let Some(x) = self.find_var(name.clone()) {
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
