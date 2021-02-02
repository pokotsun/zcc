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

use crate::tokenize::{consume, is_typename, next_equal, skip, Token, TokenKind};
use crate::types::{FuncParam, Type, TypeKind};
use crate::util::{align_to, error, error_tok};
use crate::{
    node::{BinOp, Node, NodeKind, UnaryOp, Var},
    util::LabelCounter,
};
use std::slice::Iter;
use std::{iter::Peekable, rc::Rc, unimplemented};

pub struct Function {
    pub name: String,
    pub params: Vec<Var>,
    pub body: Node,
    #[allow(dead_code)]
    locals: Vec<Var>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(name: String, params: Vec<Var>, body: Node, locals: Vec<Var>) -> Self {
        let offset = 32 + locals.iter().fold(0, |acc, var| acc + var.ty.size);
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
    pub globals: Vec<Var>,
}

impl Program {
    fn new(fns: Vec<Function>, globals: Vec<Var>) -> Self {
        Self { fns, globals }
    }
}

pub struct Parser<'a> {
    tok_peek: Peekable<Iter<'a, Token>>,
    locals: Vec<Var>,
    globals: Vec<Var>,
    data_idx: LabelCounter,
}

impl<'a> Parser<'a> {
    fn new(tok_peek: Peekable<Iter<'a, Token>>) -> Self {
        Self {
            tok_peek,
            locals: Vec::new(),
            globals: Vec::new(),
            data_idx: LabelCounter::new(),
        }
    }

    fn new_unique_name(&mut self) -> String {
        let idx = self.data_idx.next().unwrap();
        format!(".L.data.{}", idx)
    }

    fn find_var(&self, name: String) -> Option<Var> {
        // TODO なんか汚いので修正
        if let Some(x) = self
            .locals
            .iter()
            .find(|x| x.name == name)
            .map(|var| var.clone())
        {
            Some(x)
        } else {
            self.globals
                .iter()
                .find(|x| x.name == name)
                .map(|x| x.clone())
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

            match ty.kind {
                TypeKind::Func { .. } => {
                    let func = parser.typed_funcdef(ty, name);
                    funcs.push(func);
                }
                _ => {
                    // Global variable
                    loop {
                        let var = Var::new_gvar(name, ty.clone(), Vec::new());
                        parser.globals.push(var);
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
        let mut var_params = Vec::new();
        if let TypeKind::Func {
            return_ty: _,
            params,
        } = ty.kind
        {
            for (ty, var_name) in params.iter() {
                let var =
                    Var::new_lvar(var_name.clone(), Var::calc_offset(&var_params), ty.clone());
                var_params.push(var.clone());
                self.locals.push(var.clone());
            }
        }

        skip(&mut self.tok_peek, "{");
        let body = self.compound_stmt();

        Function::new(func_name, var_params, body, self.locals.clone())
    }

    // typespec = "char" | "int"
    fn typespec(&mut self) -> Type {
        if next_equal(&mut self.tok_peek, "char") {
            skip(&mut self.tok_peek, "char");
            return Type::new_char();
        }
        skip(&mut self.tok_peek, "int");
        Type::new_int()
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
                let ty = Self::type_suffix(self, ty);
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
        // TODO ここも Self::typespecである必要ないのでは?
        let basety = Self::typespec(self);

        let mut is_already_declared = false;
        let mut nodes = Vec::new();
        while !next_equal(&mut self.tok_peek, ";") {
            if is_already_declared {
                skip(&mut self.tok_peek, ",");
            }
            is_already_declared = true;

            let (ty, name) = Self::declarator(self, basety.clone());
            let var = Var::new_lvar(name, Var::calc_offset(&self.locals), ty.clone());
            self.locals.push(var.clone());

            if !next_equal(&mut self.tok_peek, "=") {
                continue;
            }
            let lhs = Node::new_var_node(var);
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
            let next_tok = self.tok_peek.peek().map(|x| (*x).clone()); // 実体のコピー
            let els = next_tok.filter(|tok| tok.equal("else")).map(|_| {
                self.tok_peek.next();
                Self::stmt(self)
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
            return Self::compound_stmt(self);
        }
        Self::expr_stmt(self)
    }

    // compound-stmt = (declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Node {
        let mut nodes = Vec::new();

        while !next_equal(&mut self.tok_peek, "}") {
            let node = if is_typename(&mut self.tok_peek) {
                Self::declaration(self)
            } else {
                Self::stmt(self)
            };
            nodes.push(node);
        }

        skip(&mut self.tok_peek, "}");
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

    // expr = assign
    fn expr(&mut self) -> Node {
        Self::assign(self)
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
        let mut node = Self::mul(self);
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
        let mut node = Self::unary(self);

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

    // postfix = primary ("[" expr "]")
    fn postfix(&mut self) -> Node {
        let mut node = Self::primary(self);

        while next_equal(&mut self.tok_peek, "[") {
            skip(&mut self.tok_peek, "[");
            // x[idx] is *(x + idx)
            let idx = Self::expr(self);
            skip(&mut self.tok_peek, "]");
            node = Node::new_unary(UnaryOp::Deref, Node::new_add(node, idx));
        }
        node
    }

    // funcall = ident "(" (assign (",", assign)*)? ")"
    fn funcall(&mut self, func_name: String) -> Node {
        skip(&mut self.tok_peek, "(");

        let mut args = Vec::new();
        while !next_equal(&mut self.tok_peek, ")") {
            if args.len() > 0 {
                skip(&mut self.tok_peek, ",");
            }
            let arg = Self::assign(self);
            args.push(arg);
        }
        skip(&mut self.tok_peek, ")");
        Node::new(NodeKind::FunCall {
            name: func_name.to_string(),
            args,
        })
    }

    // primary = "(" expr ")" | "sizeof" unary | ident func-args? | str | num
    fn primary(&mut self) -> Node {
        let tok = self.tok_peek.next().unwrap();
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
                self.globals.push(gvar.clone());
                Node::new_var_node(gvar)
            }
            _ => {
                // TODO ここの処理をもう少し綺麗にする
                let x = if let Some(x) = tok.get_number() {
                    x
                } else {
                    error(&format!("token number parse error: {:?}", tok));
                    unimplemented!()
                };
                Node::new(NodeKind::Num(x))
            }
        }
    }
}
