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

use crate::tokenize::{consume, next_equal, skip, Token, TokenKind};
use crate::types::{FuncParam, Type, TypeKind};
use crate::util::{align_to, error, error_tok};
use std::cell::Cell;
use std::collections::VecDeque;
use std::slice::Iter;
use std::{iter::Peekable, rc::Rc, unimplemented};
//
// Parser
//
#[derive(Debug)]
pub enum UnaryOp {
    ExprStmt,
    Return,
    Addr,
    Deref,
}

#[derive(Debug)]
pub enum BinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Equal,  // ==
    NEqual, // !=
    Lt,     // <
    Le,     // <=
    Assign, // = variable assign
}

#[derive(Debug)]
pub enum NodeKind {
    Num(i64), // Integer
    Unary(UnaryOp, Box<Node>),
    Bin {
        op: BinOp,
        lhs: Box<Node>, // Left-hand side
        rhs: Box<Node>, // Right-hand side
    },
    Var {
        var: Rc<Var>,
    },
    // if statement
    If {
        cond: Box<Node>,
        then: Box<Node>,
        els: Box<Option<Node>>,
    },
    // for statement
    For {
        cond: Box<Option<Node>>,
        then: Box<Node>,
        init: Box<Node>,
        inc: Box<Option<Node>>,
    },
    // while statement
    While {
        cond: Box<Node>,
        then: Box<Node>,
    },
    Block(Vec<Node>), // { ... }
    FunCall {
        name: String,
        args: Vec<Node>,
    }, // Function call
}

// Variable
#[derive(Clone, Debug)]
pub struct Var {
    pub name: String,
    pub offset: Cell<usize>,
    pub ty: Type,
}

impl Var {
    fn new_lvar(name: String, offset: usize, ty: Type) -> Var {
        Var {
            name,
            offset: Cell::new(offset),
            ty,
        }
    }
}

// AST node type
#[derive(Debug)]
pub struct Node {
    pub kind: NodeKind, // Node kind
}

impl Node {
    pub fn new(kind: NodeKind) -> Self {
        Self { kind }
    }

    pub fn get_type(&self) -> Type {
        match &self.kind {
            NodeKind::Unary(op, child) => match op {
                UnaryOp::Addr => match child.get_type().kind.as_ref() {
                    TypeKind::Arr { base, length: _ } => Type::pointer_to(base.clone()),
                    _ => Type::pointer_to(Rc::new(child.get_type())),
                },
                UnaryOp::Deref => match child.get_type().kind.as_ref() {
                    TypeKind::Arr { base, .. } => (*base.as_ref()).clone(),
                    _ => child.get_type(),
                },
                _ => unreachable!(),
            },
            NodeKind::Bin { op: binop, lhs, .. } => match binop {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Assign => lhs.get_type(),
                BinOp::Equal | BinOp::NEqual | BinOp::Lt | BinOp::Le => Type::new_int(),
            },
            NodeKind::Var { var } => var.ty.clone(),
            NodeKind::Num(_) | NodeKind::FunCall { .. } => Type::new_int(),
            _ => unreachable!(),
        }
    }

    pub fn new_unary(op: UnaryOp, node: Self) -> Self {
        let kind = NodeKind::Unary(op, Box::new(node));
        Self::new(kind)
    }

    pub fn new_bin(op: BinOp, lhs: Self, rhs: Self) -> Self {
        let kind = NodeKind::Bin {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
        Self::new(kind)
    }

    pub fn new_add(lhs: Self, rhs: Self) -> Self {
        match (lhs.get_type().is_ptr(), rhs.get_type().is_ptr()) {
            // pointer + num
            (true, false) => {
                let lhs_size = match lhs.get_type().kind.as_ref() {
                    TypeKind::Ptr(base) | TypeKind::Arr { base, .. } => base.size,
                    _ => unimplemented!("undefined internal type on ptr add"),
                };
                Self::new_bin(
                    BinOp::Add,
                    lhs,
                    Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(lhs_size as i64)), rhs),
                )
            }
            // num + pointer
            (false, true) => Self::new_add(rhs, lhs),
            // num + num
            (false, false) => Self::new_bin(BinOp::Add, lhs, rhs),
            // pointer + pointer
            (true, true) => unimplemented!(),
        }
    }

    pub fn new_sub(lhs: Self, rhs: Self) -> Self {
        match (lhs.get_type().is_ptr(), rhs.get_type().is_ptr()) {
            // pointer - num
            (true, false) => {
                let lhs_size = match lhs.get_type().kind.as_ref() {
                    TypeKind::Ptr(base) | TypeKind::Arr { base, .. } => base.size,
                    _ => unimplemented!("undefined internal type on ptr sub"),
                };
                Self::new_bin(
                    BinOp::Sub,
                    lhs,
                    Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(lhs_size as i64)), rhs),
                )
            }
            // pointer - pointer, which returns how many elements are between the two.
            (true, true) => Node::new_bin(
                BinOp::Div,
                Node::new_bin(BinOp::Sub, lhs, rhs),
                Node::new(NodeKind::Num(8)),
            ),
            // num - num
            (false, false) => Self::new_bin(BinOp::Sub, lhs, rhs),
            // num - pointer
            (false, true) => unimplemented!(),
        }
    }

    pub fn new_if(cond: Self, then: Self, els: Option<Self>) -> Self {
        let kind = NodeKind::If {
            cond: Box::new(cond),
            then: Box::new(then),
            els: Box::new(els),
        };
        Self::new(kind)
    }

    pub fn new_for(cond: Option<Self>, then: Self, init: Self, inc: Option<Self>) -> Self {
        let kind = NodeKind::For {
            cond: Box::new(cond),
            then: Box::new(then),
            init: Box::new(init),
            inc: Box::new(inc),
        };
        Self::new(kind)
    }

    pub fn new_while(cond: Self, then: Self) -> Self {
        let kind = NodeKind::While {
            cond: Box::new(cond),
            then: Box::new(then),
        };
        Self::new(kind)
    }

    pub fn new_var_node(var: Rc<Var>) -> Self {
        let kind = NodeKind::Var { var };
        Self::new(kind)
    }

    pub fn new_block_node(nodes: Vec<Self>) -> Self {
        let kind = NodeKind::Block(nodes);
        Self::new(kind)
    }
}

pub struct Function {
    pub name: String,
    pub params: VecDeque<Rc<Var>>,
    pub body: Node,
    #[allow(dead_code)]
    locals: VecDeque<Rc<Var>>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(name: String, params: VecDeque<Rc<Var>>, body: Node, locals: VecDeque<Rc<Var>>) -> Self {
        let mut offset = 32;
        for local in locals.iter() {
            offset += local.ty.size;
            local.offset.set(offset);
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

pub struct Parser<'a> {
    tok_peek: Peekable<Iter<'a, Token>>,
    locals: VecDeque<Rc<Var>>,
}

impl<'a> Parser<'a> {
    fn new(tok_peek: Peekable<Iter<'a, Token>>, locals: VecDeque<Rc<Var>>) -> Self {
        Self { tok_peek, locals }
    }

    // program = stmt*
    pub fn parse(tok_peek: Peekable<Iter<Token>>) -> Vec<Function> {
        // All local variable instances created during parsing are
        // accumulated to this list.
        let mut parser = Parser::new(tok_peek, VecDeque::new());
        let mut funcs = Vec::new();
        while let Some(_) = parser.tok_peek.peek() {
            let func = parser.funcdef();
            funcs.push(func);
        }
        funcs
    }

    // funcdef = typespec declarator compound-stmt
    pub fn funcdef(&mut self) -> Function {
        let ty = self.typespec();
        let (ty, func_name) = self.declarator(ty);

        let mut var_params = VecDeque::new();
        if let TypeKind::Func {
            return_ty: _,
            params,
        } = ty.kind.as_ref()
        {
            for (ty, var_name) in params.iter() {
                // offsetは関数内の全変数が出揃わないとoffsetを用意できないため
                // 一旦無効な値0を入れる
                let var = Var::new_lvar(var_name.clone(), 0, ty.clone());
                let var = Rc::new(var);
                var_params.push_front(var.clone());
                self.locals.push_front(var.clone());
            }
        }

        skip(&mut self.tok_peek, "{");
        let body = self.compound_stmt();

        Function::new(func_name, var_params, body, self.locals.clone())
    }

    // typespec = "int"
    pub fn typespec(&mut self) -> Type {
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
    pub fn declarator(&mut self, mut ty: Type) -> FuncParam {
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
            let var = Var::new_lvar(name, 0, ty.clone());
            let var = Rc::new(var);
            self.locals.push_front(var.clone());

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
            return Self::compound_stmt(self);
        }
        Self::expr_stmt(self)
    }

    // compound-stmt = (declaration | stmt)* "}"
    fn compound_stmt(&mut self) -> Node {
        let mut nodes = vec![];

        while !next_equal(&mut self.tok_peek, "}") {
            let node = if next_equal(&mut self.tok_peek, "int") {
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

    // postfix = primary ("[" expr "]")
    fn postfix(&mut self) -> Node {
        let mut node = self.primary();

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

    // primary = "(" expr ")" | "sizeof" unary | ident func-args? | num
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
                let var = if let Some(x) = self.locals.iter().find(|x| x.name == *name) {
                    x.clone()
                } else {
                    error_tok(tok, "undefined variable");
                    // FIXME 綺麗にする
                    self.locals[0].clone()
                };
                Node::new_var_node(var)
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
