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
use crate::types::Type;
use crate::util::{align_to, error, error_tok};
use std::cell::Cell;
use std::collections::VecDeque;
use std::iter::Peekable;
use std::rc::Rc;
use std::slice::Iter;
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

// Local Variable
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
                UnaryOp::Addr => Type::pointer_to(child.get_type()),
                UnaryOp::Deref => child.get_type(),
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
            (true, false) => Node::new_bin(
                BinOp::Add,
                lhs,
                Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(8)), rhs),
            ),
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
            (true, false) => Node::new_bin(
                BinOp::Sub,
                lhs,
                Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(8)), rhs),
            ),
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

    // typespec = "int"
    pub fn typespec(tok_peek: &mut Peekable<Iter<Token>>) -> Type {
        skip(tok_peek, "int");
        Type::new_int()
    }

    // declarator = "*"* ident
    pub fn declarator(tok_peek: &mut Peekable<Iter<Token>>, mut ty: Type) -> Type {
        // FIXME なんか凄く汚い
        while consume(tok_peek, "*") {
            ty = Type::pointer_to(ty);
        }
        let tok = tok_peek.next().unwrap();
        if !matches!(tok.kind, TokenKind::Ident(_)) {
            error_tok(tok, "invalid pointer dereference");
        }
        ty.name.replace(tok.word.clone());
        ty
    }

    // declaration = typespec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
    fn declaration(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Self {
        // TODO ここも Self::typespecである必要ないのでは?
        let basety = Self::typespec(tok_peek);

        let mut is_already_declared = false;
        let mut nodes = Vec::new();
        while !next_equal(tok_peek, ";") {
            if is_already_declared {
                skip(tok_peek, ",");
            }
            is_already_declared = true;

            let ty = Self::declarator(tok_peek, basety.clone());
            // offsetは関数内の全変数が出揃わないとoffsetを用意できないため
            // 一旦無効な値0を入れる
            let var = Var::new_lvar(ty.name.borrow().clone(), 0, ty.clone());
            let var = Rc::new(var);
            let rcvar = var.clone();
            locals.push_front(var);

            if !next_equal(tok_peek, "=") {
                continue;
            }
            let lhs = Self::new_var_node(rcvar);

            tok_peek.next(); // "=" tokenを飛ばす
            let rhs = Self::assign(tok_peek, locals);
            let node = Self::new_bin(BinOp::Assign, lhs, rhs);
            let node = Self::new_unary(UnaryOp::ExprStmt, node);
            nodes.push(node);
        }
        let node = Self::new_block_node(nodes);
        node
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("return") {
            tok_peek.next();
            let node = Self::new_unary(UnaryOp::Return, Self::expr(tok_peek, locals));
            skip(tok_peek, ";");
            return node;
        }

        if tok.equal("if") {
            tok_peek.next();
            skip(tok_peek, "(");
            let cond = Self::expr(tok_peek, locals);
            skip(tok_peek, ")");
            let then = Node::stmt(tok_peek, locals);

            let els = tok_peek
                .peek()
                .and_then(|next_tok| Some(next_tok.clone()))
                .filter(|next_tok| next_tok.equal("else"))
                .map(|_| {
                    tok_peek.next();
                    Node::stmt(tok_peek, locals)
                });
            return Node::new_if(cond, then, els);
        }

        if tok.equal("for") {
            tok_peek.next();
            skip(tok_peek, "(");

            let init = Self::expr_stmt(tok_peek, locals);

            let next_tok = tok_peek.peek().map(|x| (*x).clone());
            let cond = next_tok
                .filter(|tok| !tok.equal(";"))
                .map(|_| Self::expr(tok_peek, locals));
            skip(tok_peek, ";");

            let next_tok = tok_peek.peek().map(|x| (*x).clone());
            let inc = next_tok
                .filter(|tok| !tok.equal(")"))
                .map(|_| Self::expr(tok_peek, locals));
            skip(tok_peek, ")");

            let then = Self::stmt(tok_peek, locals);
            return Self::new_for(cond, then, init, inc);
        }

        if tok.equal("while") {
            tok_peek.next();
            skip(tok_peek, "(");
            let cond = Self::expr(tok_peek, locals);
            skip(tok_peek, ")");
            let then = Self::stmt(tok_peek, locals);
            return Self::new_while(cond, then);
        }

        if tok.equal("{") {
            tok_peek.next();
            return Self::compound_stmt(tok_peek, locals);
        }
        Self::expr_stmt(tok_peek, locals)
    }

    // compound-stmt = (declaration | stmt)* "}"
    fn compound_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut nodes = vec![];

        while !next_equal(tok_peek, "}") {
            let node = if next_equal(tok_peek, "int") {
                Self::declaration(tok_peek, locals)
            } else {
                Self::stmt(tok_peek, locals)
            };
            nodes.push(node);
        }

        skip(tok_peek, "}");
        Self::new_block_node(nodes)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        // FIXME Nullのため, OptionかNoneという処理を入れたほうが良い?
        if next_equal(tok_peek, ";") {
            tok_peek.next();
            return Self::new_block_node(vec![]);
        }

        let node = Self::new_unary(UnaryOp::ExprStmt, Self::expr(tok_peek, locals));
        skip(tok_peek, ";");
        return node;
    }

    // expr = assign
    fn expr(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        Node::assign(tok_peek, locals)
    }

    // assign = equality ("=" assign)?
    fn assign(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut node = Node::equality(tok_peek, locals);
        let tok = tok_peek.peek().unwrap();
        if tok.equal("=") {
            tok_peek.next();
            node = Self::new_bin(BinOp::Assign, node, Self::assign(tok_peek, locals));
        }
        node
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut node = Node::relational(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("==") {
                tok_peek.next();
                let rhs = Self::relational(tok_peek, locals);
                node = Self::new_bin(BinOp::Equal, node, rhs);
                continue;
            }
            if tok.equal("!=") {
                tok_peek.next();
                let rhs = Self::relational(tok_peek, locals);
                node = Self::new_bin(BinOp::NEqual, node, rhs);
                continue;
            }
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut node = Node::add(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("<") {
                tok_peek.next();
                let rhs = Self::add(tok_peek, locals);
                node = Self::new_bin(BinOp::Lt, node, rhs);
                continue;
            }

            if tok.equal("<=") {
                tok_peek.next();
                let rhs = Self::add(tok_peek, locals);
                node = Self::new_bin(BinOp::Le, node, rhs);
                continue;
            }
            if tok.equal(">") {
                tok_peek.next();
                let rhs = Self::add(tok_peek, locals);
                node = Self::new_bin(BinOp::Lt, rhs, node);
                continue;
            }
            if tok.equal(">=") {
                tok_peek.next();
                let rhs = Self::add(tok_peek, locals);
                node = Self::new_bin(BinOp::Le, rhs, node);
                continue;
            }
            return node;
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut node = Node::mul(tok_peek, locals);
        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("+") {
                tok_peek.next();
                let rhs = Self::mul(tok_peek, locals);
                node = Self::new_add(node, rhs);
                continue;
            }
            if tok.equal("-") {
                tok_peek.next();
                let rhs = Self::mul(tok_peek, locals);
                node = Self::new_sub(node, rhs);
                continue;
            }
            return node;
        }
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let mut node = Node::unary(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("*") {
                tok_peek.next();
                let rhs = Self::unary(tok_peek, locals);
                node = Self::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                tok_peek.next();
                let rhs = Self::unary(tok_peek, locals);
                node = Self::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // unary = ("+" | "-" | "*" | "&") unary
    //       | primary
    fn unary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("+") {
            tok_peek.next();
            return Self::unary(tok_peek, locals);
        }
        if tok.equal("-") {
            tok_peek.next();
            return Self::new_bin(
                BinOp::Sub,
                Self::new(NodeKind::Num(0)),
                Self::unary(tok_peek, locals),
            );
        }
        if tok.equal("&") {
            tok_peek.next();
            return Self::new_unary(UnaryOp::Addr, Self::unary(tok_peek, locals));
        }

        if tok.equal("*") {
            tok_peek.next();
            return Self::new_unary(UnaryOp::Deref, Self::unary(tok_peek, locals));
        }

        return Self::primary(tok_peek, locals);
    }

    // funcall = ident "(" (assign (",", assign)*)? ")"
    fn funcall(
        func_name: String,
        tok_peek: &mut Peekable<Iter<Token>>,
        locals: &mut VecDeque<Rc<Var>>,
    ) -> Self {
        skip(tok_peek, "(");

        let mut args = Vec::new();
        while !next_equal(tok_peek, ")") {
            if args.len() > 0 {
                skip(tok_peek, ",");
            }
            let arg = Node::assign(tok_peek, locals);
            args.push(arg);
        }
        skip(tok_peek, ")");
        Node::new(NodeKind::FunCall {
            name: func_name.to_string(),
            args,
        })
    }

    // primary = "(" expr ")" | ident func-args? | num
    fn primary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut VecDeque<Rc<Var>>) -> Node {
        let tok = tok_peek.next().unwrap();
        if tok.equal("(") {
            let node = Self::expr(tok_peek, locals);
            skip(tok_peek, ")");
            return node;
        }
        match &tok.kind {
            TokenKind::Ident(name) => {
                // Function call
                if next_equal(tok_peek, "(") {
                    return Node::funcall(name.to_string(), tok_peek, locals);
                }

                // variable
                let var = if let Some(x) = locals.iter().find(|x| x.name == *name) {
                    x.clone()
                } else {
                    error_tok(tok, "undefined variable");
                    // FIXME 綺麗にする
                    locals[0].clone()
                };
                Self::new_var_node(var)
            }
            _ => {
                // TODO ここの処理をもう少し綺麗にする
                let x = if let Some(x) = tok.get_number() {
                    x
                } else {
                    error(&format!("token number parse error: {:?}", tok));
                    unimplemented!()
                };
                Self::new(NodeKind::Num(x))
            }
        }
    }
}

pub struct Function {
    pub body: Node,
    #[allow(dead_code)]
    locals: VecDeque<Rc<Var>>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(body: Node, locals: VecDeque<Rc<Var>>) -> Self {
        let mut offset = 32;
        for local in locals.iter() {
            offset += 8;
            local.offset.set(offset);
        }
        let stack_size = align_to(offset, 16);
        Self {
            body,
            locals,
            stack_size,
        }
    }

    // program = stmt*
    pub fn parse(tok_peek: &mut Peekable<Iter<Token>>) -> Self {
        // All local variable instances created during parsing are
        // accumulated to this list.
        let mut locals = VecDeque::new();
        skip(tok_peek, "{");
        let node = Node::compound_stmt(tok_peek, &mut locals);
        Function::new(node, locals)
    }
}
