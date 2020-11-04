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
use crate::tokenize::{skip, Token, TokenKind};
use crate::types::Type;
use crate::util::{align_to, error};
use std::iter::Peekable;
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
    Var(Var),
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
}

// Local Variable
#[derive(Clone, Debug)]
pub struct Var {
    pub name: String,
    pub offset: usize,
}

impl Var {
    fn new_lvar(name: String, offset: usize) -> Var {
        Var { name, offset }
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
            NodeKind::Var(_) | NodeKind::Num(_) => Type::new_int(),
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
            (true, false) => Self::new_bin(
                BinOp::Sub,
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
            (true, false) => Self::new_bin(
                BinOp::Add,
                lhs,
                Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(8)), rhs),
            ),
            // pointer - pointer, which returns how many elements are between the two.
            // 変数スタックはマイナス方向に伸びるため(ex. int x, y -> &x=-8, &y=-16),
            // &x-&yしてやると差分のポインタが得られる
            (true, true) => Self::new_bin(
                BinOp::Div,
                Self::new_bin(BinOp::Sub, rhs, lhs),
                Self::new(NodeKind::Num(8)),
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

    pub fn new_var_node(var: Var) -> Self {
        let kind = NodeKind::Var(var);
        Self::new(kind)
    }

    pub fn new_block_node(nodes: Vec<Self>) -> Self {
        let kind = NodeKind::Block(nodes);
        Self::new(kind)
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        // FIXME Multiple Borrowを避けるためにcloneしているが如何なものか
        let tok = tok_peek.peek().unwrap().clone();
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
            let then = Self::stmt(tok_peek, locals);
            let next_tok = tok_peek.peek().map(|x| (*x).clone()); // 実体のコピー
            let els = next_tok.filter(|tok| tok.equal("else")).map(|_| {
                tok_peek.next();
                Self::stmt(tok_peek, locals)
            });
            return Self::new_if(cond, then, els);
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

    // compound-stmt = stmt* "}"
    fn compound_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut nodes = vec![];

        while tok_peek.peek().filter(|tok| !tok.equal("}")).is_some() {
            let node = Self::stmt(tok_peek, locals);
            nodes.push(node);
        }

        skip(tok_peek, "}");
        Self::new_block_node(nodes)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        // FIXME Nullのため, OptionかNoneという処理を入れたほうが良い?
        if let Some(true) = tok_peek.peek().and_then(|tok| Some(tok.equal(";"))) {
            tok_peek.next();
            return Self::new_block_node(vec![]);
        }

        let node = Self::new_unary(UnaryOp::ExprStmt, Self::expr(tok_peek, locals));
        skip(tok_peek, ";");
        return node;
    }

    // expr = assign
    fn expr(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        Self::assign(tok_peek, locals)
    }

    // assign = equality ("=" assign)?
    fn assign(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut node = Self::equality(tok_peek, locals);
        let tok = tok_peek.peek().unwrap();
        if tok.equal("=") {
            tok_peek.next();
            node = Self::new_bin(BinOp::Assign, node, Self::assign(tok_peek, locals));
        }
        node
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut node = Self::relational(tok_peek, locals);

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
    fn relational(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut node = Self::add(tok_peek, locals);

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
    fn add(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut node = Self::mul(tok_peek, locals);
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
    fn mul(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let mut node = Self::unary(tok_peek, locals);

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
    fn unary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
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

    // primary = "(" expr ")" | ident | num
    fn primary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Self {
        let tok = tok_peek.next().unwrap();
        if tok.equal("(") {
            let node = Self::expr(tok_peek, locals);
            skip(tok_peek, ")");
            return node;
        }
        match &tok.kind {
            TokenKind::Ident(name) => {
                let var = if let Some(x) = locals.iter().find(|x| x.name == *name) {
                    x.clone()
                } else {
                    let x = Var::new_lvar(name.clone(), 32 + (locals.len() + 1) * 8);
                    locals.push(x.clone());
                    x
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
    locals: Vec<Var>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(body: Node, locals: Vec<Var>) -> Self {
        let offset = 32 + 8 * (locals.len());
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
        let mut locals = Vec::new();
        skip(tok_peek, "{");
        let node = Node::compound_stmt(tok_peek, &mut locals);
        Function::new(node, locals)
    }
}
