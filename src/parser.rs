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
    PtrAdd, // pointer Add
    PtrSub, // pointer Sub
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

    pub fn new_unary(op: UnaryOp, node: Node) -> Self {
        let kind = NodeKind::Unary(op, Box::new(node));
        Node::new(kind)
    }

    pub fn new_bin(op: BinOp, lhs: Node, rhs: Node) -> Self {
        let kind = NodeKind::Bin {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
        Node::new(kind)
    }

    pub fn new_if(cond: Node, then: Node, els: Option<Node>) -> Self {
        let kind = NodeKind::If {
            cond: Box::new(cond),
            then: Box::new(then),
            els: Box::new(els),
        };
        Node::new(kind)
    }

    pub fn new_for(cond: Option<Node>, then: Node, init: Node, inc: Option<Node>) -> Self {
        let kind = NodeKind::For {
            cond: Box::new(cond),
            then: Box::new(then),
            init: Box::new(init),
            inc: Box::new(inc),
        };
        Node::new(kind)
    }

    pub fn new_while(cond: Node, then: Node) -> Self {
        let kind = NodeKind::While {
            cond: Box::new(cond),
            then: Box::new(then),
        };
        Node::new(kind)
    }

    pub fn new_var_node(var: Var) -> Self {
        let kind = NodeKind::Var(var);
        Node::new(kind)
    }

    pub fn new_block_node(nodes: Vec<Node>) -> Self {
        let kind = NodeKind::Block(nodes);
        Node::new(kind)
    }

    // stmt = "return" expr ";"
    //      | "if" "(" expr ")" stmt ("else" stmt)?
    //      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
    //      | "while" "(" expr ")" stmt
    //      | "{" compound-stmt
    //      | expr-stmt
    fn stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        // FIXME Multiple Borrowを避けるためにcloneしているが如何なものか
        let tok = tok_peek.peek().unwrap().clone();
        if tok.equal("return") {
            tok_peek.next();
            let node = Node::new_unary(UnaryOp::Return, Node::expr(tok_peek, locals));
            skip(tok_peek, ";");
            return node;
        }

        if tok.equal("if") {
            tok_peek.next();
            skip(tok_peek, "(");
            let cond = Node::expr(tok_peek, locals);
            skip(tok_peek, ")");
            let then = Node::stmt(tok_peek, locals);
            let next_tok = tok_peek.peek().map(|x| (*x).clone()); // 実体のコピー
            let els = next_tok.filter(|tok| tok.equal("else")).map(|_| {
                tok_peek.next();
                Node::stmt(tok_peek, locals)
            });
            return Node::new_if(cond, then, els);
        }

        if tok.equal("for") {
            tok_peek.next();
            skip(tok_peek, "(");

            let init = Node::expr_stmt(tok_peek, locals);

            let next_tok = tok_peek.peek().map(|x| (*x).clone());
            let cond = next_tok
                .filter(|tok| !tok.equal(";"))
                .map(|_| Node::expr(tok_peek, locals));
            skip(tok_peek, ";");

            let next_tok = tok_peek.peek().map(|x| (*x).clone());
            let inc = next_tok
                .filter(|tok| !tok.equal(")"))
                .map(|_| Node::expr(tok_peek, locals));
            skip(tok_peek, ")");

            let then = Node::stmt(tok_peek, locals);
            return Node::new_for(cond, then, init, inc);
        }

        if tok.equal("while") {
            tok_peek.next();
            skip(tok_peek, "(");
            let cond = Node::expr(tok_peek, locals);
            skip(tok_peek, ")");
            let then = Node::stmt(tok_peek, locals);
            return Node::new_while(cond, then);
        }

        if tok.equal("{") {
            tok_peek.next();
            return Node::compound_stmt(tok_peek, locals);
        }
        Node::expr_stmt(tok_peek, locals)
    }

    // compound-stmt = stmt* "}"
    fn compound_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut nodes = vec![];

        while tok_peek.peek().filter(|tok| !tok.equal("}")).is_some() {
            let node = Node::stmt(tok_peek, locals);
            nodes.push(node);
        }

        skip(tok_peek, "}");
        Node::new_block_node(nodes)
    }

    // expr-stmt = expr? ";"
    fn expr_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        // FIXME Nullのため, OptionかNoneという処理を入れたほうが良い?
        if let Some(true) = tok_peek.peek().and_then(|tok| Some(tok.equal(";"))) {
            tok_peek.next();
            return Node::new_block_node(vec![]);
        }

        let node = Node::new_unary(UnaryOp::ExprStmt, Node::expr(tok_peek, locals));
        skip(tok_peek, ";");
        return node;
    }

    // expr = assign
    fn expr(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        Node::assign(tok_peek, locals)
    }

    // assign = equality ("=" assign)?
    fn assign(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut node = Node::equality(tok_peek, locals);
        let tok = tok_peek.peek().unwrap();
        if tok.equal("=") {
            tok_peek.next();
            node = Node::new_bin(BinOp::Assign, node, Node::assign(tok_peek, locals));
        }
        node
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut node = Node::relational(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("==") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek, locals);
                node = Node::new_bin(BinOp::Equal, node, rhs);
                continue;
            }
            if tok.equal("!=") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek, locals);
                node = Node::new_bin(BinOp::NEqual, node, rhs);
                continue;
            }
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut node = Node::add(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("<") {
                tok_peek.next();
                let rhs = Node::add(tok_peek, locals);
                node = Node::new_bin(BinOp::Lt, node, rhs);
                continue;
            }

            if tok.equal("<=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek, locals);
                node = Node::new_bin(BinOp::Le, node, rhs);
                continue;
            }
            if tok.equal(">") {
                tok_peek.next();
                let rhs = Node::add(tok_peek, locals);
                node = Node::new_bin(BinOp::Lt, rhs, node);
                continue;
            }
            if tok.equal(">=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek, locals);
                node = Node::new_bin(BinOp::Le, rhs, node);
                continue;
            }
            return node;
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut node = Node::mul(tok_peek, locals);
        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("+") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek, locals);
                node = if matches!(rhs.kind, NodeKind::Unary(UnaryOp::Addr, _))
                    || matches!(node.kind, NodeKind::Unary(UnaryOp::Addr, _))
                {
                    Node::new_bin(BinOp::PtrAdd, node, rhs)
                } else {
                    Node::new_bin(BinOp::Add, node, rhs)
                };
                continue;
            }
            if tok.equal("-") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek, locals);
                node = if matches!(rhs.kind, NodeKind::Unary(UnaryOp::Addr, _))
                    || matches!(node.kind, NodeKind::Unary(UnaryOp::Addr, _))
                {
                    Node::new_bin(BinOp::PtrSub, node, rhs)
                } else {
                    Node::new_bin(BinOp::Sub, node, rhs)
                };
                continue;
            }
            return node;
        }
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let mut node = Node::unary(tok_peek, locals);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("*") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek, locals);
                node = Node::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek, locals);
                node = Node::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // unary = ("+" | "-" | "*" | "&") unary
    //       | primary
    fn unary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("+") {
            tok_peek.next();
            return Node::unary(tok_peek, locals);
        }
        if tok.equal("-") {
            tok_peek.next();
            return Node::new_bin(
                BinOp::Sub,
                Node::new(NodeKind::Num(0)),
                Node::unary(tok_peek, locals),
            );
        }
        if tok.equal("&") {
            tok_peek.next();
            return Node::new_unary(UnaryOp::Addr, Node::unary(tok_peek, locals));
        }

        if tok.equal("*") {
            tok_peek.next();
            return Node::new_unary(UnaryOp::Deref, Node::unary(tok_peek, locals));
        }

        return Node::primary(tok_peek, locals);
    }

    // primary = "(" expr ")" | ident | num
    fn primary(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let tok = tok_peek.next().unwrap();
        if tok.equal("(") {
            let node = Node::expr(tok_peek, locals);
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

                Node::new_var_node(var)
            }
            _ => {
                // TODO ここの処理をもう少し綺麗にする
                let x = if let Some(x) = tok.get_number() {
                    x
                } else {
                    error(&format!("token number parse error: {:?}", tok));
                    0
                };
                Node::new(NodeKind::Num(x))
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
