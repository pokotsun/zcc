use crate::tokenize::{skip, Token, TokenKind};
use std::iter::Peekable;
use std::slice::Iter;
//
// Parser
//
pub enum UnaryOp {
    ExprStmt,
    Return,
}

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

pub enum NodeKind {
    Num(i64), // Integer
    Unary(UnaryOp, Box<Node>),
    Bin {
        op: BinOp,
        lhs: Box<Node>, // Left-hand side
        rhs: Box<Node>, // Right-hand side
    },
    Var {
        name: String,
    },
}

// AST node type
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

    pub fn new_var_node(name: String) -> Self {
        let kind = NodeKind::Var { name };
        Node::new(kind)
    }

    // stmt = "return" expr ";"
    //      | expr-stmt
    fn stmt(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("return") {
            tok_peek.next();
            let node = Node::new_unary(UnaryOp::Return, Node::expr(tok_peek));
            skip(tok_peek, ";");
            return node;
        }
        Node::expr_stmt(tok_peek)
    }

    // expr-stmt = expr ";"
    fn expr_stmt(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let node = Node::new_unary(UnaryOp::ExprStmt, Node::expr(tok_peek));
        skip(tok_peek, ";");
        return node;
    }

    // expr = assign
    fn expr(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        Node::assign(tok_peek)
    }

    // assign = equality ("=" assign)?
    fn assign(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::equality(tok_peek);
        let tok = tok_peek.peek().unwrap();
        if tok.equal("=") {
            tok_peek.next();
            node = Node::new_bin(BinOp::Assign, node, Node::assign(tok_peek));
        }
        node
    }

    // equality = relational ("==" relational | "!=" relational)
    fn equality(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::relational(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("==") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek);
                node = Node::new_bin(BinOp::Equal, node, rhs);
                continue;
            }
            if tok.equal("!=") {
                tok_peek.next();
                let rhs = Node::relational(tok_peek);
                node = Node::new_bin(BinOp::NEqual, node, rhs);
                continue;
            }
            return node;
        }
    }

    // relational = add ("<" add | "<=" add | ">" add | ">=" add)*
    fn relational(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::add(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("<") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Lt, node, rhs);
                continue;
            }

            if tok.equal("<=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Le, node, rhs);
                continue;
            }
            if tok.equal(">") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Lt, rhs, node);
                continue;
            }
            if tok.equal(">=") {
                tok_peek.next();
                let rhs = Node::add(tok_peek);
                node = Node::new_bin(BinOp::Le, rhs, node);
                continue;
            }
            return node;
        }
    }

    // add = mul ("+" mul | "-" mul)*
    fn add(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::mul(tok_peek);
        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("+") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek);
                node = Node::new_bin(BinOp::Add, node, rhs);
                continue;
            }
            if tok.equal("-") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek);
                node = Node::new_bin(BinOp::Sub, node, rhs);
                continue;
            }
            return node;
        }
    }

    // mul = unary ("*" unary | "/" unary)*
    fn mul(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let mut node = Node::unary(tok_peek);

        loop {
            let tok = tok_peek.peek().unwrap();
            if tok.equal("*") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek);
                node = Node::new_bin(BinOp::Mul, node, rhs);
                continue;
            }
            if tok.equal("/") {
                tok_peek.next();
                let rhs = Node::unary(tok_peek);
                node = Node::new_bin(BinOp::Div, node, rhs);
                continue;
            }
            return node;
        }
    }

    // unary = ("+" | "-") unary
    //       | primary
    fn unary(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("+") {
            tok_peek.next();
            return Node::unary(tok_peek);
        }

        if tok.equal("-") {
            tok_peek.next();
            return Node::new_bin(
                BinOp::Sub,
                Node::new(NodeKind::Num(0)),
                Node::unary(tok_peek),
            );
        }

        return Node::primary(tok_peek);
    }

    // primary = "(" expr ")" | ident | num
    fn primary(tok_peek: &mut Peekable<Iter<Token>>) -> Node {
        let tok = tok_peek.next().unwrap();
        if tok.equal("(") {
            let node = Node::expr(tok_peek);
            skip(tok_peek, ")");
            return node;
        }
        // let node = Node::new(NodeKind::Num(tok.get_number().unwrap()));
        match &tok.kind {
            TokenKind::Ident(name) => Node::new_var_node(name.to_string()),
            _ => Node::new(NodeKind::Num(tok.get_number().unwrap())),
        }
    }

    // program = stmt*
    pub fn parse(tok_peek: &mut Peekable<Iter<Token>>) -> Vec<Node> {
        let mut nodes = Vec::new();
        while let Some(tok) = tok_peek.peek() {
            if !matches!(tok.kind, TokenKind::Eof) {
                let node = Node::stmt(tok_peek);
                nodes.push(node);
            } else {
                // eofをskip
                skip(tok_peek, "EOF");
            }
        }
        nodes
    }
}
