use crate::tokenize::{skip, Token, TokenKind};
use crate::util::align_to;
use std::iter::Peekable;
use std::slice::Iter;
//
// Parser
//
#[derive(Debug)]
pub enum UnaryOp {
    ExprStmt,
    Return,
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
        var: Var,
    },
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

    pub fn new_var_node(var: Var) -> Self {
        let kind = NodeKind::Var { var };
        Node::new(kind)
    }

    // stmt = "return" expr ";"
    //      | expr-stmt
    fn stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
        let tok = tok_peek.peek().unwrap();
        if tok.equal("return") {
            tok_peek.next();
            let node = Node::new_unary(UnaryOp::Return, Node::expr(tok_peek, locals));
            skip(tok_peek, ";");
            return node;
        }
        Node::expr_stmt(tok_peek, locals)
    }

    // expr-stmt = expr ";"
    fn expr_stmt(tok_peek: &mut Peekable<Iter<Token>>, locals: &mut Vec<Var>) -> Node {
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
                node = Node::new_bin(BinOp::Add, node, rhs);
                continue;
            }
            if tok.equal("-") {
                tok_peek.next();
                let rhs = Node::mul(tok_peek, locals);
                node = Node::new_bin(BinOp::Sub, node, rhs);
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

    // unary = ("+" | "-") unary
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
            _ => Node::new(NodeKind::Num(tok.get_number().unwrap())),
        }
    }

}

pub struct Function {
    pub nodes: Vec<Node>,
    #[allow(dead_code)]
    locals: Vec<Var>, // local variables
    pub stack_size: usize,
}

impl Function {
    fn new(nodes: Vec<Node>, locals: Vec<Var>) -> Self { 
        let offset = 32 + 8 * (locals.len() + 1);
        let stack_size = align_to(offset, 16);

        Self { nodes, locals, stack_size } 
    }


    // program = stmt*
    pub fn parse(tok_peek: &mut Peekable<Iter<Token>>) -> Self {
        let mut nodes = Vec::new();
        // All local variable instances created during parsing are
        // accumulated to this list.
        let mut locals = Vec::new();
        while let Some(tok) = tok_peek.peek() {
            if !matches!(tok.kind, TokenKind::Eof) {
                let node = Node::stmt(tok_peek, &mut locals);
                nodes.push(node);
            } else {
                // eofをskip
                skip(tok_peek, "EOF");
            }
        }
        Function::new(nodes, locals)
    }
}
