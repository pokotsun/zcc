use crate::types::{Type, TypeKind};
use std::cell::Cell;
use std::rc::Rc;

#[derive(Debug)]
pub enum UnaryOp {
    ExprStmt,
    StmtExpr, // statement expression
    Return,
    Addr,
    Deref,
    Member(Member),
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
    Comma,  // ,
}

#[derive(Debug)]
pub enum NodeKind {
    Num(usize), // Integer
    Unary(UnaryOp, Box<Node>),
    Bin {
        op: BinOp,
        lhs: Box<Node>, // Left-hand side
        rhs: Box<Node>, // Right-hand side
    },
    Var {
        var: Rc<Var>,
    },
    Struct {
        members: Vec<Member>,
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
        args: Vec<Rc<Var>>,
    }, // Function call
    NullExpr,         // Do nothing
}

// Variable
#[derive(Clone, Debug)]
pub enum VarType {
    Local(Rc<Cell<usize>>), // Offset from RBP
    Global(Vec<String>),    // initdata
}

#[derive(Clone, Debug)]
pub struct Var {
    pub name: String,
    pub ty: Type,
    pub var_ty: VarType,
    pub scope_depth: usize,
}

impl Var {
    pub fn new_lvar(name: String, offset: usize, ty: Type, scope_depth: usize) -> Var {
        Var {
            name,
            ty,
            var_ty: VarType::Local(Rc::new(Cell::new(offset))),
            scope_depth,
        }
    }

    pub fn new_gvar(name: String, ty: Type, init_data: Vec<String>) -> Var {
        Var {
            name,
            ty,
            var_ty: VarType::Global(init_data),
            scope_depth: 0,
        }
    }

    pub fn new_string_literal(name: String, init_data: Vec<String>) -> Var {
        let ty = Type::new_string(init_data.len());
        Var::new_gvar(name, ty, init_data)
    }
}
#[derive(Debug, Clone)]
pub struct Member {
    pub ty: Type,
    pub name: String,
    pub offset: Cell<usize>,
}

impl Member {
    pub fn new(ty: Type, name: String, offset: usize) -> Self {
        Self {
            ty,
            name,
            offset: Cell::new(offset),
        }
    }
}

// Scope for struct or union tags
pub struct TagScope {
    pub name: String,
    pub scope_depth: usize,
    pub ty: Type,
}

impl TagScope {
    pub fn new(name: String, scope_depth: usize, ty: Type) -> Self {
        Self {
            name,
            scope_depth,
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
                    TypeKind::Arr { base, .. } | TypeKind::Ptr(base) => (*base.as_ref()).clone(),
                    _ => unimplemented!("invalid pointer dereference"),
                },
                UnaryOp::StmtExpr => {
                    if let NodeKind::Block(nodes) = &child.kind {
                        if let Some(NodeKind::Unary(UnaryOp::ExprStmt, child)) =
                            nodes.last().map(|node| &node.kind)
                        {
                            return child.get_type();
                        }
                    }
                    unimplemented!("statement expression returning void is not supported");
                }
                UnaryOp::Member(member) => member.ty.clone(),
                _ => unreachable!(),
            },
            NodeKind::Bin {
                op: binop,
                lhs,
                rhs,
            } => match binop {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Assign => lhs.get_type(),
                BinOp::Equal | BinOp::NEqual | BinOp::Lt | BinOp::Le => Type::new_int(),
                BinOp::Comma => rhs.get_type(),
            },
            NodeKind::Var { var } => var.ty.clone(),
            NodeKind::Num(_) | NodeKind::FunCall { .. } => Type::new_long(),
            _ => unreachable!("\n{:#?}", self),
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
                    Self::new_bin(BinOp::Mul, rhs, Self::new(NodeKind::Num(lhs_size))),
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
                    Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(lhs_size)), rhs),
                )
            }
            // pointer - pointer, which returns how many elements are between the two.
            (true, true) => {
                let lhs_size = match lhs.get_type().kind.as_ref() {
                    TypeKind::Ptr(base) | TypeKind::Arr { base, .. } => base.size,
                    _ => unimplemented!("undefined internal type on ptr - ptr sub"),
                };
                Node::new_bin(
                    BinOp::Div,
                    Node::new_bin(BinOp::Sub, lhs, rhs),
                    Node::new(NodeKind::Num(lhs_size)),
                )
            }
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
