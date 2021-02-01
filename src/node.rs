use crate::types::{Type, TypeKind};
use std::rc::Rc;

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
    FunCall {
        name: String,
        args: Vec<Node>,
    }, // Function call
}

// Variable
#[derive(Clone, Debug)]
pub enum VarType {
    Local(usize),           // Offset from RBP
    Global(Option<String>), // initdata
}

#[derive(Clone, Debug)]
pub struct Var {
    pub name: String,
    pub ty: Type,
    pub var_ty: VarType,
}

impl Var {
    pub fn new_lvar(name: String, offset: usize, ty: Type) -> Var {
        Var {
            name,
            ty,
            var_ty: VarType::Local(offset),
        }
    }

    pub fn new_gvar(name: String, ty: Type, init_data: Option<String>) -> Var {
        Var {
            name,
            ty,
            var_ty: VarType::Global(init_data),
        }
    }

    pub fn new_string_literal(name: String, init_data: String) -> Var {
        let ty = Type::new_string(init_data.len());
        Var::new_gvar(name, ty, Some(init_data))
    }

    // 変数間のoffsetを計算するUtil関数 将来的に消す
    pub fn calc_offset(locals: &Vec<Var>) -> usize {
        32 + locals.iter().fold(0, |acc, var| acc + var.ty.size)
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
                UnaryOp::Addr => match child.get_type().kind {
                    TypeKind::Arr { base, length: _ } => Type::pointer_to(base),
                    _ => Type::pointer_to(Rc::new(child.get_type())),
                },
                UnaryOp::Deref => match child.get_type().kind {
                    TypeKind::Arr { base, .. } => (*base).clone(),
                    _ => child.get_type(),
                },
                _ => unreachable!(),
            },
            NodeKind::Bin { op: binop, lhs, .. } => match binop {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Assign => lhs.get_type(),
                BinOp::Equal | BinOp::NEqual | BinOp::Lt | BinOp::Le => Type::new_int(),
            },
            NodeKind::Var(var) => var.ty.clone(),
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
                let lhs_size = match lhs.get_type().kind {
                    TypeKind::Ptr(base) | TypeKind::Arr { base, .. } => base.size,
                    _ => unimplemented!("undefined internal type on ptr add"),
                };
                Self::new_bin(
                    BinOp::Sub,
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
                let lhs_size = match lhs.get_type().kind {
                    TypeKind::Ptr(base) | TypeKind::Arr { base, .. } => base.size,
                    _ => unimplemented!("undefined internal type on ptr sub"),
                };
                Self::new_bin(
                    BinOp::Add,
                    lhs,
                    Self::new_bin(BinOp::Mul, Self::new(NodeKind::Num(lhs_size as i64)), rhs),
                )
            }
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
}
