use crate::node::Member;
use std::cell::RefCell;
use std::rc::Rc;

pub type FuncParam = (Type, String);

#[derive(Clone, Debug)]
pub enum TypeKind {
    Char,
    Short,
    Int,
    Long,
    Ptr(Rc<RefCell<Type>>),
    Func {
        return_ty: Rc<TypeKind>,
        params: Vec<FuncParam>,
    },
    Arr {
        base: Rc<RefCell<Type>>,
        length: usize,
    },
    Struct {
        members: Vec<Member>,
    },
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: Rc<TypeKind>,
    pub size: usize, // sizeof() value
    // Pointer-to or array-of type. We intentionally use the same member
    // to represent pointer/array duality in C.
    //
    // In many contexts in which a pointer is expected, we examine this
    // member instead of "kind" member to determine whether a type is a
    // pointer or not. That means in many contexts "array of T" is
    // naturally handled as if it were "pointer to T", as required by
    // the C spec.
    pub align: usize,
}

impl Type {
    fn new(kind: Rc<TypeKind>, size: usize, align: usize) -> Self {
        Self { kind, size, align }
    }

    pub fn new_char() -> Self {
        Self::new(Rc::new(TypeKind::Char), 1, 1)
    }

    pub fn new_short() -> Self {
        Self::new(Rc::new(TypeKind::Short), 2, 2)
    }

    pub fn new_int() -> Self {
        Self::new(Rc::new(TypeKind::Int), 4, 4)
    }

    pub fn new_long() -> Self {
        Self::new(Rc::new(TypeKind::Long), 8, 8)
    }

    pub fn pointer_to(base: Rc<RefCell<Type>>) -> Self {
        Self::new(Rc::new(TypeKind::Ptr(base)), 8, 8)
    }

    pub fn array_of(base: Rc<RefCell<Type>>, length: usize) -> Self {
        let size = base.borrow().size * length;
        let align = base.borrow().align;
        let ty = Self::new(Rc::new(TypeKind::Arr { base: base, length }), size, align);
        ty
    }

    pub fn new_string(length: usize) -> Self {
        Self::array_of(Rc::new(RefCell::new(Self::new_char())), length)
    }

    pub fn new_struct(members: Vec<Member>, size: usize, align: usize) -> Self {
        Self::new(Rc::new(TypeKind::Struct { members }), size, align)
    }

    pub fn is_ptr(&self) -> bool {
        match self.kind.as_ref() {
            TypeKind::Ptr(_) | TypeKind::Arr { .. } => true,
            _ => false,
        }
    }

    pub fn new_func(kind: Rc<TypeKind>, params: Vec<FuncParam>) -> Self {
        Self::new(
            Rc::new(TypeKind::Func {
                return_ty: kind,
                params,
            }),
            32,
            32, // TODO 要検討
        )
    }
}
