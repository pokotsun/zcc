use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum TypeKind {
    Int,
    Ptr(Rc<Type>),
    Func {
        return_ty: Rc<TypeKind>,
        params: Vec<Type>,
    },
    Arr {
        base: Rc<Type>,
        length: usize,
    },
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub name: RefCell<String>,
    pub size: usize, // sizeof() value
                     // Pointer-to or array-of type. We intentionally use the same member
                     // to represent pointer/array duality in C.
                     //
                     // In many contexts in which a pointer is expected, we examine this
                     // member instead of "kind" member to determine whether a type is a
                     // pointer or not. That means in many contexts "array of T" is
                     // naturally handled as if it were "pointer to T", as required by
                     // the C spec.
}

impl Type {
    fn new(kind: TypeKind, name: String, size: usize) -> Self {
        Self {
            kind,
            name: RefCell::new(name),
            size,
        }
    }
    pub fn new_int() -> Self {
        // FIXME ここのString::newは消せないのか?
        Self::new(TypeKind::Int, String::new(), 8)
    }

    pub fn pointer_to(base: Rc<Type>, name: String) -> Self {
        Self::new(TypeKind::Ptr(Rc::new((*base).clone())), name, 8)
    }

    pub fn array_of(base: Type, length: usize) -> Self {
        let size = base.size * length;
        let ty = Self::new(
            TypeKind::Arr {
                base: Rc::new(base),
                length,
            },
            String::new(),
            size,
        );
        ty
    }

    pub fn is_ptr(self) -> bool {
        match self.kind {
            TypeKind::Ptr(_) | TypeKind::Arr { .. } => true,
            _ => false,
        }
    }

    pub fn new_func(kind: TypeKind, params: Vec<Type>) -> Self {
        Self::new(
            TypeKind::Func {
                return_ty: Rc::new(kind),
                params,
            },
            String::new(),
            32,
        )
    }
}
