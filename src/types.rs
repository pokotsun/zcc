use std::rc::Rc;

pub type FuncParam = (Type, String);

#[derive(Clone, Debug)]
pub enum TypeKind {
    Int,
    Ptr(Rc<Type>),
    Func {
        return_ty: Rc<TypeKind>,
        params: Vec<FuncParam>,
    },
    Arr {
        base: Rc<Type>,
        length: usize,
    },
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
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
    fn new(kind: TypeKind, size: usize) -> Self {
        Self { kind, size }
    }
    pub fn new_int() -> Self {
        // FIXME ここのString::newは消せないのか?
        Self::new(TypeKind::Int, 8)
    }

    pub fn pointer_to(base: Rc<Type>) -> Self {
        Self::new(TypeKind::Ptr(Rc::new((*base).clone())), 8)
    }

    pub fn array_of(base: Type, length: usize) -> Self {
        let size = base.size * length;
        let ty = Self::new(
            TypeKind::Arr {
                base: Rc::new(base),
                length,
            },
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

    pub fn new_func(kind: TypeKind, params: Vec<FuncParam>) -> Self {
        Self::new(
            TypeKind::Func {
                return_ty: Rc::new(kind),
                params,
            },
            32,
        )
    }
}
