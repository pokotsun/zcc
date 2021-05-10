use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum TypeKind {
    Int,
    Ptr(Rc<TypeKind>),
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
    pub kind: Rc<TypeKind>,
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
    fn new(kind: Rc<TypeKind>, name: String, size: usize) -> Self {
        Self {
            kind,
            name: RefCell::new(name),
            size,
        }
    }
    pub fn new_int() -> Self {
        // FIXME ここのString::newは消せないのか?
        Self::new(Rc::new(TypeKind::Int), String::new(), 8)
    }

    pub fn pointer_to(base: Rc<Type>, name: String) -> Self {
        Self::new(Rc::new(TypeKind::Ptr(base.kind.clone())), name, 8)
    }

    pub fn array_of(base: Rc<Type>, length: usize) -> Self {
        let size = base.size * length;
        Self::new(
            Rc::new(
            TypeKind::Arr {
                base,
                length,
            }),
            String::new(),
            size,
        )
    }

    pub fn is_ptr(self) -> bool {
        match self.kind.as_ref() {
            TypeKind::Ptr(_) => true,
            _ => false,
        }
    }

    pub fn new_func(kind: Rc<TypeKind>, params: Vec<Type>) -> Self {
        Self::new(
            Rc::new(
            TypeKind::Func {
                return_ty: kind,
                params,
            }),
            String::new(),
            32,
        )
    }
}
