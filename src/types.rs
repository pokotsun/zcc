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
}

#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub name: RefCell<String>,
}

impl Type {
    fn new(kind: TypeKind, name: String) -> Self {
        Self {
            kind,
            name: RefCell::new(name),
        }
    }
    pub fn new_int() -> Self {
        // FIXME ここのString::newは消せないのか?
        Self::new(TypeKind::Int, String::new())
    }

    pub fn pointer_to(base: Type, name: String) -> Self {
        Self::new(TypeKind::Ptr(Rc::new(base.kind)), name)
    }

    pub fn is_ptr(self) -> bool {
        match self.kind {
            TypeKind::Ptr(_) => true,
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
        )
    }
}
