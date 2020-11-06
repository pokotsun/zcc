use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum TypeKind {
    Int,
    Ptr(Rc<TypeKind>),
}

#[derive(Clone, Debug)]
pub struct Type {
    kind: TypeKind,
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
}
