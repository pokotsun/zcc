use std::rc::Rc;

#[derive(Debug)]
pub enum Type {
    Int,
    Ptr(Rc<Type>),
}

impl Type {
    pub fn new_int() -> Self {
        Self::Int
    }

    pub fn pointer_to(base: Self) -> Self {
        Self::Ptr(Rc::new(base))
    }

    pub fn is_ptr(self) -> bool {
        match self {
            Type::Ptr(_) => true,
            _ => false,
        }
    }
}
