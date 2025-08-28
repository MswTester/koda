#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BaseType {
    U32,
    I32,
    F32,
    Bool,
    String,
    Unit,
    Option,
    Range,
    Vec,
    Set,
    Map,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeName {
    pub base: BaseType,
    pub params: Vec<TypeName>,
}

impl TypeName {
    pub fn simple(base: BaseType) -> Self { Self { base, params: vec![] } }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Unit,
    U32,
    I32,
    F32,
    Bool,
    String,
    // Option and Range wrappers
    Option(Box<Type>),
    Range(Box<Type>),
    // Collections
    Vec(Box<Type>),
    Set(Box<Type>),
    Map(Box<Type>, Box<Type>),
    // Function type: (params...) -> ret
    Func(Vec<Type>, Box<Type>),
    // Type variable for inference/unification
    Var(u32),
    // Integer literal type before resolution to concrete numeric type
    IntLit,
}
