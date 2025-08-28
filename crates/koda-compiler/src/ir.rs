use crate::types::Type;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrValueKind {
    Unit,
    Bool(bool),
    IntU32(u32),
    IntI32(i32),
    FloatF32(u32), // store as raw bits to preserve NaN payloads if needed
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrValue {
    pub ty: Type,
    pub kind: IrValueKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IrInstr {
    // Arithmetic
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Div(usize, usize),
    // Comparisons => bool
    Eq(usize, usize),
    Ne(usize, usize),
    Lt(usize, usize),
    Le(usize, usize),
    Gt(usize, usize),
    Ge(usize, usize),
    // Casts
    Cast { src: usize, to: Type },
    // Calls to builtins (e.g., print)
    Call { callee: String, args: Vec<usize>, ret: Type },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrBlock {
    pub instrs: Vec<IrInstr>,
    // Values table lives at function/module level; instrs refer to indices
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrFunction {
    pub name: String,
    pub params: Vec<Type>,
    pub ret: Type,
    pub block: IrBlock,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrModule {
    pub functions: Vec<IrFunction>,
}

impl IrModule {
    pub fn new() -> Self { Self { functions: vec![] } }
}
