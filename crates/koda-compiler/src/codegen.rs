use crate::ast::Program;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CodegenError {
    #[error("{0}")]
    Msg(String),
}

pub type CodegenResult<T> = Result<T, CodegenError>;

#[cfg(feature = "llvm")]
pub fn compile_with_llvm(prog: &Program) -> CodegenResult<()> {
    use inkwell::context::Context;
    use inkwell::OptimizationLevel;

    let context = Context::create();
    let _module = context.create_module("koda_module");
    let _builder = context.create_builder();
    let _ee = _module
        .create_jit_execution_engine(OptimizationLevel::Aggressive)
        .map_err(|e| CodegenError::Msg(format!("failed to create JIT: {}", e)))?;

    // TODO: lower Program -> IR -> LLVM IR
    let _ = prog; // silence unused for now

    Ok(())
}

#[cfg(not(feature = "llvm"))]
pub fn compile_with_llvm(_prog: &Program) -> CodegenResult<()> {
    Err(CodegenError::Msg(
        "LLVM backend not enabled; rebuild with --features koda-compiler/llvm".into(),
    ))
}
