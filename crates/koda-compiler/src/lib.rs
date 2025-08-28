pub mod token;
pub mod error;
pub mod lexer;
pub mod types;
pub mod ast;
pub mod parser;
pub mod typeck;
pub mod ir;
pub mod codegen;

pub use token::{Token, TokenKind, Position};
pub use error::{LexError, ParseError};
pub use lexer::Lexer;
pub use parser::Parser;
pub use error::ParseResult;
pub use types::Type;
pub use typeck::{typecheck, TypeError, TypeResult};
pub use ir::{IrModule, IrFunction, IrBlock, IrInstr, IrValue, IrValueKind};
pub use codegen::{compile_with_llvm, CodegenError, CodegenResult};
