use crate::token::Position;
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum LexErrorKind {
    #[error("invalid character '{ch}'")]
    InvalidChar { ch: char },
    #[error("unterminated string literal")]
    UnterminatedString,
    #[error("invalid escape sequence")] 
    InvalidEscape,
    #[error("integer overflow")] 
    IntOverflow,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("lex error at {pos:?}: {kind}")]
pub struct LexError {
    pub kind: LexErrorKind,
    pub pos: Position,
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ParseErrorKind {
    #[error("unexpected token, expected {expected}, found {found:?}")]
    UnexpectedToken { expected: &'static str, found: &'static str },
    #[error("unexpected end of input")] 
    UnexpectedEof,
    #[error("from lexer: {0}")]
    FromLex(String),
}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[error("parse error at {pos:?}: {kind}")]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub pos: Position,
}

pub type LexResult<T> = Result<T, LexError>;
pub type ParseResult<T> = Result<T, ParseError>;
