#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position {
    pub index: usize,
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn new(index: usize, line: usize, column: usize) -> Self { Self { index, line, column } }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Int(u64),
    StringLit(String),

    // Keywords
    Return,
    True,
    False,
    NoneKw,
    For,
    In,
    While,
    Loop,
    Break,
    Continue,
    As,

    // Symbols / Operators
    Plus,
    Minus,
    Star,
    Slash,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Question,
    Dot,
    DotDot,
    Eq,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Arrow,
    Newline,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub pos: Position,
}
