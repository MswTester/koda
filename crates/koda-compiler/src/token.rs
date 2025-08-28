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
    PlusEq,
    Minus,
    MinusEq,
    Star,
    StarEq,
    Slash,
    SlashEq,
    Percent,
    PercentEq,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Question,
    QuestionQuestion,
    QuestionQuestionEq,
    Dot,
    DotDot,
    Eq,
    EqEq,
    NotEq,
    Not,
    Amp,
    AmpEq,
    AmpAmp,
    AmpAmpEq,
    Pipe,
    PipeEq,
    PipePipe,
    PipePipeEq,
    Caret,
    CaretEq,
    Lt,
    Le,
    Shl,
    ShlEq,
    Gt,
    Ge,
    Shr,
    ShrEq,
    Arrow,
    Newline,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub pos: Position,
}
