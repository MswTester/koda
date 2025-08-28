use crate::error::{LexError, LexErrorKind, LexResult};
use crate::token::{Position, Token, TokenKind};

pub struct Lexer {
    input: Vec<char>,
    len: usize,
    idx: usize,
    line: usize,
    col: usize,
}

impl Lexer {
    pub fn new(source: &str) -> Self {
        let input: Vec<char> = source.chars().collect();
        let len = input.len();
        Self { input, len, idx: 0, line: 1, col: 1 }
    }

    fn pos(&self) -> Position { Position { index: self.idx, line: self.line, column: self.col } }

    fn peek(&self) -> Option<char> { self.input.get(self.idx).copied() }

    fn bump(&mut self) -> Option<char> {
        if self.idx >= self.len { return None; }
        let ch = self.input[self.idx];
        self.idx += 1;
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }

    fn match_next(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.bump();
            true
        } else { false }
    }

    fn skip_ws_and_comments(&mut self) -> Option<Token> {
        loop {
            match self.peek() {
                Some(' ' | '\t' | '\r') => { self.bump(); }
                Some('#') => {
                    while let Some(c) = self.peek() { if c == '\n' { break; } self.bump(); }
                }
                _ => break,
            }
        }
        // emit Newline tokens one-by-one to preserve statement boundaries
        if self.peek() == Some('\n') {
            let pos = self.pos();
            self.bump();
            return Some(Token { kind: TokenKind::Newline, pos });
        }
        None
    }

    fn read_ident_or_kw(&mut self) -> Token {
        let pos = self.pos();
        let mut s = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' { s.push(ch); self.bump(); } else { break; }
        }
        let kind = match s.as_str() {
            "return" => TokenKind::Return,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "none" => TokenKind::NoneKw,
            "for" => TokenKind::For,
            "in" => TokenKind::In,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "as" => TokenKind::As,
            _ => TokenKind::Ident(s),
        };
        Token { kind, pos }
    }

    fn read_number(&mut self) -> Result<Token, LexError> {
        let pos = self.pos();
        let mut value: u128 = 0;
        let mut has_digit = false;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                has_digit = true;
                let d = (ch as u8 - b'0') as u128;
                value = value.checked_mul(10).ok_or(LexError { kind: LexErrorKind::IntOverflow, pos })?;
                value = value.checked_add(d).ok_or(LexError { kind: LexErrorKind::IntOverflow, pos })?;
                self.bump();
            } else { break; }
        }
        if !has_digit { return Err(LexError { kind: LexErrorKind::InvalidChar { ch: self.peek().unwrap_or('\0') }, pos }); }
        let v = u64::try_from(value).map_err(|_| LexError { kind: LexErrorKind::IntOverflow, pos })?;
        Ok(Token { kind: TokenKind::Int(v), pos })
    }

    fn read_string(&mut self) -> Result<Token, LexError> {
        let start = self.pos();
        // opening quote already consumed
        let mut s = String::new();
        loop {
            match self.bump() {
                Some('"') => break,
                Some('\\') => match self.bump() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some('"') => s.push('"'),
                    Some('\\') => s.push('\\'),
                    Some(_) | None => return Err(LexError { kind: LexErrorKind::InvalidEscape, pos: start }),
                },
                Some(ch) => s.push(ch),
                None => return Err(LexError { kind: LexErrorKind::UnterminatedString, pos: start }),
            }
        }
        Ok(Token { kind: TokenKind::StringLit(s), pos: start })
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        if let Some(tok) = self.skip_ws_and_comments() { return Ok(tok); }
        let pos = self.pos();
        let ch = match self.peek() { Some(c) => c, None => return Ok(Token { kind: TokenKind::Eof, pos }) };
        match ch {
            'a'..='z' | 'A'..='Z' | '_' => Ok(self.read_ident_or_kw()),
            '0'..='9' => self.read_number(),
            '"' => { self.bump(); self.read_string() },
            '(' => { self.bump(); Ok(Token { kind: TokenKind::LParen, pos }) }
            ')' => { self.bump(); Ok(Token { kind: TokenKind::RParen, pos }) }
            '{' => { self.bump(); Ok(Token { kind: TokenKind::LBrace, pos }) }
            '}' => { self.bump(); Ok(Token { kind: TokenKind::RBrace, pos }) }
            ',' => { self.bump(); Ok(Token { kind: TokenKind::Comma, pos }) }
            ':' => { self.bump(); Ok(Token { kind: TokenKind::Colon, pos }) }
            '?' => { self.bump(); Ok(Token { kind: TokenKind::Question, pos }) }
            '.' => { 
                self.bump();
                if self.match_next('.') { Ok(Token { kind: TokenKind::DotDot, pos }) } else { Ok(Token { kind: TokenKind::Dot, pos }) }
            }
            '+' => { self.bump(); Ok(Token { kind: TokenKind::Plus, pos }) }
            '-' => { 
                self.bump();
                if self.match_next('>') { Ok(Token { kind: TokenKind::Arrow, pos }) } else { Ok(Token { kind: TokenKind::Minus, pos }) }
            }
            '*' => { self.bump(); Ok(Token { kind: TokenKind::Star, pos }) }
            '/' => { self.bump(); Ok(Token { kind: TokenKind::Slash, pos }) }
            '=' => { 
                self.bump();
                if self.match_next('=') { Ok(Token { kind: TokenKind::EqEq, pos }) } else { Ok(Token { kind: TokenKind::Eq, pos }) }
            }
            '!' => {
                self.bump();
                if self.match_next('=') { Ok(Token { kind: TokenKind::NotEq, pos }) } else { Err(LexError { kind: LexErrorKind::InvalidChar { ch: '!' }, pos }) }
            }
            '<' => {
                self.bump();
                if self.match_next('=') { Ok(Token { kind: TokenKind::Le, pos }) } else { Ok(Token { kind: TokenKind::Lt, pos }) }
            }
            '>' => {
                self.bump();
                if self.match_next('=') { Ok(Token { kind: TokenKind::Ge, pos }) } else { Ok(Token { kind: TokenKind::Gt, pos }) }
            }
            '\n' => { self.bump(); Ok(Token { kind: TokenKind::Newline, pos }) }
            _ => Err(LexError { kind: LexErrorKind::InvalidChar { ch }, pos }),
        }
    }
}
