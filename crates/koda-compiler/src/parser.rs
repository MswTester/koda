use crate::ast::*;
use crate::error::{ParseError, ParseErrorKind, ParseResult};
use crate::lexer::Lexer;
use crate::token::{Token, TokenKind, Position};
use crate::types::{BaseType, TypeName};

pub struct Parser {
    tokens: Vec<Token>,
    idx: usize,
}

impl Parser {
    pub fn from_source(src: &str) -> ParseResult<Self> {
        let mut lex = Lexer::new(src);
        let mut tokens = Vec::new();
        loop {
            match lex.next_token() {
                Ok(tok) => {
                    if tok.kind == TokenKind::Eof { tokens.push(tok); break; }
                    tokens.push(tok);
                }
                Err(e) => return Err(ParseError { kind: ParseErrorKind::FromLex(format!("{}", e)), pos: e.pos }),
            }
        }
        Ok(Self { tokens, idx: 0 })
    }

    pub fn parse_program(&mut self) -> ParseResult<Program> {
        let mut stmts = Vec::new();
        while !self.is(TokenKind::Eof) {
            self.skip_newlines();
            if self.is(TokenKind::Eof) { break; }
            stmts.push(self.parse_stmt()?);
            self.skip_stmt_sep();
        }
        Ok(Program { stmts })
    }

    fn cur(&self) -> &Token { &self.tokens[self.idx] }
    fn is(&self, kind: TokenKind) -> bool { self.cur().kind == kind }

    fn bump(&mut self) { if self.idx < self.tokens.len() - 1 { self.idx += 1; } }

    fn skip_newlines(&mut self) { while matches!(self.cur().kind, TokenKind::Newline) { self.bump(); } }

    fn skip_stmt_sep(&mut self) { while matches!(self.cur().kind, TokenKind::Newline) { self.bump(); } }

    fn expect(&mut self, expected: TokenKind) -> ParseResult<Token> {
        if self.cur().kind == expected { let t = self.cur().clone(); self.bump(); Ok(t) } else {
            Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: Self::kind_name(&expected), found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos })
        }
    }

    fn kind_name(k: &TokenKind) -> &'static str {
        use TokenKind::*;
        match k {
            Ident(_) => "identifier",
            Int(_) => "integer",
            StringLit(_) => "string",
            Return => "return",
            True => "true",
            False => "false",
            NoneKw => "none",
            For => "for",
            In => "in",
            While => "while",
            Loop => "loop",
            Break => "break",
            Continue => "continue",
            As => "as",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            LParen => "(",
            RParen => ")",
            LBrace => "{",
            RBrace => "}",
            Comma => ",",
            Colon => ":",
            Question => "?",
            Dot => ".",
            DotDot => "..",
            Eq => "=",
            EqEq => "==",
            NotEq => "!=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
            Arrow => "->",
            Newline => "newline",
            Eof => "eof",
        }
    }

    fn parse_stmt(&mut self) -> ParseResult<Stmt> {
        self.skip_newlines();
        match &self.cur().kind {
            TokenKind::For => self.parse_for_stmt(),
            TokenKind::While => self.parse_while_stmt(),
            TokenKind::Loop => self.parse_loop_stmt(),
            TokenKind::Break => { let pos = self.cur().pos; self.bump(); Ok(Stmt::Break(pos)) }
            TokenKind::Continue => { let pos = self.cur().pos; self.bump(); Ok(Stmt::Continue(pos)) }
            TokenKind::Return => self.parse_return_stmt(),
            TokenKind::Ident(_) => {
                // try let/assign: ident [: type]? = expr
                if self.peek_is_colon_or_eq() { self.parse_let_like() } else {
                    let e = self.parse_expr()?; let pos = Self::expr_pos(&e); Ok(Stmt::ExprStmt(e, pos))
                }
            }
            _ => { let e = self.parse_expr()?; let pos = Self::expr_pos(&e); Ok(Stmt::ExprStmt(e, pos)) }
        }
    }

    fn peek_is_colon_or_eq(&self) -> bool {
        if let TokenKind::Ident(_) = &self.cur().kind { /* ok */ } else { return false; }
        if self.idx + 1 >= self.tokens.len() { return false; }
        matches!(self.tokens[self.idx+1].kind, TokenKind::Colon | TokenKind::Eq)
    }

    fn parse_let_like(&mut self) -> ParseResult<Stmt> {
        let name = if let TokenKind::Ident(s) = &self.cur().kind { s.clone() } else { unreachable!() };
        let pos = self.cur().pos; self.bump();
        let ty = if matches!(self.cur().kind, TokenKind::Colon) { self.bump(); Some(self.parse_type()?) } else { None };
        self.expect(TokenKind::Eq)?;
        let value = self.parse_expr()?;
        Ok(Stmt::Let { name, ty, value, pos })
    }

    fn parse_return_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        if matches!(self.cur().kind, TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof) {
            Ok(Stmt::Return(None, pos))
        } else {
            let e = self.parse_expr()?;
            Ok(Stmt::Return(Some(e), pos))
        }
    }

    fn parse_for_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        // for i in expr { ... } | for expr { ... }
        match &self.cur().kind {
            TokenKind::Ident(name) => {
                let name_s = name.clone();
                if matches!(self.tokens.get(self.idx+1).map(|t| &t.kind), Some(TokenKind::In)) {
                    self.bump(); // ident
                    self.expect(TokenKind::In)?;
                    let iter = self.parse_expr()?;
                    let body = self.parse_block()?;
                    Ok(Stmt::ForIn { name: name_s, iter, body, pos })
                } else {
                    // not 'in' form, treat as expr times
                    let expr = Expr::Ident(name_s, self.tokens[self.idx-1].pos);
                    let times = self.parse_postfix_after_ident(expr)?;
                    let body = self.parse_block()?;
                    Ok(Stmt::ForTimes { times, body, pos })
                }
            }
            _ => {
                let times = self.parse_expr()?;
                let body = self.parse_block()?;
                Ok(Stmt::ForTimes { times, body, pos })
            }
        }
    }

    fn parse_while_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        let cond = self.parse_expr()?;
        let body = self.parse_block()?;
        Ok(Stmt::While { cond, body, pos })
    }

    fn parse_loop_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        let body = self.parse_block()?;
        Ok(Stmt::Loop { body, pos })
    }

    fn parse_block(&mut self) -> ParseResult<Block> {
        let pos = self.expect(TokenKind::LBrace)?.pos;
        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.cur().kind, TokenKind::RBrace) { self.bump(); break; }
            if matches!(self.cur().kind, TokenKind::Eof) { return Err(ParseError { kind: ParseErrorKind::UnexpectedEof, pos }); }
            let s = self.parse_stmt()?;
            stmts.push(s);
            self.skip_stmt_sep();
        }
        Ok(Block { stmts, pos })
    }

    fn parse_expr_or_block(&mut self) -> ParseResult<Expr> {
        if matches!(self.cur().kind, TokenKind::LBrace) { Ok(Expr::Block(self.parse_block()?)) } else { self.parse_expr() }
    }

    fn parse_expr(&mut self) -> ParseResult<Expr> { self.parse_ternary() }

    fn parse_ternary(&mut self) -> ParseResult<Expr> {
        let cond = self.parse_compare()?;
        if matches!(self.cur().kind, TokenKind::Question) {
            let pos = if let Some(p) = Self::expr_pos_opt(&cond) { p } else { self.cur().pos };
            self.bump();
            let then_e = self.parse_expr_or_block()?;
            let else_e = if matches!(self.cur().kind, TokenKind::Colon) { self.bump(); Some(self.parse_expr_or_block()?) } else { None };
            Ok(Expr::IfElse { cond: Box::new(cond), then_e: Box::new(then_e), else_e: else_e.map(Box::new), pos })
        } else { Ok(cond) }
    }

    fn parse_compare(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_add_sub()?;
        loop {
            let pos = Self::expr_pos(&left);
            let op = match self.cur().kind {
                TokenKind::EqEq => BinOp::Eq,
                TokenKind::NotEq => BinOp::Ne,
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Le => BinOp::Le,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::Ge => BinOp::Ge,
                _ => break,
            };
            self.bump();
            let right = self.parse_add_sub()?;
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_add_sub(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_mul_div()?;
        loop {
            let pos = Self::expr_pos(&left);
            let op = match self.cur().kind { TokenKind::Plus => BinOp::Add, TokenKind::Minus => BinOp::Sub, _ => break };
            self.bump();
            let right = self.parse_mul_div()?;
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_mul_div(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_unary()?;
        loop {
            let pos = Self::expr_pos(&left);
            let op = match self.cur().kind { TokenKind::Star => BinOp::Mul, TokenKind::Slash => BinOp::Div, _ => break };
            self.bump();
            let right = self.parse_unary()?;
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> ParseResult<Expr> {
        match self.cur().kind {
            TokenKind::Minus => { let pos = self.cur().pos; self.bump(); let e = self.parse_unary()?; Ok(Expr::Unary { op: UnOp::Neg, expr: Box::new(e), pos }) }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> ParseResult<Expr> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.cur().kind {
                TokenKind::LParen => {
                    let pos = Self::expr_pos(&expr);
                    let mut args = Vec::new();
                    self.bump();
                    if !matches!(self.cur().kind, TokenKind::RParen) {
                        loop {
                            args.push(self.parse_expr()?);
                            if matches!(self.cur().kind, TokenKind::Comma) { self.bump(); continue; }
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    expr = Expr::Call { callee: Box::new(expr), args, pos };
                }
                TokenKind::Dot => {
                    // method-style conversions: .string() .i32() .u32() .f32()
                    let dot_pos = self.cur().pos; self.bump();
                    let name = match &self.cur().kind { TokenKind::Ident(s) => s.clone(), _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "conversion name", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos }) };
                    self.bump();
                    self.expect(TokenKind::LParen)?; // require empty parens
                    self.expect(TokenKind::RParen)?;
                    let to = match name.as_str() {
                        "string" => TypeName { base: BaseType::String, params: vec![] },
                        "i32" => TypeName { base: BaseType::I32, params: vec![] },
                        "u32" => TypeName { base: BaseType::U32, params: vec![] },
                        "f32" => TypeName { base: BaseType::F32, params: vec![] },
                        _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "conversion name (.string/.i32/.u32/.f32)", found: "identifier" }, pos: dot_pos }),
                    };
                    expr = Expr::Cast { expr: Box::new(expr), to, pos: dot_pos };
                }
                TokenKind::As => {
                    // explicit cast: expr as Type
                    let as_pos = self.cur().pos; self.bump();
                    let to = self.parse_type()?;
                    expr = Expr::Cast { expr: Box::new(expr), to, pos: as_pos };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> ParseResult<Expr> {
        match &self.cur().kind {
            TokenKind::Int(v) => { let pos = self.cur().pos; let val = *v; self.bump();
                // possible range: previous expression .. next expression handled in parse_range? Easier: if next is DotDot, parse start..end here
                if matches!(self.cur().kind, TokenKind::DotDot) {
                    self.bump();
                    let end = self.parse_unary()?;
                    let start = Expr::Int(val, pos);
                    let p = pos;
                    Ok(Expr::Range { start: Box::new(start), end: Box::new(end), pos: p })
                } else { Ok(Expr::Int(val, pos)) }
            }
            TokenKind::True => { let pos = self.cur().pos; self.bump(); Ok(Expr::Bool(true, pos)) }
            TokenKind::False => { let pos = self.cur().pos; self.bump(); Ok(Expr::Bool(false, pos)) }
            TokenKind::NoneKw => { let pos = self.cur().pos; self.bump(); Ok(Expr::NoneLit(pos)) }
            TokenKind::StringLit(s) => { let pos = self.cur().pos; let lit = s.clone(); self.bump(); Ok(Expr::String(lit, pos)) }
            TokenKind::Ident(name) => { let pos = self.cur().pos; let n = name.clone(); self.bump(); Ok(Expr::Ident(n, pos)) }
            TokenKind::LParen => {
                // Could be fn-literal or grouped expr
                let save = self.idx; let pos = self.cur().pos; self.bump();
                // Try to parse params list
                let mut params: Vec<Param> = Vec::new();
                let mut is_param_list = true;
                if matches!(self.cur().kind, TokenKind::RParen) {
                    // empty parameter list
                } else {
                    loop {
                        match &self.cur().kind {
                            TokenKind::Ident(n) => {
                                let name = n.clone(); self.bump();
                                let ty = if matches!(self.cur().kind, TokenKind::Colon) { self.bump(); Some(self.parse_type()?) } else { None };
                                params.push(Param { name, ty });
                            }
                            _ => { is_param_list = false; break; }
                        }
                        if matches!(self.cur().kind, TokenKind::Comma) { self.bump(); continue; }
                        break;
                    }
                }
                if is_param_list { self.expect(TokenKind::RParen)?; }
                if is_param_list && matches!(self.cur().kind, TokenKind::Arrow) {
                    self.bump();
                    // optional return type before block
                    let ret = if matches!(self.cur().kind, TokenKind::LBrace) { None } else { Some(self.parse_type()?) };
                    let body = self.parse_block()?;
                    Ok(Expr::FnLit { params, ret, body, pos })
                } else {
                    // not a function literal -> fallback to grouped expr
                    self.idx = save; // rewind
                    self.expect(TokenKind::LParen)?; // consume '('
                    let e = self.parse_expr()?; self.expect(TokenKind::RParen)?; Ok(e)
                }
            }
            TokenKind::LBrace => { let b = self.parse_block()?; Ok(Expr::Block(b)) }
            _ => Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "expression", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos })
        }
    }

    fn parse_type(&mut self) -> ParseResult<TypeName> {
        // simple identifiers as types + Option<T> / Range<T> with single parameter using angle brackets is not in syntax; using names like Option<u32> would require '<' '>' which we don't have. For now parse builtins by identifier.
        let ident = match &self.cur().kind { TokenKind::Ident(s) => s.clone(), _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "type name", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos }) };
        self.bump();
        let base = match ident.as_str() { "u32" => BaseType::U32, "i32" => BaseType::I32, "f32" => BaseType::F32, "bool" => BaseType::Bool, "string" => BaseType::String, _ => BaseType::Unit };
        Ok(TypeName { base, params: vec![] })
    }

    fn parse_postfix_after_ident(&mut self, ident_expr: Expr) -> ParseResult<Expr> {
        // support immediate postfix like call if needed; currently used for 'for times' when first token after 'for' was ident but not 'in'
        let mut expr = ident_expr;
        loop {
            match self.cur().kind {
                TokenKind::LParen => {
                    let pos = Self::expr_pos(&expr);
                    let mut args = Vec::new();
                    self.bump();
                    if !matches!(self.cur().kind, TokenKind::RParen) {
                        loop {
                            args.push(self.parse_expr()?);
                            if matches!(self.cur().kind, TokenKind::Comma) { self.bump(); continue; }
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    expr = Expr::Call { callee: Box::new(expr), args, pos };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn expr_pos(e: &Expr) -> Position { Self::expr_pos_opt(e).unwrap() }
    fn expr_pos_opt(e: &Expr) -> Option<Position> {
        match e {
            Expr::Int(_, p) | Expr::Bool(_, p) | Expr::String(_, p) | Expr::NoneLit(p) | Expr::Ident(_, p) | Expr::Binary { pos: p, .. } | Expr::Unary { pos: p, .. } | Expr::Call { pos: p, .. } | Expr::Range { pos: p, .. } | Expr::IfElse { pos: p, .. } | Expr::FnLit { pos: p, .. } | Expr::Cast { pos: p, .. } => Some(*p),
            Expr::Block(b) => Some(b.pos),
        }
    }
}
