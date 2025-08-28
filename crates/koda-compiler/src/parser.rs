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
            PlusEq => "+=",
            Minus => "-",
            MinusEq => "-=",
            Star => "*",
            StarEq => "*=",
            Slash => "/",
            SlashEq => "/=",
            Percent => "%",
            PercentEq => "%=",
            LParen => "(",
            RParen => ")",
            LBrace => "{",
            RBrace => "}",
            Comma => ",",
            Colon => ":",
            Question => "?",
            QuestionQuestion => "??",
            QuestionQuestionEq => "??=",
            Dot => ".",
            DotDot => "..",
            Eq => "=",
            EqEq => "==",
            NotEq => "!=",
            Not => "!",
            Amp => "&",
            AmpEq => "&=",
            AmpAmp => "&&",
            AmpAmpEq => "&&=",
            Pipe => "|",
            PipeEq => "|=",
            PipePipe => "||",
            PipePipeEq => "||=",
            Caret => "^",
            CaretEq => "^=",
            Lt => "<",
            Le => "<=",
            Shl => "<<",
            ShlEq => "<<=",
            Gt => ">",
            Ge => ">=",
            Shr => ">>",
            ShrEq => ">>=",
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
                // try compound-assign or let-like decl: ident (op= | [: type]? = ) expr
                if self.peek_is_compound_assign() { self.parse_assign_stmt() } else if self.peek_is_colon_or_eq() { self.parse_let_like() } else {
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
                    let body = self.parse_maybe_typed_block()?;
                    Ok(Stmt::ForIn { name: name_s, iter, body, pos })
                } else {
                    // not 'in' form, treat as expr times
                    let pos_ident = self.cur().pos; // current token is the ident
                    self.bump(); // consume the ident before parsing the times expression/postfix
                    let expr = Expr::Ident(name_s, pos_ident);
                    let times = self.parse_postfix_after_ident(expr)?;
                    let body = self.parse_maybe_typed_block()?;
                    Ok(Stmt::ForTimes { times, body, pos })
                }
            }
            _ => {
                let times = self.parse_expr()?;
                let body = self.parse_maybe_typed_block()?;
                Ok(Stmt::ForTimes { times, body, pos })
            }
        }
    }

    fn parse_while_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        let cond = self.parse_expr()?;
        let body = self.parse_maybe_typed_block()?;
        Ok(Stmt::While { cond, body, pos })
    }

    fn parse_loop_stmt(&mut self) -> ParseResult<Stmt> {
        let pos = self.cur().pos; self.bump();
        let body = self.parse_maybe_typed_block()?;
        Ok(Stmt::Loop { body, pos })
    }

    fn parse_block(&mut self) -> ParseResult<Block> {
        self.skip_newlines();
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
        self.skip_newlines();
        if matches!(self.cur().kind, TokenKind::LBrace) {
            return Ok(Expr::Block(self.parse_block()?));
        }
        // Try typed block expression: TypeName '{' ... '}'
        if matches!(self.cur().kind, TokenKind::Ident(_)) {
            let save = self.idx;
            if let Ok(to) = self.parse_type() {
                self.skip_newlines();
                if matches!(self.cur().kind, TokenKind::LBrace) {
                    let pos = self.cur().pos;
                    let b = self.parse_block()?;
                    return Ok(Expr::Cast { expr: Box::new(Expr::Block(b)), to, pos });
                }
            }
            // rewind if not a typed block
            self.idx = save;
        }
        self.parse_expr()
    }

    fn parse_expr(&mut self) -> ParseResult<Expr> { self.parse_ternary() }

    fn parse_ternary(&mut self) -> ParseResult<Expr> {
        let cond = self.parse_nullish()?
        ;
        if matches!(self.cur().kind, TokenKind::Question) {
            let pos = if let Some(p) = Self::expr_pos_opt(&cond) { p } else { self.cur().pos };
            self.bump();
            let then_e = self.parse_expr_or_block()?;
            let else_e = if matches!(self.cur().kind, TokenKind::Colon) { self.bump(); Some(self.parse_expr_or_block()?) } else { None };
            Ok(Expr::IfElse { cond: Box::new(cond), then_e: Box::new(then_e), else_e: else_e.map(Box::new), pos })
        } else {
            // Implicit ternary: allow `cond <typed|untyped block> : <expr_or_block>`
            let pos = if let Some(p) = Self::expr_pos_opt(&cond) { p } else { self.cur().pos };
            let mut is_implicit_then = false;
            if matches!(self.cur().kind, TokenKind::LBrace) {
                is_implicit_then = true;
            } else if matches!(self.cur().kind, TokenKind::Ident(_)) {
                let save = self.idx;
                if let Ok(_) = self.parse_type() {
                    if matches!(self.cur().kind, TokenKind::LBrace) { is_implicit_then = true; }
                }
                self.idx = save;
            }
            if is_implicit_then {
                let save_then = self.idx;
                let then_e = self.parse_expr_or_block()?;
                if matches!(self.cur().kind, TokenKind::Colon) {
                    self.bump();
                    let else_e = Some(self.parse_expr_or_block()?);
                    Ok(Expr::IfElse { cond: Box::new(cond), then_e: Box::new(then_e), else_e: else_e.map(Box::new), pos })
                } else {
                    // no ':' -> rewind; then-block belongs to outer construct (e.g., for-times)
                    self.idx = save_then;
                    Ok(cond)
                }
            } else {
                Ok(cond)
            }
        }
    }

    fn parse_nullish(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_logical_or()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::QuestionQuestion) { break; }
            self.bump();
            let right = self.parse_logical_or()?;
            left = Expr::Binary { op: BinOp::NullishCoalesce, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_logical_or(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_logical_and()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::PipePipe) { break; }
            self.bump();
            let right = self.parse_logical_and()?;
            left = Expr::Binary { op: BinOp::LOr, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_logical_and(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_bit_or()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::AmpAmp) { break; }
            self.bump();
            let right = self.parse_bit_or()?;
            left = Expr::Binary { op: BinOp::LAnd, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_bit_or(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_bit_xor()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::Pipe) { break; }
            self.bump();
            let right = self.parse_bit_xor()?;
            left = Expr::Binary { op: BinOp::BitOr, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_bit_xor(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_bit_and()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::Caret) { break; }
            self.bump();
            let right = self.parse_bit_and()?;
            left = Expr::Binary { op: BinOp::BitXor, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_bit_and(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_compare()?;
        loop {
            let pos = Self::expr_pos(&left);
            if !matches!(self.cur().kind, TokenKind::Amp) { break; }
            self.bump();
            let right = self.parse_compare()?;
            left = Expr::Binary { op: BinOp::BitAnd, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_compare(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_shift()?;
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
            let right = self.parse_shift()?;
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> ParseResult<Expr> {
        let mut left = self.parse_add_sub()?;
        loop {
            let pos = Self::expr_pos(&left);
            let op = match self.cur().kind { TokenKind::Shl => BinOp::Shl, TokenKind::Shr => BinOp::Shr, _ => break };
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
            let op = match self.cur().kind { TokenKind::Star => BinOp::Mul, TokenKind::Slash => BinOp::Div, TokenKind::Percent => BinOp::Mod, _ => break };
            self.bump();
            let right = self.parse_unary()?;
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right), pos };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> ParseResult<Expr> {
        match self.cur().kind {
            TokenKind::Minus => { let pos = self.cur().pos; self.bump(); let e = self.parse_unary()?; Ok(Expr::Unary { op: UnOp::Neg, expr: Box::new(e), pos }) }
            TokenKind::Not => { let pos = self.cur().pos; self.bump(); let e = self.parse_unary()?; Ok(Expr::Unary { op: UnOp::Not, expr: Box::new(e), pos }) }
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
                    // method calls or built-in conversions
                    let dot_pos = self.cur().pos; self.bump();
                    let name_pos = self.cur().pos;
                    let name = match &self.cur().kind { TokenKind::Ident(s) => s.clone(), _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "method or conversion name", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos }) };
                    self.bump();
                    if matches!(self.cur().kind, TokenKind::LParen) {
                        // parse argument list
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
                        // built-in zero-arg conversions remain as casts
                        if args.is_empty() {
                            let to = match name.as_str() {
                                "string" => Some(TypeName { base: BaseType::String, params: vec![] }),
                                "i32" => Some(TypeName { base: BaseType::I32, params: vec![] }),
                                "u32" => Some(TypeName { base: BaseType::U32, params: vec![] }),
                                "f32" => Some(TypeName { base: BaseType::F32, params: vec![] }),
                                _ => None,
                            };
                            if let Some(to) = to { expr = Expr::Cast { expr: Box::new(expr), to, pos: dot_pos }; continue; }
                        }
                        // desugar obj.method(a,b) -> method(obj, a, b)
                        let mut full_args = Vec::with_capacity(1 + args.len());
                        full_args.push(expr);
                        full_args.extend(args);
                        let callee = Expr::Ident(name, name_pos);
                        let pos_call = dot_pos;
                        expr = Expr::Call { callee: Box::new(callee), args: full_args, pos: pos_call };
                    } else {
                        // property access not supported
                        return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "( for method call", found: Self::kind_name(&self.cur().kind) }, pos: name_pos });
                    }
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

    fn peek_is_compound_assign(&self) -> bool {
        if !matches!(self.cur().kind, TokenKind::Ident(_)) { return false; }
        let i = self.idx + 1; if i >= self.tokens.len() { return false; }
        use TokenKind::*;
        matches!(self.tokens[i].kind,
            PlusEq | MinusEq | StarEq | SlashEq | PercentEq |
            AmpEq | PipeEq | CaretEq | ShlEq | ShrEq |
            AmpAmpEq | PipePipeEq | QuestionQuestionEq
        )
    }

    fn parse_assign_stmt(&mut self) -> ParseResult<Stmt> {
        let name = if let TokenKind::Ident(s) = &self.cur().kind { s.clone() } else { unreachable!() };
        let pos = self.cur().pos; self.bump();
        let op = self.parse_assign_op()?;
        let expr = self.parse_expr()?;
        Ok(Stmt::Assign { name, op, expr, pos })
    }

    fn parse_assign_op(&mut self) -> ParseResult<AssignOp> {
        use TokenKind::*;
        let op = match self.cur().kind {
            PlusEq => AssignOp::AddAssign,
            MinusEq => AssignOp::SubAssign,
            StarEq => AssignOp::MulAssign,
            SlashEq => AssignOp::DivAssign,
            PercentEq => AssignOp::ModAssign,
            AmpEq => AssignOp::BitAndAssign,
            PipeEq => AssignOp::BitOrAssign,
            CaretEq => AssignOp::BitXorAssign,
            ShlEq => AssignOp::ShlAssign,
            ShrEq => AssignOp::ShrAssign,
            AmpAmpEq => AssignOp::LAndAssign,
            PipePipeEq => AssignOp::LOrAssign,
            QuestionQuestionEq => AssignOp::NullishAssign,
            _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "assignment operator", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos })
        };
        self.bump();
        Ok(op)
    }

    fn parse_primary(&mut self) -> ParseResult<Expr> {
        // typed block as primary expression: TypeName '{' ... '}'
        if matches!(self.cur().kind, TokenKind::Ident(_)) {
            let save = self.idx;
            if let Ok(to) = self.parse_type() {
                if matches!(self.cur().kind, TokenKind::LBrace) {
                    let pos = self.cur().pos;
                    let b = self.parse_block()?;
                    return Ok(Expr::Cast { expr: Box::new(Expr::Block(b)), to, pos });
                }
            }
            self.idx = save;
        }
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

    // Parse a block, optionally preceded by a type name (e.g., `void { ... }`).
    // The type (if any) is ignored here because statements that accept blocks
    // do not carry type annotations. Typed blocks as expressions are handled
    // in `parse_expr_or_block`.
    fn parse_maybe_typed_block(&mut self) -> ParseResult<Block> {
        self.skip_newlines();
        if matches!(self.cur().kind, TokenKind::Ident(_)) {
            let save = self.idx;
            if let Ok(_to) = self.parse_type() {
                self.skip_newlines();
                if matches!(self.cur().kind, TokenKind::LBrace) {
                    return self.parse_block();
                }
            }
            // rewind if not actually a typed block prefix
            self.idx = save;
        }
        self.parse_block()
    }

    fn parse_type(&mut self) -> ParseResult<TypeName> {
        // Parse base identifier
        let ident = match &self.cur().kind { TokenKind::Ident(s) => s.clone(), _ => return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "type name", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos }) };
        self.bump();
        let base = match ident.as_str() {
            "u32" => BaseType::U32,
            "i32" => BaseType::I32,
            "f32" => BaseType::F32,
            "bool" => BaseType::Bool,
            "string" => BaseType::String,
            "unit" => BaseType::Unit,
            "void" => BaseType::Unit,
            "Option" => BaseType::Option,
            "Range" => BaseType::Range,
            "Vec" => BaseType::Vec,
            "Set" => BaseType::Set,
            "Map" => BaseType::Map,
            _ => BaseType::Unit,
        };
        let mut params: Vec<TypeName> = Vec::new();
        if matches!(self.cur().kind, TokenKind::Lt) {
            // Parse generic params: <T, U>
            self.bump(); // consume '<'
            if matches!(self.cur().kind, TokenKind::Gt) {
                return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "type parameter", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos });
            }
            loop {
                params.push(self.parse_type()?);
                if matches!(self.cur().kind, TokenKind::Comma) { self.bump(); continue; }
                break;
            }
            // expect '>'
            if !matches!(self.cur().kind, TokenKind::Gt) {
                return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: ">", found: Self::kind_name(&self.cur().kind) }, pos: self.cur().pos });
            }
            self.bump();
        }
        // Optional arity validation (soft check; parser returns and typechecker can enforce more)
        match base {
            BaseType::Option | BaseType::Range | BaseType::Vec | BaseType::Set => {
                if params.len() != 1 { return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "one type parameter", found: "different arity" }, pos: self.cur().pos }); }
            }
            BaseType::Map => {
                if params.len() != 2 { return Err(ParseError { kind: ParseErrorKind::UnexpectedToken { expected: "two type parameters", found: "different arity" }, pos: self.cur().pos }); }
            }
            _ => {}
        }
        Ok(TypeName { base, params })
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
