use crate::token::Position;
use crate::types::TypeName;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let { name: String, ty: Option<TypeName>, value: Expr, pos: Position },
    ExprStmt(Expr, Position),
    ForIn { name: String, iter: Expr, body: Block, pos: Position },
    ForTimes { times: Expr, body: Block, pos: Position },
    While { cond: Expr, body: Block, pos: Position },
    Loop { body: Block, pos: Position },
    Break(Position),
    Continue(Position),
    Return(Option<Expr>, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub pos: Position,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Int(u64, Position),
    Bool(bool, Position),
    String(String, Position),
    NoneLit(Position),
    Ident(String, Position),
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr>, pos: Position },
    Unary { op: UnOp, expr: Box<Expr>, pos: Position },
    Call { callee: Box<Expr>, args: Vec<Expr>, pos: Position },
    Range { start: Box<Expr>, end: Box<Expr>, pos: Position },
    Block(Block),
    IfElse { cond: Box<Expr>, then_e: Box<Expr>, else_e: Option<Box<Expr>>, pos: Position },
    FnLit { params: Vec<Param>, ret: Option<TypeName>, body: Block, pos: Position },
    Cast { expr: Box<Expr>, to: TypeName, pos: Position },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeName>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp { Add, Sub, Mul, Div, Eq, Ne, Lt, Le, Gt, Ge }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp { Neg, Not }
