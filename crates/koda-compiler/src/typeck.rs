use std::collections::HashMap;

use crate::ast::*;
use crate::token::Position;
use crate::types::{Type, BaseType, TypeName};

#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: String,
    pub pos: Position,
}

pub type TypeResult<T> = Result<T, TypeError>;

#[derive(Default)]
struct Subst { // simple substitution for type variables
    map: HashMap<u32, Type>,
}

impl Subst {
    fn apply(&mut self, t: &Type) -> Type {
        match t {
            Type::Var(id) => {
                if let Some(tt) = self.map.get(id).cloned() { self.apply(&tt) } else { t.clone() }
            }
            Type::Option(inner) => Type::Option(Box::new(self.apply(inner))),
            Type::Range(inner) => Type::Range(Box::new(self.apply(inner))),
            Type::Func(ps, r) => Type::Func(ps.iter().map(|p| self.apply(p)).collect(), Box::new(self.apply(r))),
            _ => t.clone(),
        }
    }

    fn bind(&mut self, id: u32, t: Type) {
        self.map.insert(id, t);
    }
}

#[derive(Default)]
pub struct Tc {
    env: Vec<HashMap<String, Type>>, // lexical scopes
    next_tv: u32,
    subst: Subst,
    types: HashMap<Position, Type>, // annotated types per expression position
}

impl Tc {
    fn expr_pos(e: &Expr) -> Position {
        match e {
            Expr::Int(_, p)
            | Expr::Bool(_, p)
            | Expr::String(_, p)
            | Expr::NoneLit(p)
            | Expr::Ident(_, p)
            | Expr::Binary { pos: p, .. }
            | Expr::Unary { pos: p, .. }
            | Expr::Call { pos: p, .. }
            | Expr::Range { pos: p, .. }
            | Expr::IfElse { pos: p, .. }
            | Expr::FnLit { pos: p, .. }
            | Expr::Cast { pos: p, .. } => *p,
            Expr::Block(b) => b.pos,
        }
    }
    pub fn new() -> Self {
        let mut this = Self { env: vec![HashMap::new()], next_tv: 0, subst: Subst::default(), types: HashMap::new() };
        this.install_builtins();
        this
    }

    fn tv(&mut self) -> Type { let id = self.next_tv; self.next_tv += 1; Type::Var(id) }

    fn enter(&mut self) { self.env.push(HashMap::new()); }
    fn exit(&mut self) { self.env.pop(); }

    fn insert(&mut self, name: String, ty: Type) { if let Some(scope) = self.env.last_mut() { scope.insert(name, ty); } }

    fn lookup(&mut self, name: &str) -> Option<Type> {
        if name == "print" {
            // Always return a fresh instantiation: (T) -> Unit
            return Some(Type::Func(vec![self.tv()], Box::new(Type::Unit)));
        }
        for scope in self.env.iter().rev() {
            if let Some(t) = scope.get(name) { return Some(self.subst.apply(t)); }
        }
        None
    }

    fn install_builtins(&mut self) {
        // print: (T) -> Unit (monomorphic instantiation per reference via fresh type var)
        let t = self.tv();
        let func = Type::Func(vec![t], Box::new(Type::Unit));
        self.insert("print".into(), func);
    }

    fn from_typename(tn: &TypeName) -> Type {
        match tn.base {
            BaseType::U32 => Type::U32,
            BaseType::I32 => Type::I32,
            BaseType::F32 => Type::F32,
            BaseType::Bool => Type::Bool,
            BaseType::String => Type::String,
            BaseType::Unit => Type::Unit,
            BaseType::Option => {
                let inner = tn.params.get(0).map(Self::from_typename).unwrap_or(Type::Unit);
                Type::Option(Box::new(inner))
            }
            BaseType::Range => {
                let inner = tn.params.get(0).map(Self::from_typename).unwrap_or(Type::U32);
                Type::Range(Box::new(inner))
            }
        }
    }

    fn unify_numeric(&mut self, a: &Type, b: &Type) -> TypeResult<Type> {
        use Type::*;
        let aa = self.subst.apply(a);
        let bb = self.subst.apply(b);
        match (aa, bb) {
            (U32, U32) => Ok(Type::U32),
            (I32, I32) => Ok(Type::I32),
            (F32, F32) => Ok(Type::F32),
            (IntLit, U32) | (U32, IntLit) => Ok(Type::U32),
            (IntLit, I32) | (I32, IntLit) => Ok(Type::I32),
            (IntLit, IntLit) => Ok(Type::U32), // default integer
            (Var(id), t) | (t, Var(id)) => { self.subst.bind(id, t.clone()); Ok(t) }
            (l, r) => Err(TypeError { message: format!("numeric type mismatch: {:?} vs {:?}", l, r), pos: Position { index: 0, line: 0, column: 0 } })
        }
    }

    fn unify(&mut self, a: &Type, b: &Type) -> TypeResult<Type> {
        use Type::*;
        let aa = self.subst.apply(a);
        let bb = self.subst.apply(b);
        match (aa, bb) {
            (x, y) if x == y => Ok(x),
            (Var(id), t) | (t, Var(id)) => { self.subst.bind(id, t.clone()); Ok(t) }
            (Option(a), Option(b)) => { let u = self.unify(&a, &b)?; Ok(Option(Box::new(u))) }
            (Range(a), Range(b)) => { let u = self.unify_numeric(&a, &b)?; Ok(Range(Box::new(u))) }
            (Func(a_ps, a_r), Func(b_ps, b_r)) => {
                if a_ps.len() != b_ps.len() { return Err(TypeError { message: "function arity mismatch".into(), pos: Position { index: 0, line: 0, column: 0 } }); }
                let mut ps: Vec<Type> = Vec::with_capacity(a_ps.len());
                for (ap, bp) in a_ps.iter().zip(b_ps.iter()) { ps.push(self.unify(ap, bp)?); }
                let r = self.unify(&a_r, &b_r)?;
                Ok(Func(ps, Box::new(r)))
            }
            (IntLit, t @ U32) | (U32, t @ IntLit) => Ok(t),
            (IntLit, t @ I32) | (I32, t @ IntLit) => Ok(t),
            (IntLit, IntLit) => Ok(U32),
            (a, b) => Err(TypeError { message: format!("type mismatch: {:?} vs {:?}", a, b), pos: Position { index: 0, line: 0, column: 0 } }),
        }
    }

    fn cast_allowed(&mut self, from: &Type, to: &Type) -> bool {
        use Type::*;
        let f = self.subst.apply(from);
        let t = self.subst.apply(to);
        match (f, t) {
            // Identity
            (a, b) if a == b => true,
            // Int literal can be cast to concrete numeric
            (IntLit, U32) | (IntLit, I32) | (IntLit, F32) => true,
            // Numeric to numeric (explicit only, no implicit)
            (U32, U32) | (U32, I32) | (U32, F32)
            | (I32, U32) | (I32, I32) | (I32, F32)
            | (F32, U32) | (F32, I32) | (F32, F32) => true,
            // Bool to numeric/string
            (Bool, U32) | (Bool, I32) | (Bool, F32) | (Bool, String) => true,
            // Any to string via .string() or as string
            (IntLit, String) | (U32, String) | (I32, String) | (F32, String) | (String, String) => true,
            // Disallow other forms (Option, Range, Func, etc.)
            _ => false,
        }
    }

    fn unify_at(&mut self, a: &Type, b: &Type, pos: Position) -> TypeResult<Type> {
        match self.unify(a, b) {
            Ok(t) => Ok(t),
            Err(e) => Err(TypeError { message: e.message, pos })
        }
    }

    fn unify_numeric_at(&mut self, a: &Type, b: &Type, pos: Position) -> TypeResult<Type> {
        match self.unify_numeric(a, b) {
            Ok(t) => Ok(t),
            Err(e) => Err(TypeError { message: e.message, pos })
        }
    }

    pub fn check_program(&mut self, p: &Program) -> TypeResult<()> {
        for s in &p.stmts { self.check_stmt(s)?; }
        Ok(())
    }

    fn check_block(&mut self, b: &Block, ret_expected: Option<Type>) -> TypeResult<Type> {
        self.enter();
        let mut last_ty = Type::Unit;
        for (_idx, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Return(eopt, _) => {
                    let t = if let Some(e) = eopt { self.check_expr(e, ret_expected.clone())? } else { Type::Unit };
                    if let Some(exp) = &ret_expected { self.unify_at(&t, exp, b.pos)?; }
                    last_ty = Type::Unit; // after return, type is irrelevant
                }
                _ => {
                    self.check_stmt(s)?;
                    if let Stmt::ExprStmt(e, _) = s { last_ty = self.check_expr(e, ret_expected.clone())?; }
                }
            }
        }
        self.exit();
        Ok(last_ty)
    }

    fn check_stmt(&mut self, s: &Stmt) -> TypeResult<()> {
        match s {
            Stmt::Let { name, ty, value, pos } => {
                let vty = self.check_expr(value, None)?;
                let final_ty = if let Some(tn) = ty { let annotated = Self::from_typename(tn); self.unify_at(&vty, &annotated, *pos)? } else { vty };
                self.insert(name.clone(), final_ty);
                Ok(())
            }
            Stmt::ExprStmt(e, _) => { let _ = self.check_expr(e, None)?; Ok(()) }
            Stmt::ForIn { name, iter, body, .. } => {
                let ity = self.check_expr(iter, None)?;
                if let Type::Range(inner) = self.subst.apply(&ity) {
                    self.enter();
                    self.insert(name.clone(), *inner.clone());
                    let _ = self.check_block(body, None)?;
                    self.exit();
                    Ok(())
                } else {
                    Err(TypeError { message: format!("for-in expects Range<T>, got {:?}", ity), pos: body.pos })
                }
            }
            Stmt::ForTimes { times, body, pos: _ } => {
                let t = self.check_expr(times, None)?;
                let _ = self.unify_numeric_at(&t, &Type::U32, body.pos)?; // accept numeric; default u32
                let _ = self.check_block(body, None)?;
                Ok(())
            }
            Stmt::While { cond, body, .. } => { let t = self.check_expr(cond, None)?; self.unify_at(&t, &Type::Bool, body.pos)?; let _ = self.check_block(body, None)?; Ok(()) }
            Stmt::Loop { body, .. } => { let _ = self.check_block(body, None)?; Ok(()) }
            Stmt::Break(_) | Stmt::Continue(_) => Ok(()),
            Stmt::Return(_, _) => Ok(()) // handled in block
        }
    }

    fn check_call(&mut self, callee: &Expr, args: &[Expr], pos: Position) -> TypeResult<Type> {
        let cty = self.check_expr(callee, None)?;
        match self.subst.apply(&cty) {
            Type::Func(params, ret) => {
                if params.len() != args.len() { return Err(TypeError { message: format!("arity mismatch: expected {}, got {}", params.len(), args.len()), pos }); }
                for (p, a) in params.iter().zip(args.iter()) { let at = self.check_expr(a, None)?; let _ = self.unify_at(p, &at, pos)?; }
                Ok(*ret)
            }
            other => Err(TypeError { message: format!("not callable: {:?}", other), pos })
        }
    }

    fn check_expr(&mut self, e: &Expr, ret_expected: Option<Type>) -> TypeResult<Type> {
        use Expr::*;
        let pos = Self::expr_pos(e);
        let ty: Type = match e {
            Int(_, _) => Ok(Type::IntLit),
            Bool(_, _) => Ok(Type::Bool),
            String(_, _) => Ok(Type::String),
            NoneLit(_) => Ok(Type::Option(Box::new(Type::Unit))),
            Ident(name, _) => self.lookup(name).ok_or(TypeError { message: format!("unbound identifier: {}", name), pos: Position { index: 0, line: 0, column: 0 } }),
            Unary { op, expr, .. } => {
                let t = self.check_expr(expr, ret_expected)?;
                match op {
                    UnOp::Neg => self.unify_numeric(&t, &t), // allow any numeric type
                    UnOp::Not => { self.unify(&t, &Type::Bool)?; Ok(Type::Bool) }
                }
            }
            Binary { op, left, right, .. } => {
                let lt = self.check_expr(left, ret_expected.clone())?;
                let rt = self.check_expr(right, ret_expected)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                        let t = self.unify_numeric_at(&lt, &rt, Self::expr_pos(left))?; Ok(t)
                    }
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        // comparisons on numeric for now
                        let _ = self.unify_numeric_at(&lt, &rt, Self::expr_pos(left))?; Ok(Type::Bool)
                    }
                }
            }
            Call { callee, args, pos } => self.check_call(callee, args, *pos),
            Range { start, end, .. } => {
                let st = self.check_expr(start, ret_expected.clone())?;
                let en = self.check_expr(end, ret_expected)?;
                let t = self.unify_numeric_at(&st, &en, Self::expr_pos(start))?;
                Ok(Type::Range(Box::new(t)))
            }
            Block(b) => self.check_block(b, ret_expected),
            IfElse { cond, then_e, else_e, .. } => {
                let ct = self.check_expr(cond, ret_expected.clone())?; self.unify_at(&ct, &Type::Bool, Self::expr_pos(cond))?;
                let tt = self.check_expr(then_e, ret_expected.clone())?;
                if let Some(else_e) = else_e { let et = self.check_expr(else_e, ret_expected)?; self.unify_at(&tt, &et, Self::expr_pos(then_e)) } else { Ok(Type::Option(Box::new(tt))) }
            }
            FnLit { params, ret, body, .. } => {
                // param types
                let mut pts: Vec<Type> = Vec::new();
                self.enter();
                for p in params {
                    let pt = if let Some(tn) = &p.ty { Self::from_typename(tn) } else { self.tv() };
                    self.insert(p.name.clone(), pt.clone());
                    pts.push(pt);
                }
                let ret_t_annot = ret.as_ref().map(Self::from_typename);
                let body_t = self.check_block(body, ret_t_annot.clone())?;
                let ret_t = if let Some(r) = ret_t_annot { self.unify_at(&body_t, &r, body.pos)? } else { body_t };
                self.exit();
                Ok(Type::Func(pts, Box::new(ret_t)))
            }
            Cast { expr, to, pos } => {
                let src_t = self.check_expr(expr, None)?;
                let dst_t = Self::from_typename(to);
                if self.cast_allowed(&src_t, &dst_t) { Ok(dst_t) } else { Err(TypeError { message: format!("invalid cast from {:?} to {:?}", src_t, dst_t), pos: *pos }) }
            }
        }?;
        // Record the inferred type for this expression position
        self.types.insert(pos, self.subst.apply(&ty));
        Ok(ty)
    }
}

pub fn typecheck(program: &Program) -> TypeResult<()> {
    let mut tc = Tc::new();
    tc.check_program(program)
}

pub fn type_annotations(program: &Program) -> TypeResult<HashMap<Position, Type>> {
    let mut tc = Tc::new();
    tc.check_program(program)?;
    Ok(tc.types)
}
