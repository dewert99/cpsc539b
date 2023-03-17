use crate::defs::{BaseType, Ident, Lit, Predicate, PrimOp, Type};
use crate::ty;
use crate::util::SemiPersistent;
use crate::util::{Either, SPHashMap};
use ahash::AHashMap;
use std::ops::{Add, BitAnd, BitOr, DerefMut, Sub};
use lazy_static::lazy_static;
use z3::ast::Ast;
use z3::{ast, Config, Context, Model, SatResult, Solver};

pub type Tenv<'a, 'ctx> = AHashMap<Ident, InferType<'a, 'ctx>>;

pub struct TyCtxBase<'a, 'ctx> {
    pub tenv: AHashMap<Ident, InferType<'a, 'ctx>>,
    pub solver: Solver<'ctx>,
}

pub type TyCtx<'a, 'ctx> = SemiPersistent<TyCtxBase<'a, 'ctx>>;

pub type Subst<'ctx> = SPHashMap<Ident, ast::Dynamic<'ctx>>;

#[derive(Clone, Debug)]
pub enum InferType<'a, 'ctx> {
    Subst(Subst<'ctx>, &'a Type),
    Selfify(ast::Dynamic<'ctx>, &'a BaseType),
}

fn fresh_const<'ctx>(ctx: &'ctx Context, ty: &BaseType, prefix: &str) -> ast::Dynamic<'ctx> {
    match ty {
        BaseType::Int => ast::Int::fresh_const(ctx, prefix).into(),
    }
}

pub fn convert_pred<'ctx>(
    subst: &Subst<'ctx>,
    tcx: &TyCtx<'_, 'ctx>,
    pred: &Predicate,
    rsub: &ast::Dynamic<'ctx>,
) -> ast::Dynamic<'ctx> {
    let convert = |pred| convert_pred(subst, tcx, pred, rsub);
    let ctx = tcx.ctx();
    match pred {
        Predicate::Res => rsub.clone(),
        Predicate::Var(x) => subst
            .get(x)
            .cloned()
            .unwrap_or_else(|| match tcx.tenv.get(x) {
                Some(InferType::Selfify(x, _)) => x.clone(),
                _ => unreachable!(),
            }),
        Predicate::Lit(Lit::Bool(b)) => ast::Bool::from_bool(ctx, *b).into(),
        Predicate::Lit(Lit::Int(n)) => ast::Int::from_i64(ctx, *n as i64).into(),
        Predicate::Op(box (op, a0, a1)) => {
            let [a0, a1] = [convert(a0), convert(a1)];
            match op {
                PrimOp::Add => a0.as_int().unwrap().add(&a1.as_int().unwrap()).into(),
                PrimOp::Sub => a0.as_int().unwrap().sub(&a1.as_int().unwrap()).into(),
                PrimOp::Le => a0.as_int().unwrap().le(&a1.as_int().unwrap()).into(),
                PrimOp::Eq => a0._eq(&a1).into(),
                PrimOp::And => a0.as_bool().unwrap().bitand(&a1.as_bool().unwrap()).into(),
                PrimOp::Or => a0.as_bool().unwrap().bitor(&a1.as_bool().unwrap()).into(),
            }
        }
        Predicate::Not(box [x]) => convert(x).as_bool().unwrap().not().into(),
        Predicate::If(box [i, t, e]) => {
            let [i, t, e] = [convert(i), convert(t), convert(e)];
            i.as_bool().unwrap().ite(&t, &e)
        }
    }
}

impl<'a, 'ctx> TyCtx<'a, 'ctx> {
    pub fn ctx(&self) -> &'ctx Context {
        self.solver.get_context()
    }

    pub fn fresh_const(&self, ty: &BaseType, prefix: &str) -> ast::Dynamic<'ctx> {
        match ty {
            BaseType::Int => ast::Int::fresh_const(self.ctx(), prefix).into(),
        }
    }

    pub fn add_assumption<'b>(
        &'b mut self,
        assume: &'b ast::Bool<'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        self.do_and_revert(
            |data| {
                data.solver.push();
                data.solver.assert(assume);
            },
            |_, data| data.solver.pop(1),
        )
    }

    pub fn insert_sp<'b>(
        &'b mut self,
        id: &'b Ident,
        ty: InferType<'a, 'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        match ty {
            InferType::Subst(subst, Type::Refined(b_ty, box r)) => {
                let z3_const = fresh_const(self.ctx(), b_ty, id.as_str());
                let z3_pred = convert_pred(&subst, self, r, &z3_const).as_bool().unwrap();
                Either::L(self.do_and_revert(
                    move |data| {
                        println!("(push)");
                        data.solver.push();
                        println!("(assert {z3_pred})");
                        data.solver.assert(&z3_pred);
                        data.tenv
                            .insert(id.clone(), InferType::Selfify(z3_const, b_ty))
                    },
                    |last_val, data| {
                        match last_val.take() {
                            None => data.tenv.remove(id),
                            Some(val) => data.tenv.insert(id.clone(), val),
                        };
                        println!("(pop)");
                        data.solver.pop(1);
                    },
                ))
            }
            ty => Either::R(self.do_and_revert(
                |data| data.tenv.insert(id.clone(), ty),
                |last_val, data| {
                    match last_val.take() {
                        None => data.tenv.remove(id),
                        Some(val) => data.tenv.insert(id.clone(), val),
                    };
                },
            )),
        }
    }

    pub fn check(&self, assertion: ast::Bool<'ctx>) -> Result<(), Model<'ctx>> {
        println!("(check {assertion})");
        let assertions = &[!assertion];
        match self.solver.check_assumptions(assertions) {
            SatResult::Unsat => Ok(()),
            _ => Err(self.solver.get_model().unwrap()),
        }
    }
}

lazy_static!{
    static ref ADD_TY: Type = ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (+ "x" "y"))))));
    static ref SUB_TY: Type = ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (sub "x" "y"))))));
}

pub fn make_tenv() -> Tenv<'static, 'static> {
    AHashMap::from([
        ("add".into(), InferType::Subst(Subst::default(), &*ADD_TY)),
        ("sub".into(), InferType::Subst(Subst::default(), &*SUB_TY)),
    ])
}

pub fn make_context() -> Context {
    let mut config = Config::new();
    config.set_param_value("trace", "true");
    Context::new(&config)
}

pub fn make_tcx<'ctx>(context: &'ctx Context) -> TyCtx<'static, 'ctx> {
    let solver = Solver::new(&context);
    let tenv = make_tenv();
    TyCtx::new(TyCtxBase { solver, tenv })
}

