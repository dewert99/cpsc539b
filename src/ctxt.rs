use crate::defs::{BaseType, Ident, Lit, Predicate, PrimOp, Type};
use crate::error_reporting::{infer_ty_to_ty, z3_ast_to_pred};
use crate::ty;
use crate::util::Either;
use crate::util::{
    do_revert, inc_dr, map_insert_dr, map_remove_dr, shift, DoRevert, SemiPersistent,
};
use ahash::AHashMap;
use lazy_static::lazy_static;
use std::fmt::{Debug, Formatter};
use std::ops::{Add, BitAnd, BitOr, DerefMut, Sub};
use z3::ast::Ast;
use z3::{ast, Config, Context, Model, SatResult, Solver};

pub type Tenv<'a, 'ctx> = AHashMap<Ident, InferType<'a, 'ctx>>;
pub type TPenv = AHashMap<Ident, ()>;

pub struct TyCtxBase<'a, 'ctx> {
    pub tenv: AHashMap<Ident, InferType<'a, 'ctx>>,
    pub tpenv: TPenv,
    pub fresh_count: u32,
    pub solver: Solver<'ctx>,
    pub verbose: bool,
    pub tab_count: u32,
}

impl<'a, 'ctx> TyCtxBase<'a, 'ctx> {
    fn push(&mut self) {
        self.solver.push();
    }

    fn pop(&mut self) {
        self.solver.pop(1);
    }

    fn assert(&mut self, b: &ast::Bool) {
        self.solver.assert(b)
    }

    fn tenv(&mut self) -> &mut Tenv<'a, 'ctx> {
        &mut self.tenv
    }

    fn tpenv(&mut self) -> &mut TPenv {
        &mut self.tpenv
    }

    fn tpcount(&mut self) -> &mut u32 {
        &mut self.fresh_count
    }
}

pub type TyCtx<'a, 'ctx> = SemiPersistent<TyCtxBase<'a, 'ctx>>;

#[derive(Copy, Clone, Debug)]
pub enum InstTy<'a> {
    Fresh(u32),
    Ty(&'a Type),
}

#[derive(Clone, Debug)]
pub struct SubstBase<'a, 'ctx> {
    pub val: AHashMap<Ident, ast::Dynamic<'ctx>>,
    pub ty: AHashMap<Ident, InstTy<'a>>,
}

pub type Subst<'a, 'ctx> = SemiPersistent<SubstBase<'a, 'ctx>>;

impl<'a, 'ctx> SubstBase<'a, 'ctx> {
    fn val(&mut self) -> &mut AHashMap<Ident, ast::Dynamic<'ctx>> {
        &mut self.val
    }

    fn ty(&mut self) -> &mut AHashMap<Ident, InstTy<'a>> {
        &mut self.ty
    }
}

#[derive(Clone)]
pub enum InferType<'a, 'ctx> {
    Subst(Subst<'a, 'ctx>, &'a Type),
    Selfify(ast::Dynamic<'ctx>, &'a BaseType),
}

impl<'a, 'ctx> Debug for InferType<'a, 'ctx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let ty = infer_ty_to_ty(&mut self.clone());
        Debug::fmt(&ty, f)
    }
}

pub fn empty_subst<'a, 'ctx>() -> Subst<'a, 'ctx> {
    Subst::new(SubstBase {
        ty: AHashMap::default(),
        val: AHashMap::default(),
    })
}

impl<'a, 'ctx> Subst<'a, 'ctx> {
    pub fn insert_v(
        &mut self,
        id: Ident,
        val: ast::Dynamic<'ctx>,
    ) -> impl DerefMut<Target = Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_insert_dr(id, val), SubstBase::val))
    }

    pub fn remove_v(&mut self, id: Ident) -> impl DerefMut<Target = Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_remove_dr(id), SubstBase::val))
    }

    pub fn insert_tp(
        &mut self,
        id: Ident,
        val: InstTy<'a>,
    ) -> impl DerefMut<Target = Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_insert_dr(id, val), SubstBase::ty))
    }

    pub fn remove_tp(&mut self, id: Ident) -> impl DerefMut<Target = Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_remove_dr(id), SubstBase::ty))
    }
}

impl<'a, 'ctx> From<&'a Type> for InferType<'a, 'ctx> {
    fn from(ty: &'a Type) -> Self {
        let base = SubstBase {
            ty: Default::default(),
            val: Default::default(),
        };
        InferType::Subst(Subst::new(base), ty)
    }
}

pub fn convert_pred<'ctx>(
    subst: &Subst<'_, 'ctx>,
    tcx: &TyCtx<'_, 'ctx>,
    pred: &Predicate,
    rsub: &ast::Dynamic<'ctx>,
) -> ast::Dynamic<'ctx> {
    let convert = |pred| convert_pred(subst, tcx, pred, rsub);
    let ctx = tcx.ctx();
    match pred {
        Predicate::Res => rsub.clone(),
        Predicate::Var(x) => subst
            .val
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

fn add_assumption_dr<'a, 'ctx>(assume: ast::Bool<'ctx>) -> impl DoRevert<TyCtxBase<'a, 'ctx>> {
    do_revert(move |base: &mut TyCtxBase<'a, 'ctx>| {
        base.push();
        base.assert(&assume);
        |base: &mut TyCtxBase<'a, 'ctx>| base.pop()
    })
}

fn tab_dr<'a, 'ctx>() -> impl DoRevert<TyCtxBase<'a, 'ctx>> {
    fn tab<'a, 'ctx, 'b>(x: &'b mut TyCtxBase<'a, 'ctx>) -> &'b mut u32 {
        &mut x.tab_count
    }
    shift(inc_dr(), tab)
}

macro_rules! vprintln {
    ($tcx:expr, $($ts:tt),*) => {
        if $tcx.verbose {
            eprint!("{:indent$}", "", indent = ($tcx.tab_count*2) as usize);
            eprintln!($($ts,)*)
        }
    };
}

pub(crate) use vprintln;

impl<'a, 'ctx> TyCtx<'a, 'ctx> {
    pub fn ctx(&self) -> &'ctx Context {
        self.solver.get_context()
    }

    pub fn fresh_const(&self, ty: &BaseType, prefix: &str) -> ast::Dynamic<'ctx> {
        match ty {
            BaseType::Int => ast::Int::fresh_const(self.ctx(), prefix).into(),
            BaseType::Bool => ast::Bool::fresh_const(self.ctx(), prefix).into(),
        }
    }

    pub fn add_assumption<'b>(
        &'b mut self,
        assume: ast::Bool<'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        vprintln!(
            self,
            "_: {:?}",
            (Type::Refined(
                BaseType::Int,
                Box::new(z3_ast_to_pred(&assume.clone().into()))
            ))
        );
        self.do_and_revert((add_assumption_dr(assume), tab_dr()))
    }

    pub fn insert<'b>(
        &'b mut self,
        id: &'b Ident,
        ty: InferType<'a, 'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        vprintln!(self, "{id:?}: {ty:?}");
        match ty {
            InferType::Subst(subst, Type::Refined(b_ty, box r)) => {
                let z3_const = self.fresh_const(b_ty, id.as_str());
                let z3_pred = convert_pred(&subst, self, r, &z3_const).as_bool().unwrap();
                Either::L(self.do_and_revert((
                    (tab_dr(), add_assumption_dr(z3_pred)),
                    shift(
                        map_insert_dr(id.clone(), InferType::Selfify(z3_const, b_ty)),
                        TyCtxBase::tenv,
                    ),
                )))
            }
            ty => Either::R(self.do_and_revert((
                tab_dr(),
                shift(map_insert_dr(id.clone(), ty), TyCtxBase::tenv),
            ))),
        }
    }

    pub fn insert_tp<'b>(
        &'b mut self,
        id: &'b Ident,
    ) -> Result<impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b, ()> {
        if self.tpenv.contains_key(id) {
            return Err(());
        }
        vprintln!(self, "{id:?}: Type");
        Ok(self.do_and_revert((
            tab_dr(),
            shift(map_insert_dr(id.clone(), ()), TyCtxBase::tpenv),
        )))
    }

    pub fn fresh_ty<'b>(
        &'b mut self,
    ) -> (
        InstTy<'static>,
        impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b,
    ) {
        let x = InstTy::Fresh(self.fresh_count);
        vprintln!(self, "$T{}: Type", (self.fresh_count));
        (
            x,
            self.do_and_revert((tab_dr(), shift(inc_dr(), TyCtxBase::tpcount))),
        )
    }

    pub fn check(&self, assertion: ast::Bool<'ctx>) -> Result<(), Model<'ctx>> {
        vprintln!(self, "checking {assertion:?}");
        let assertions = &[!assertion];
        match self.solver.check_assumptions(assertions) {
            SatResult::Unsat => Ok(()),
            _ => Err(self.solver.get_model().unwrap()),
        }
    }
}

lazy_static! {
    static ref ADD_TY: Type =
        ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (+ "x" "y"))))));
    static ref SUB_TY: Type =
        ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (sub "x" "y"))))));
    static ref LE_TY: Type =
        ty!((-> "x" (: int #t) (fun "y" (: int #t) (: bool (= res (<= "x" "y"))))));
    static ref EQ_TY: Type =
        ty!((-> "x" (: int #t) (fun "y" (: int #t) (: bool (= res (= "x" "y"))))));
    static ref ASSERT_TY: Type = ty!((-> "x" (: bool res) (: bool res)));
}

pub fn make_tenv() -> Tenv<'static, 'static> {
    AHashMap::from([
        ("add".into(), (&*ADD_TY).into()),
        ("sub".into(), (&*SUB_TY).into()),
        ("le".into(), (&*LE_TY).into()),
        ("eq".into(), (&*EQ_TY).into()),
        ("assert".into(), (&*ASSERT_TY).into()),
    ])
}

pub fn make_context() -> Context {
    let mut config = Config::new();
    config.set_param_value("trace", "true");
    Context::new(&config)
}

pub fn make_tcx<'ctx>(context: &'ctx Context, verbose: bool) -> TyCtx<'static, 'ctx> {
    let solver = Solver::new(&context);
    let tenv = make_tenv();
    TyCtx::new(TyCtxBase {
        solver,
        tenv,
        tpenv: AHashMap::default(),
        fresh_count: 0,
        tab_count: 0,
        verbose,
    })
}
