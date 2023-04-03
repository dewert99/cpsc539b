use crate::defs::{BaseType, Ident, Lit, Predicate, PrimOp, Type};
use crate::error_reporting::{infer_ty_to_ty, z3_ast_to_pred};
use crate::ty;
use crate::util::{
    do_revert, inc_dr, map_insert_dr, map_remove_dr, shift, DoRevert, SemiPersistent,
};
use ahash::AHashMap;
use std::fmt::Debug;
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
pub enum InferType<'a, 'ctx, S: AsRef<Subst<'a, 'ctx>> + AsMut<Subst<'a, 'ctx>> = Subst<'a, 'ctx>> {
    Subst(S, &'a Type),
    Selfify(ast::Dynamic<'ctx>, &'a BaseType),
    Fresh(u32),
}

pub type BInferType<'a, 'ctx, 'b> = InferType<'a, 'ctx, &'b mut Subst<'a, 'ctx>>;

impl<'a, 'ctx, S: AsRef<Subst<'a, 'ctx>> + AsMut<Subst<'a, 'ctx>>> InferType<'a, 'ctx, S> {
    pub(crate) fn reborrow(&mut self) -> BInferType<'a, 'ctx, '_> {
        match self {
            InferType::Subst(s, data) => BInferType::Subst(s.as_mut(), *data),
            InferType::Selfify(z3, bty) => BInferType::Selfify(z3.clone(), *bty),
            InferType::Fresh(id) => BInferType::Fresh(*id),
        }
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
    rsub: Option<&ast::Dynamic<'ctx>>,
) -> ast::Dynamic<'ctx> {
    let convert = |pred| convert_pred(subst, tcx, pred, rsub);
    let ctx = tcx.ctx();
    match pred {
        Predicate::Res => rsub.unwrap().clone(),
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

fn resolve_s<'a, 'ctx, S: AsRef<Subst<'a, 'ctx>> + AsMut<Subst<'a, 'ctx>>>(
    ty: &'a Type,
    subst: S,
    tcx: &TyCtx<'a, 'ctx>,
    id: &Ident,
    rsf: ast::Bool<'ctx>,
) -> (InferType<'a, 'ctx, S>, ast::Bool<'ctx>) {
    match ty {
        Type::Var(tid) => match subst.as_ref().ty.get(tid) {
            None => (InferType::Subst(subst, ty), rsf),
            Some(InstTy::Fresh(id)) => (InferType::Fresh(*id), rsf),
            Some(InstTy::Ty(ty)) => resolve_s(ty, subst, tcx, id, rsf),
        },
        Type::Refined(box (Type::Base(b_ty), r)) => {
            let z3_const = tcx.fresh_const(b_ty, id.as_str());
            let z3_pred = convert_pred(subst.as_ref(), tcx, r, Some(&z3_const))
                .as_bool()
                .unwrap();
            (InferType::Selfify(z3_const, b_ty), rsf & z3_pred)
        }
        Type::Refined(box (ty, r)) => {
            let z3_pred = convert_pred(subst.as_ref(), tcx, r, None)
                .as_bool()
                .unwrap();
            resolve_s(ty, subst, tcx, id, rsf & z3_pred)
        }
        Type::Base(b_ty) => {
            let z3_const = tcx.fresh_const(b_ty, id.as_str());
            (InferType::Selfify(z3_const, b_ty), rsf)
        }
        _ => (InferType::Subst(subst, ty), rsf),
    }
}

fn resolve<'a, 'ctx, S: AsRef<Subst<'a, 'ctx>> + AsMut<Subst<'a, 'ctx>>>(
    ty: InferType<'a, 'ctx, S>,
    tcx: &TyCtx<'a, 'ctx>,
    id: &Ident,
) -> (InferType<'a, 'ctx, S>, ast::Bool<'ctx>) {
    let z3_true = ast::Bool::from_bool(tcx.ctx(), true);
    let (mut res0, res1) = match ty {
        InferType::Subst(subst, ty) => resolve_s(ty, subst, tcx, id, z3_true),
        _ => (ty, z3_true),
    };
    vprintln!(
        tcx,
        "^~ resolved to {:?}, {:?}",
        (infer_ty_to_ty(res0.reborrow())),
        res1
    );
    (res0, res1)
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
            (Type::Refined(Box::new((
                Type::Base(BaseType::Int),
                z3_ast_to_pred(&assume.clone().into())
            ))))
        );
        self.do_and_revert((add_assumption_dr(assume), tab_dr()))
    }

    pub fn insert<'b>(
        &'b mut self,
        id: &'b Ident,
        mut ty: InferType<'a, 'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        vprintln!(self, "{id:?}: {:?}", (infer_ty_to_ty(ty.reborrow())));
        let (ty, z3_pred) = resolve(ty, self, id);
        self.do_and_revert((
            (tab_dr(), add_assumption_dr(z3_pred)),
            shift(map_insert_dr(id.clone(), ty), TyCtxBase::tenv),
        ))
    }

    pub fn insert_dummy<'b, 'c>(
        &'b mut self,
        id: &Ident,
        mut ty: BInferType<'a, 'ctx, 'c>,
    ) -> (
        BInferType<'a, 'ctx, 'c>,
        impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b,
    ) {
        vprintln!(self, "{id:?}: {:?}", (infer_ty_to_ty(ty.reborrow())));
        let (ty, z3_pred) = resolve(ty, self, id);
        (
            ty,
            self.do_and_revert((tab_dr(), add_assumption_dr(z3_pred))),
        )
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

    pub fn check_pred(
        &self,
        subst: &Subst<'_, 'ctx>,
        pred: &Predicate,
        rsub: Option<&ast::Dynamic<'ctx>>,
    ) -> Result<(), Model<'ctx>> {
        let pred = convert_pred(subst, self, pred, rsub).as_bool().unwrap();
        self.check(pred)
    }
}

pub type PreTenv = AHashMap<Ident, Type>;

pub fn base_tenv() -> PreTenv {
    AHashMap::from([
        ("add".into(), ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (+ "x" "y"))))))),
        ("sub".into(), ty!((-> "x" (: int #t) (fun "y" (: int #t) (: int (= res (sub "x" "y"))))))),
        ("le".into(), ty!((-> "x" (: int #t) (fun "y" (: int #t) (: bool (= res (<= "x" "y"))))))),
        ("eq".into(),  ty!((-> "x" (: int #t) (fun "y" (: int #t) (: bool (= res (= "x" "y"))))))),
        ("assert".into(), ty!((-> "x" (: bool res) (: bool res)))),
    ])
}

pub fn make_context() -> Context {
    let mut config = Config::new();
    config.set_param_value("trace", "true");
    Context::new(&config)
}

pub fn make_tcx<'a, 'ctx>(context: &'ctx Context, tenv: &'a PreTenv, verbose: bool) -> TyCtx<'a, 'ctx> {
    let solver = Solver::new(&context);
    let tenv = tenv.iter().map(|(k, v)| (k.clone(), v.into())).collect();
    TyCtx::new(TyCtxBase {
        solver,
        tenv,
        tpenv: AHashMap::default(),
        fresh_count: 0,
        tab_count: 0,
        verbose,
    })
}
