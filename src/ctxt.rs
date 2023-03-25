use std::marker::PhantomData;
use crate::defs::{BaseType, Ident, Lit, Predicate, PrimOp, Type};
use crate::ty;
use crate::util::{do_revert, inc_dr, map_insert_dr, shift, DoRevert, SemiPersistent, map_remove_dr};
use crate::util::{Either};
use ahash::AHashMap;
use lazy_static::lazy_static;
use std::ops::{Add, BitAnd, BitOr, DerefMut, Sub};
use z3::ast::Ast;
use z3::{ast, Config, Context, Model, SatResult, Solver};

pub type Tenv<'a, 'ctx> = AHashMap<Ident, InferType<'a, 'ctx>>;
pub type TPenv = AHashMap<Ident, u32>;

pub struct TyCtxBase<'a, 'ctx> {
    pub tenv: AHashMap<Ident, InferType<'a, 'ctx>>,
    pub tpenv: TPenv,
    pub tpcount: u32,
    pub solver: Solver<'ctx>,
}

impl<'a, 'ctx> TyCtxBase<'a, 'ctx> {
    fn push(&mut self) {
        println!("(push)");
        self.solver.push();
    }

    fn pop(&mut self) {
        println!("(pop)");
        self.solver.pop(1);
    }

    fn assert(&mut self, b: &ast::Bool) {
        println!("(assert {b})");
        self.solver.assert(b)
    }

    fn tenv(&mut self) -> &mut Tenv<'a, 'ctx> {
        &mut self.tenv
    }

    fn tpenv(&mut self) -> &mut TPenv {
        &mut self.tpenv
    }

    fn tpcount(&mut self) -> &mut u32 {
        &mut self.tpcount
    }
}

pub type TyCtx<'a, 'ctx> = SemiPersistent<TyCtxBase<'a, 'ctx>>;

pub type InstTy = u32;

#[derive(Clone, Debug)]
pub struct SubstBase<'a, 'ctx>{
    pub val: AHashMap<Ident, ast::Dynamic<'ctx>>,
    pub ty: AHashMap<Ident, InstTy>,
    phantom: PhantomData<& 'a ()>,
}

pub type Subst<'a, 'ctx> = SemiPersistent<SubstBase<'a, 'ctx>>;

impl<'a, 'ctx> SubstBase<'a, 'ctx> {
    fn val(&mut self) -> &mut AHashMap<Ident, ast::Dynamic<'ctx>> {
        &mut self.val
    }

    fn ty(&mut self) -> &mut AHashMap<Ident, InstTy> {
        &mut self.ty
    }
}

#[derive(Clone, Debug)]
pub enum InferType<'a, 'ctx> {
    Subst(Subst<'a, 'ctx>, &'a Type),
    Selfify(ast::Dynamic<'ctx>, &'a BaseType),
}

pub fn new_subst<'a, 'ctx>(tcx: &TyCtxBase<'a, 'ctx>) -> Subst<'a, 'ctx> {
    let ty = tcx.tpenv.clone();
    Subst::new(SubstBase{ty, val: AHashMap::default(), phantom: PhantomData})
}

pub fn empty_subst<'a, 'ctx>() -> Subst<'a, 'ctx> {
    Subst::new(SubstBase{ty: AHashMap::default(), val: AHashMap::default(), phantom: PhantomData})
}

impl<'a, 'ctx> Subst<'a, 'ctx> {
    pub fn insert_v(&mut self, id: Ident, val: ast::Dynamic<'ctx>) -> impl DerefMut<Target=Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_insert_dr(id, val), SubstBase::val))
    }

    pub fn remove_v(&mut self, id: Ident) -> impl DerefMut<Target=Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_remove_dr(id), SubstBase::val))
    }

    pub fn insert_tp(&mut self, id: Ident, val: InstTy) -> impl DerefMut<Target=Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_insert_dr(id, val), SubstBase::ty))
    }

    pub fn remove_tp(&mut self, id: Ident) -> impl DerefMut<Target=Subst<'a, 'ctx>> + '_ {
        self.do_and_revert(shift(map_remove_dr(id), SubstBase::ty))
    }
}

pub fn ty_to_infer<'a, 'ctx>(ty: &'a Type, tcx: &TyCtx<'a, 'ctx>) -> InferType<'a, 'ctx> {
    InferType::Subst(new_subst(tcx), ty)
}

impl<'a, 'ctx> From<&'a Type> for InferType<'a, 'ctx> {
    fn from(ty: &'a Type) -> Self {
        let base = SubstBase{ty: Default::default(), val: Default::default(), phantom: PhantomData};
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
        Predicate::Var(x) => subst.val
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
        self.do_and_revert(add_assumption_dr(assume))
    }

    pub fn insert<'b>(
        &'b mut self,
        id: &'b Ident,
        ty: InferType<'a, 'ctx>,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        match ty {
            InferType::Subst(subst, Type::Refined(b_ty, box r)) => {
                let z3_const = self.fresh_const(b_ty, id.as_str());
                let z3_pred = convert_pred(&subst, self, r, &z3_const).as_bool().unwrap();
                Either::L(self.do_and_revert((
                    add_assumption_dr(z3_pred),
                    shift(
                        map_insert_dr(id.clone(), InferType::Selfify(z3_const, b_ty)),
                        TyCtxBase::tenv,
                    ),
                )))
            }
            ty => {
                Either::R(self.do_and_revert(shift(map_insert_dr(id.clone(), ty), TyCtxBase::tenv)))
            }
        }
    }

    pub fn insert_tp<'b>(
        &'b mut self,
        id: &'b Ident,
    ) -> impl DerefMut<Target = TyCtx<'a, 'ctx>> + 'b {
        let n = self.tpcount;
        self.do_and_revert((
            shift(inc_dr(), TyCtxBase::tpcount),
            shift(map_insert_dr(id.clone(), n), TyCtxBase::tpenv),
        ))
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

pub fn make_tcx<'ctx>(context: &'ctx Context) -> TyCtx<'static, 'ctx> {
    let solver = Solver::new(&context);
    let tenv = make_tenv();
    TyCtx::new(TyCtxBase {
        solver,
        tenv,
        tpenv: AHashMap::default(),
        tpcount: 0,
    })
}
