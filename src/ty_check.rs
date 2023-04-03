use crate::ctxt::{empty_subst, vprintln, BInferType, InferType, InstTy, Subst, Tenv, TyCtx};
use crate::defs::{BaseType, Exp, Ident, Lit, Predicate, PrimOp, Type};
use crate::error_reporting::{apply_subst, infer_ty_to_ty, z3_ast_to_type};
use crate::ty_check::TypeError::*;
use z3::{ast, Context, Model};

#[derive(Debug)]
pub enum TypeError<'a, 'ctx> {
    SubType {
        exp: &'a Exp,
        actual: Type,
        expected: Type,
        model: Option<Model<'ctx>>,
    },
    NotAnf(&'a Exp),
    NotBool(Type, &'a Exp),
    CantInfer(&'a Exp),
    NotFun(&'a Type),
    TrailingArg(&'a Exp),
    TrailingParm(&'a Ident),
    CanApplyForallTo(&'a Exp, Type),
    Unbound(&'a Ident),
    PredIllFormed(&'a Type),
    BinderMismatch(&'a Ident, &'a Type),
    BadApp(&'a Exp),
    ShadowedTypeVar(&'a Type),
    TrailingInst(&'a Type),
    CantProve(&'a Type, Model<'ctx>),
}

type PredTy = BaseType;

type TCResult<'a, 'ctx, T> = Result<T, TypeError<'a, 'ctx>>;

fn lit_kind(l: &Lit) -> &'static BaseType {
    match l {
        Lit::Int(_) => &PredTy::Int,
        Lit::Bool(_) => &PredTy::Bool,
    }
}

fn infer_pred_ty(pred: &Predicate, tenv: &Tenv, res_ty: Option<&BaseType>) -> Result<PredTy, ()> {
    let recur = |pred| infer_pred_ty(pred, tenv, res_ty);
    match pred {
        Predicate::Res => Ok(res_ty.ok_or(())?.clone()),
        Predicate::Lit(l) => Ok(lit_kind(l).clone()),
        Predicate::Var(id) => match tenv.get(id) {
            Some(InferType::Selfify(_, ty)) => Ok((*ty).clone()),
            _ => Err(()),
        },
        Predicate::Op(box (op, p1, p2)) => match (op, recur(p1)?, recur(p2)?) {
            (PrimOp::Add | PrimOp::Sub, PredTy::Int, PredTy::Int) => Ok(PredTy::Int),
            (PrimOp::Le, PredTy::Int, PredTy::Int) => Ok(PredTy::Bool),
            (PrimOp::Add | PrimOp::Or, PredTy::Bool, PredTy::Bool) => Ok(PredTy::Bool),
            (PrimOp::Eq, ty1, ty2) if ty1 == ty2 => Ok(PredTy::Bool),
            _ => Err(()),
        },
        Predicate::Not(box [p]) => match recur(p)? {
            PredTy::Bool => Ok(PredTy::Bool),
            _ => Err(()),
        },
        Predicate::If(box [i, t, e]) => match (recur(i)?, recur(t)?, recur(e)?) {
            (PredTy::Bool, ty1, ty2) if ty1 == ty2 => Ok(ty1),
            _ => Err(()),
        },
    }
}

fn check_type_well_formed<'a, 'ctx>(
    ty: &'a Type,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), &'a Type> {
    match ty {
        Type::Refined(box (Type::Base(base), pred)) => {
            match infer_pred_ty(pred, &tcx.tenv, Some(base)) {
                Ok(PredTy::Bool) => Ok(()),
                _ => Err(ty),
            }
        }
        Type::Refined(box (ty, pred)) => match infer_pred_ty(pred, &tcx.tenv, None) {
            Ok(PredTy::Bool) => check_type_well_formed(ty, tcx),
            _ => Err(ty),
        },
        Type::Base(_) => Ok(()),
        Type::Fun(box (id, arg_ty, ret_ty)) => {
            check_type_well_formed(arg_ty, tcx)?;
            let tcx = &mut *tcx.insert(id, arg_ty.into());
            check_type_well_formed(ret_ty, tcx)
        }
        Type::Forall(box (id, ty2)) => {
            let mut tcx = tcx.insert_tp(id).map_err(|()| ty)?;
            check_type_well_formed(ty2, &mut *tcx)
        }
        Type::Var(id) => {
            if tcx.tpenv.contains_key(id) {
                Ok(())
            } else {
                Err(ty)
            }
        }
    }
}

fn check_subtype_val<'a, 'ctx>(
    actual: &ast::Dynamic<'ctx>,
    acutal_base: &'a BaseType,
    expect: &'a Type,
    expect_s: &mut Subst<'a, 'ctx>,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    check_subtype(
        BInferType::Selfify(actual.clone(), acutal_base),
        expect,
        expect_s,
        tcx,
    )
}

fn check_subtype<'a, 'ctx>(
    mut actual: BInferType<'a, 'ctx, '_>,
    expect: &'a Type,
    expect_s: &mut Subst<'a, 'ctx>,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    vprintln!(
        tcx,
        "checking {:?} is a subtype of {:?}",
        (infer_ty_to_ty(actual.reborrow())),
        (apply_subst(expect, expect_s))
    );
    let (actual, mut tcx) = tcx.insert_dummy(&"_".into(), actual);
    let tcx = &mut *tcx;
    let expect = match expect {
        Type::Var(v) => expect_s.ty.get(v).copied().unwrap_or(InstTy::Ty(expect)),
        _ => InstTy::Ty(expect),
    };
    match (actual, expect) {
        (InferType::Fresh(id1), InstTy::Fresh(id2)) => {
            if id1 == id2 {
                Ok(())
            } else {
                Err(None)
            }
        }
        (
            InferType::Selfify(actual, actual_base),
            InstTy::Ty(Type::Refined(box (Type::Base(base), pred))),
        ) => {
            if actual_base != base {
                Err(None)
            } else {
                tcx.check_pred(&expect_s, pred, Some(&actual)).map_err(Some)
            }
        }
        (actual, InstTy::Ty(Type::Refined(box (expect, pred)))) => {
            tcx.check_pred(expect_s, pred, None).map_err(Some)?;
            check_subtype(actual, expect, expect_s, tcx)
        }
        (InferType::Selfify(_, actual_base), InstTy::Ty(Type::Base(base))) => {
            if actual_base != base {
                Err(None)
            } else {
                Ok(())
            }
        }
        (
            InferType::Subst(actual_s, Type::Fun(box (actual_id, actual_arg, actual_res))),
            InstTy::Ty(Type::Fun(box (expect_id, expect_arg, expect_res))),
        ) => {
            let (mut expect_arg, mut tcx) =
                tcx.insert_dummy(expect_id, BInferType::Subst(expect_s, expect_arg));
            let tcx = &mut *tcx;
            check_subtype(expect_arg.reborrow(), actual_arg, actual_s, tcx)?;
            match expect_arg {
                InferType::Selfify(z3_var, _) => {
                    let actual_s = &mut *actual_s.insert_v(actual_id.clone(), z3_var.clone());
                    let expect_s = &mut *expect_s.insert_v(expect_id.clone(), z3_var);
                    check_subtype_h(actual_res, actual_s, expect_res, expect_s, tcx)
                }
                _ => check_subtype_h(actual_res, actual_s, expect_res, expect_s, tcx),
            }
        }
        (
            InferType::Subst(actual_s, Type::Forall(box (actual_id, actual))),
            InstTy::Ty(Type::Forall(box (expect_id, expect))),
        ) => {
            let (fresh, mut tcx) = tcx.fresh_ty();
            let actual_s = &mut *actual_s.insert_tp(actual_id.clone(), fresh);
            let expect_s = &mut *expect_s.insert_tp(expect_id.clone(), fresh);
            check_subtype_h(actual, actual_s, expect, expect_s, &mut *tcx)
        }
        (InferType::Subst(_, Type::Var(id1)), InstTy::Ty(Type::Var(id2))) => {
            if id1 == id2 {
                Ok(())
            } else {
                Err(None)
            }
        }
        _ => Err(None),
    }
}

fn check_subtype_h<'a, 'ctx>(
    actual: &'a Type,
    actual_s: &mut Subst<'a, 'ctx>,
    expect: &'a Type,
    expect_s: &mut Subst<'a, 'ctx>,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    check_subtype(BInferType::Subst(actual_s, actual), expect, expect_s, tcx)
}

fn lit_to_z3<'ctx>(l: &Lit, ctx: &'ctx Context) -> ast::Dynamic<'ctx> {
    match l {
        Lit::Int(n) => ast::Int::from_i64(ctx, *n as i64).into(),
        Lit::Bool(b) => ast::Bool::from_bool(ctx, *b).into(),
    }
}

fn infer_type<'a, 'ctx>(
    exp: &'a Exp,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, InferType<'a, 'ctx>> {
    vprintln!(tcx, "inferring type for {exp:?}");
    let mut inf = match exp {
        Exp::Lit(l) => Ok(InferType::Selfify(lit_to_z3(l, tcx.ctx()), &lit_kind(l))),
        Exp::Var(id) => tcx.tenv.get(id).ok_or(Unbound(&id)).cloned(),
        Exp::App(box []) => Err(BadApp(exp)),
        Exp::App(box [f, args @ ..]) => args.iter().fold(infer_type(f, tcx), |f_ty, arg| {
            match (f_ty?, infer_type(arg, tcx)?) {
                (
                    InferType::Subst(_, Type::Var(..) | Type::Base(..))
                    | InferType::Selfify(..)
                    | InferType::Fresh(..),
                    _,
                ) => Err(TrailingArg(exp)),
                (InferType::Subst(_, Type::Refined(..)), _) => Err(NotAnf(exp)),
                (InferType::Subst(mut s, f @ Type::Forall(..)), _) => {
                    Err(CanApplyForallTo(exp, apply_subst(f, &mut s)))
                }
                // Dependent Fun
                (
                    InferType::Subst(mut subst, Type::Fun(box (id, arg_ty, ret_ty))),
                    InferType::Selfify(z3_val, base),
                ) => {
                    check_subtype_val(&z3_val, base, arg_ty, &mut subst, tcx).map_err(|model| {
                        SubType {
                            model,
                            exp: arg,
                            actual: z3_ast_to_type(&z3_val, base),
                            expected: apply_subst(arg_ty, &mut subst),
                        }
                    })?;
                    let subst = subst.map(|data| {
                        data.val.insert(id.clone(), z3_val);
                    });
                    Ok(InferType::Subst(subst, ret_ty))
                }
                (_, InferType::Subst(_, Type::Refined(..))) => Err(NotAnf(exp)), // Not in ANF
                // Fun
                (
                    InferType::Subst(mut f_subst, Type::Fun(box (_, expect_arg, ret_ty))),
                    mut actual_arg,
                ) => {
                    check_subtype(actual_arg.reborrow(), expect_arg, &mut f_subst, tcx).map_err(
                        |model| SubType {
                            model,
                            exp: arg,
                            actual: infer_ty_to_ty(actual_arg.reborrow()),
                            expected: apply_subst(expect_arg, &mut f_subst),
                        },
                    )?;
                    Ok(InferType::Subst(f_subst, ret_ty))
                }
            }
        }),
        Exp::Inst(box exp, box tys) => {
            tys.into_iter()
                .fold(infer_type(exp, tcx), |base_ty, ty| match base_ty? {
                    InferType::Subst(subst, Type::Forall(box (id, base_ty))) => {
                        let subst = subst.map(|s| {
                            s.ty.insert(id.clone(), InstTy::Ty(ty));
                        });
                        Ok(InferType::Subst(subst, base_ty))
                    }
                    InferType::Subst(_, Type::Refined(..)) => Err(NotAnf(exp)),
                    _ => Err(TrailingInst(ty)),
                })
        }
        Exp::Ascribe(box (exp, ty)) => {
            check_type_well_formed(ty, tcx).map_err(PredIllFormed)?;
            check_type(exp, ty, tcx)?;
            Ok(ty.into())
        }
        _ => Err(CantInfer(exp)),
    }?;
    vprintln!(
        tcx,
        "inferred {exp:?} has type {:?}",
        (infer_ty_to_ty(inf.reborrow()))
    );
    Ok(inf)
}

fn check_lambda<'a, 'ctx>(
    vars: &'a [Ident],
    body: &'a Exp,
    ty: &'a Type,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, ()> {
    match (vars, ty) {
        ([], _) => check_type(body, ty, tcx),
        ([id, rest @ ..], ty @ Type::Fun(box (id2, arg_ty, ret_ty))) => {
            if id == id2 {
                check_lambda(rest, body, ret_ty, &mut *tcx.insert(id, arg_ty.into()))
            } else {
                Err(BinderMismatch(id, ty))
            }
        }
        ([id, ..], Type::Refined(box (Type::Base(..), _)) | Type::Base(..) | Type::Var(_)) => {
            Err(TrailingParm(id))
        }
        (vars, Type::Forall(box (id, ty))) => {
            let mut tcx = tcx.insert_tp(id).map_err(|()| ShadowedTypeVar(ty))?;
            check_lambda(vars, body, ty, &mut *tcx)
        }
        (vars, rty @ Type::Refined(box (ty, pred))) => {
            tcx.check_pred(&empty_subst(), pred, None)
                .map_err(|model| CantProve(rty, model))?;
            check_lambda(vars, body, ty, tcx)
        }
    }
}

fn check_let<'a, 'ctx>(
    bindings: &'a [(Ident, Exp)],
    body: &'a Exp,
    ty: &'a Type,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, ()> {
    match bindings {
        [] => check_type(body, ty, tcx),
        [(id, exp), rest @ ..] => {
            let bound_ty = infer_type(exp, tcx)?;
            check_let(rest, body, ty, &mut *tcx.insert(id, bound_ty))
        }
    }
}

fn check_let_rec<'a, 'ctx>(
    bindings: &'a [(Ident, Exp, Type)],
    tcx: &mut TyCtx<'a, 'ctx>,
    then: impl FnOnce(&mut TyCtx<'a, 'ctx>) -> TCResult<'a, 'ctx, ()>,
) -> TCResult<'a, 'ctx, ()> {
    match bindings {
        [] => then(tcx),
        [(id, _, bound_ty @ Type::Fun(..)), rest @ ..] => {
            check_let_rec(rest, &mut *tcx.insert(id, bound_ty.into()), then)
        }
        [(_, _, ty), ..] => Err(NotFun(&ty)),
    }
}

fn check_type<'a, 'ctx>(
    exp: &'a Exp,
    ty: &'a Type,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, ()> {
    vprintln!(tcx, "checking {exp:?} has type {ty:?}");
    match exp {
        Exp::Lambda(box vars, box body) => check_lambda(vars, body, ty, tcx),
        Exp::Let(box bindings, box body) => check_let(bindings, body, ty, tcx),
        Exp::Letrec(box bindings, box body) => check_let_rec(bindings, tcx, |tcx| {
            bindings
                .iter()
                .try_for_each(|(_, exp, ty)| check_type(exp, ty, tcx))?;
            check_type(body, ty, tcx)
        }),
        Exp::If(box [i, t, e]) => match infer_type(i, tcx)? {
            InferType::Selfify(z3_val, BaseType::Bool) => {
                check_type(t, ty, &mut *tcx.add_assumption(z3_val.as_bool().unwrap()))?;
                check_type(e, ty, &mut *tcx.add_assumption(!z3_val.as_bool().unwrap()))
            }
            InferType::Selfify(z3_val, ty) => Err(NotBool(z3_ast_to_type(&z3_val, ty), exp)),
            _ => Err(NotAnf(exp)),
        },
        _ => {
            let mut inf_ty = infer_type(exp, tcx)?;
            check_subtype(inf_ty.reborrow(), ty, &mut empty_subst(), tcx).map_err(|model| SubType {
                actual: infer_ty_to_ty(inf_ty.reborrow()),
                expected: ty.clone(),
                exp,
                model,
            })
        }
    }?;
    vprintln!(tcx, "checked {exp:?} had type {ty:?}");
    Ok(())
}

pub fn type_check<'a, 'ctx>(exp: &'a Exp, tcx: &mut TyCtx<'a, 'ctx>) -> TCResult<'a, 'ctx, ()> {
    infer_type(exp, tcx).map(|_| ())
}
