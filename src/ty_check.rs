use crate::ctxt::{convert_pred, InferType, Subst, Tenv, TyCtx};
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
    NotFun(Type),
    Unbound(Ident),
    PredIllFormed(&'a Type),
    BinderMismatch(Ident, &'a Type),
    BadApp,
}

type PredTy = BaseType;

type TCResult<'a, 'ctx, T> = Result<T, TypeError<'a, 'ctx>>;

fn lit_kind(l: &Lit) -> &'static BaseType {
    match l {
        Lit::Int(_) => &PredTy::Int,
        Lit::Bool(_) => &PredTy::Bool,
    }
}

fn infer_pred_ty(pred: &Predicate, tenv: &Tenv, res_ty: &BaseType) -> Result<PredTy, ()> {
    let recur = |pred| infer_pred_ty(pred, tenv, res_ty);
    match pred {
        Predicate::Res => Ok(res_ty.clone()),
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
        Type::Refined(base, box pred) => match infer_pred_ty(pred, &tcx.tenv, base) {
            Ok(PredTy::Bool) => Ok(()),
            _ => Err(ty),
        },
        // Dep Fun
        Type::Fun(box (id, arg_ty @ Type::Refined(base, _), ret_ty)) => {
            check_type_well_formed(arg_ty, tcx)?;
            let dummy_ty = InferType::Selfify(tcx.fresh_const(&base, "dummy"), &base);
            check_type_well_formed(ret_ty, &mut *tcx.insert_sp(id, dummy_ty))
        }
        Type::Fun(box (_, arg_ty, ret_ty)) => {
            check_type_well_formed(arg_ty, tcx)?;
            check_type_well_formed(ret_ty, tcx)
        }
    }
}

fn check_subtype_val<'a, 'ctx>(
    actual: &ast::Dynamic<'ctx>,
    acutal_base: &BaseType,
    expect: &'a Type,
    expect_s: &'a Subst<'ctx>,
    tcx: &TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    match expect {
        Type::Refined(base, pred) if acutal_base == base => {
            let pre_cond_check = convert_pred(&expect_s, tcx, pred, actual)
                .as_bool()
                .unwrap();
            tcx.check(pre_cond_check).map_err(Some)
        }
        _ => Err(None),
    }
}

fn check_subtype<'a, 'ctx>(
    actual: &mut InferType<'a, 'ctx>,
    expect: &'a Type,
    expect_s: &mut Subst<'ctx>,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    match actual {
        InferType::Selfify(actual, actual_base) => {
            check_subtype_val(actual, actual_base, expect, expect_s, tcx)
        }
        InferType::Subst(actual_s, actual) => {
            check_subtype_h(actual, actual_s, expect, expect_s, tcx)
        }
    }
}

fn check_subtype_h<'a, 'ctx>(
    actual: &'a Type,
    actual_s: &mut Subst<'ctx>,
    expect: &'a Type,
    expect_s: &mut Subst<'ctx>,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> Result<(), Option<Model<'ctx>>> {
    match (actual, expect) {
        (Type::Refined(actual_base, actual_pred), Type::Refined(expect_base, expect_pred))
            if actual_base == expect_base =>
        {
            let fresh_const = tcx.fresh_const(actual_base, "res");
            let actual_pred = convert_pred(actual_s, tcx, actual_pred, &fresh_const)
                .as_bool()
                .unwrap();
            let expect_pred = convert_pred(expect_s, tcx, expect_pred, &fresh_const)
                .as_bool()
                .unwrap();
            tcx.check(ast::Bool::implies(&actual_pred, &expect_pred))
                .map_err(Some)
        }
        // Dependent Fun
        (
            Type::Fun(box (actual_id, actual_in, actual_out)),
            Type::Fun(box (expect_id, expect_in @ Type::Refined(expected_in_base, _), expect_out)),
        ) => {
            let new_tcx =
                &mut *tcx.insert_sp(expect_id, InferType::Subst(expect_s.clone(), expect_in));
            let Some(InferType::Selfify(expected_in_val, _)) = new_tcx.tenv.get(expect_id) else {
                unreachable!()
            };
            check_subtype_val(
                expected_in_val,
                &expected_in_base,
                actual_in,
                actual_s,
                new_tcx,
            )?;
            let actual_s = &mut *actual_s.insert_sp(actual_id.clone(), expected_in_val.clone());
            let expect_s = &mut *expect_s.insert_sp(expect_id.clone(), expected_in_val.clone());
            check_subtype_h(actual_out, actual_s, expect_out, expect_s, new_tcx)
        }
        // Fun
        (Type::Fun(box (_, actual_in, actual_out)), Type::Fun(box (_, expect_in, expect_out))) => {
            check_subtype_h(expect_in, expect_s, actual_in, actual_s, tcx)?;
            check_subtype_h(actual_out, actual_s, expect_out, expect_s, tcx)
        }
        _ => Err(None),
    }
}

fn lit_to_z3<'ctx>(l: &Lit, ctx: &'ctx Context) -> ast::Dynamic<'ctx> {
    match l {
        Lit::Int(n) => ast::Int::from_i64(ctx, *n as i64).into(),
        Lit::Bool(b) => ast::Bool::from_bool(ctx, *b).into(),
    }
}

pub fn infer_type<'a, 'ctx>(
    exp: &'a Exp,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, InferType<'a, 'ctx>> {
    match exp {
        Exp::Lit(l) => Ok(InferType::Selfify(lit_to_z3(l, tcx.ctx()), &lit_kind(l))),
        Exp::Var(id) => tcx.tenv.get(id).ok_or(Unbound(id.clone())).cloned(),
        Exp::App(box []) => Err(BadApp),
        Exp::App(box [f, args @ ..]) => {
            args.iter().fold(infer_type(f, tcx), |f_ty, arg| {
                match (f_ty?, infer_type(arg, tcx)?) {
                    (
                        bad @ (InferType::Subst(_, Type::Refined(..)) | InferType::Selfify(..)),
                        _,
                    ) => Err(NotFun(infer_ty_to_ty(&bad))),
                    // Dependent Fun
                    (
                        InferType::Subst(subst, Type::Fun(box (id, arg_ty, ret_ty))),
                        InferType::Selfify(z3_val, base),
                    ) => {
                        check_subtype_val(&z3_val, base, arg_ty, &subst, tcx).map_err(|model| {
                            SubType {
                                model,
                                exp: arg,
                                actual: z3_ast_to_type(&z3_val, base),
                                expected: apply_subst(arg_ty, &subst),
                            }
                        })?;
                        let subst = subst.map(|data| {
                            data.insert(id.clone(), z3_val);
                        });
                        Ok(InferType::Subst(subst, ret_ty))
                    }
                    (_, InferType::Subst(_, Type::Refined(..))) => Err(NotAnf(exp)), // Not in ANF
                    // Fun
                    (
                        InferType::Subst(mut f_subst, Type::Fun(box (_, expect_arg, ret_ty))),
                        mut actual_arg,
                    ) => {
                        check_subtype(&mut actual_arg, expect_arg, &mut f_subst, tcx).map_err(
                            |model| SubType {
                                model,
                                exp: arg,
                                actual: infer_ty_to_ty(&actual_arg),
                                expected: apply_subst(expect_arg, &f_subst),
                            },
                        )?;
                        Ok(InferType::Subst(f_subst, ret_ty))
                    }
                }
            })
        }
        Exp::Ascribe(box (exp, ty)) => {
            check_type_well_formed(ty, tcx).map_err(PredIllFormed)?;
            check_type(exp, ty, tcx)?;
            Ok(InferType::Subst(Subst::default(), ty))
        }
        _ => Err(CantInfer(exp)),
    }
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
                check_lambda(rest, body, ret_ty, &mut *tcx.insert_sp(id, arg_ty.into()))
            } else {
                Err(BinderMismatch(id.clone(), ty))
            }
        }
        (_, Type::Refined(..)) => Err(NotFun(ty.clone())),
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
            check_let(rest, body, ty, &mut *tcx.insert_sp(id, bound_ty))
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
        [(id, _, bound_ty@Type::Fun(..)), rest @ ..] => {
            check_let_rec(rest, &mut *tcx.insert_sp(id, bound_ty.into()), then)
        }
        [(_, _, ty), ..] => Err(NotFun(ty.clone()))
    }
}

fn check_type<'a, 'ctx>(
    exp: &'a Exp,
    ty: &'a Type,
    tcx: &mut TyCtx<'a, 'ctx>,
) -> TCResult<'a, 'ctx, ()> {
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
            InferType::Subst(_, _) => Err(NotAnf(exp)),
        },
        _ => {
            let mut inf_ty = infer_type(exp, tcx)?;
            check_subtype(&mut inf_ty, ty, &mut Subst::default(), tcx).map_err(|model| SubType {
                actual: infer_ty_to_ty(&inf_ty),
                expected: ty.clone(),
                exp,
                model,
            })
        }
    }
}
