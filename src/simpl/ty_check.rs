use crate::defs::*;
use crate::semi_persistent::SPHashMap;

type Tenv<'a> = SPHashMap<Ident, &'a Type>;

#[derive(Debug, Eq, PartialEq)]
pub enum TypeInfo<'a> {
    Func,
    Prod(usize),
    Sum(usize),
    Type(&'a Type),
}

#[derive(Debug, Eq, PartialEq)]
pub enum TypeError<'a> {
    CantInfer,
    Mismatch { actual: TypeInfo<'a>, expected: TypeInfo<'a> },
    Unbound,
}

use TypeError::*;

type Result<'a, T> = core::result::Result<T, (&'a Exp, TypeError<'a>)>;

fn handle_let<'a, T>(bindings: &'a [(Ident, Exp)], tenv: &mut Tenv<'a>, defs: &'a TypeDefs, f: impl Fn(&mut Tenv<'a>) -> Result<'a, T>) -> Result<'a, T> {
    match bindings {
        [(id, exp), rest @ ..] => {
            let ty = infer_type(exp, tenv, defs)?;
            handle_let(rest, &mut tenv.insert_sp(id.clone(), ty), defs, f)
        }
        [] => {
            f(tenv)
        }
    }
}


fn infer_type<'a>(exp: &'a Exp, tenv: &mut Tenv<'a>, defs: &'a TypeDefs) -> Result<'a, &'a Type> {
    match exp {
        Var(x) => match tenv.get(x) {
            Some(v) => Ok(*v),
            None => Err((exp, Unbound)),
        },
        App(box [f, arg]) => {
            match defs.resolve(infer_type(f, tenv, defs)?) {
                Fun(box [input, output]) => {
                    check_type(arg, tenv, defs, input)?;
                    Ok(output)
                }
                ty => Err((f, Mismatch { actual: TypeInfo::Type(ty), expected: TypeInfo::Func }))
            }
        }
        Ascribe(box (exp, ref ty)) => {
            check_type(exp, tenv, defs, ty)?;
            Ok(ty)
        }
        Proj(idx, box exp) => {
            match defs.resolve(infer_type(exp, tenv, defs)?) {
                Prod(box tys) if *idx < tys.len() => Ok(&tys[*idx]),
                ty => Err((exp, Mismatch { actual: TypeInfo::Type(ty), expected: TypeInfo::Prod(*idx) }))
            }
        }
        Let(box bindings, box body) => {
            handle_let(bindings, tenv, defs, |tenv| infer_type(body, tenv, defs))
        }
        exp => Err((exp, CantInfer))
    }
}

fn check_type<'a>(exp: &'a Exp, tenv: &mut Tenv<'a>, defs: &'a TypeDefs, ty: &'a Type) -> Result<'a, ()> {
    match exp {
        Lambda(box (var, body)) => match defs.resolve(ty) {
            Fun(box [input, output]) =>
                check_type(body, &mut tenv.insert_sp(var.clone(), input), defs, output),
            ty => Err((exp, Mismatch { actual: TypeInfo::Func, expected: TypeInfo::Type(ty) }))
        }
        Tuple(box exps) => match defs.resolve(ty) {
            Prod(box tys) if tys.len() == exps.len() => {
                exps.iter().zip(tys.iter()).try_for_each(|(exp, ty)| check_type(exp, tenv, defs, ty))
            }
            ty => Err((exp, Mismatch { actual: TypeInfo::Prod(exps.len()), expected: TypeInfo::Type(ty) }))
        }
        Inj(idx, box exp) => match defs.resolve(ty) {
            Sum(box tys) if *idx < tys.len() => check_type(exp, tenv, defs, &tys[*idx]),
            ty => Err((exp, Mismatch { actual: TypeInfo::Sum(*idx), expected: TypeInfo::Type(ty) }))
        }
        Match(box scrut, box arms) => {
            match defs.resolve(infer_type(scrut, tenv, defs)?) {
                Sum(box tys) if tys.len() == arms.len() => {
                    arms.iter().zip(tys.iter()).try_for_each(|((id, exp), id_ty)|
                        check_type(exp, &mut tenv.insert_sp(id.clone(), id_ty), defs, ty))
                }
                ty => Err((scrut, Mismatch { actual: TypeInfo::Type(ty), expected: TypeInfo::Sum(arms.len()) }))
            }
        }
        Fix(box (var, body)) => {
            check_type(body, &mut tenv.insert_sp(var.clone(), ty), defs, ty)
        }
        Let(box bindings, box body) => {
            handle_let(bindings, tenv, defs,|tenv| check_type(body, tenv, defs, ty))
        }
        // CheckInfer
        _ => {
            let actual = infer_type(exp, tenv, defs)?;
            if actual == ty {
                Ok(())
            } else {
                Err((exp, Mismatch { actual: TypeInfo::Type(actual), expected: TypeInfo::Type(ty) }))
            }
        }
    }
}

pub fn type_check<'a>(exp: &'a Exp, defs: &'a TypeDefs) -> Result<'a, &'a Type> {
    let mut tenv = Tenv::default();
    infer_type(exp, &mut tenv, defs)
}