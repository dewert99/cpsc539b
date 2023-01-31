use crate::defs::*;
use crate::semi_persistent::SPHashMap;

type Tenv<'a> = SPHashMap<Ident, &'a Type>;

#[derive(Debug, Eq, PartialEq)]
pub enum TypeError<'a> {
    NotFunc(&'a Type),
    NotProd(&'a Type, usize),
    NotSum(&'a Type, usize),
    CantInfer,
    Mismatch1 { expected: &'a Type },
    Mismatch2 { actual: &'a Type, expected: &'a Type },
    Unbound,
}

use TypeError::*;

type Result<'a, T> = core::result::Result<T, (&'a Exp, TypeError<'a>)>;

fn handle_let<'a, T>(bindings: &'a [(Ident, Exp)], tenv: &mut Tenv<'a>, f: impl Fn(&mut Tenv<'a>) -> Result<'a, T>) -> Result<'a, T> {
    match bindings {
        [(id, exp), rest @ ..] => {
            let ty = infer_type(exp, tenv)?;
            handle_let(rest, &mut tenv.insert_sp(id.clone(), ty), f)
        }
        [] => {
            f(tenv)
        }
    }
}


fn infer_type<'a>(exp: &'a Exp, tenv: &mut Tenv<'a>) -> Result<'a, &'a Type> {
    match exp {
        Var(x) => match tenv.get(x) {
            Some(v) => Ok(*v),
            None => Err((exp, Unbound)),
        },
        App(box [f, arg]) => {
            match infer_type(f, tenv)? {
                Fun(box [input, output]) => {
                    check_type(arg, tenv, input)?;
                    Ok(output)
                }
                ty => Err((exp, NotFunc(ty)))
            }
        }
        Ascribe(box (exp, ref ty)) => {
            check_type(exp, tenv, ty)?;
            Ok(ty)
        }
        Proj(idx, box exp) => {
            match infer_type(exp, tenv)? {
                Prod(box tys) if *idx < tys.len() => Ok(&tys[*idx]),
                ty => Err((exp, NotProd(ty, *idx)))
            }
        }
        Let(box bindings, box body) => {
            handle_let(bindings, tenv, |tenv| infer_type(body, tenv))
        }
        exp => Err((exp, CantInfer))
    }
}

fn check_type<'a>(exp: &'a Exp, tenv: &mut Tenv<'a>, ty: &'a Type) -> Result<'a, ()> {
    match (exp, ty) {
        // CheckInfer
        (Var(_) | App(_) | Ascribe(_) | Proj(..), ty) => {
            let actual = infer_type(exp, tenv)?;
            if actual == ty {
                Ok(())
            } else {
                Err((exp, Mismatch2 { actual, expected: ty }))
            }
        }
        (Lambda(box (var, body)), Fun(box [input, output])) => {
            check_type(body, &mut tenv.insert_sp(var.clone(), input), output)
        }
        (Tuple(box exps), Prod(box tys)) if tys.len() == exps.len() => {
            exps.iter().zip(tys.iter()).try_for_each(|(exp, ty)| check_type(exp, tenv, ty))
        }
        (Inj(idx, box exp), Sum(box tys)) if *idx < tys.len() => {
            check_type(exp, tenv, &tys[*idx])
        }
        (Match(box srut, box arms), ty) => {
            match infer_type(srut, tenv)? {
                Sum(box tys) if tys.len() == arms.len() => {
                    arms.iter().zip(tys.iter()).try_for_each(|((id, exp), id_ty)|
                        check_type(exp, &mut tenv.insert_sp(id.clone(), id_ty), ty))
                }
                ty => Err((exp, NotSum(ty, arms.len())))
            }
        }
        (Fix(box (var, body)), ty) => {
            check_type(body, &mut tenv.insert_sp(var.clone(), ty), ty)
        }
        (Let(box bindings, box body), ty) => {
            handle_let(bindings, tenv, |tenv| check_type(body, tenv, ty))
        }
        (exp, ty) => Err((exp, Mismatch1 { expected: ty }))
    }
}

pub fn type_check(exp: &Exp) -> Result<'_, &Type> {
    let mut tenv = Tenv::default();
    infer_type(exp, &mut tenv)
}