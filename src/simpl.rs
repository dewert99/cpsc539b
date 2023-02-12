use std::mem;
use std::mem::take;
use crate::defs::*;
use crate::semi_persistent::SPHashMap;


fn try_recur<T>(exp: &mut Exp, rec: &mut impl FnMut(&mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Lambda(box (_, exp)) => rec(exp),
        Var(_) => Ok(()),
        App(box [exp1, exp2]) => {
            rec(exp2)?;
            rec(exp1)
        }
        Ascribe(box (exp, _)) => rec(exp),
        Tuple(box exps) => exps.iter_mut().try_for_each(&mut *rec),
        Proj(_, box exp) => rec(exp),
        Inj(_, box exp) => rec(exp),
        Match(box exp, box arms) => {
            rec(exp)?;
            arms.iter_mut().map(|x| &mut x.1).try_for_each(&mut *rec)
        }
        Fix(box (_, exp)) => rec(exp),
        Let(box bindings, box body) => {
            bindings.iter_mut().map(|x| &mut x.1).try_for_each(&mut *rec)?;
            rec(body)
        }
    }
}

// similar to try_recur but it doesn't step into bindings
fn try_recur2<T>(exp: &mut Exp, rec: &mut impl FnMut(&mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Lambda(_) | Var(_) | Fix(_) | Let(..) => Ok(()),
        App(box [exp1, exp2]) => {
            rec(exp2)?;
            rec(exp1)
        }
        Ascribe(box (exp, _)) => rec(exp),
        Tuple(box exps) => exps.iter_mut().try_for_each(&mut *rec),
        Proj(_, box exp) => rec(exp),
        Inj(_, box exp) => rec(exp),
        Match(box exp, _) => rec(exp),
    }
}

#[derive(Copy, Clone)]
pub enum Never {}

fn simpl_match_h<T>(exp: &mut Exp, stop: Result<(), T>, defs: &TypeDefs, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Match(box scrut, box arms) => {
            rec(true, scrut)?;
            match scrut {
                Inj(idx, box scrut) if idx < &mut arms.len() => {
                    let scrut = take(scrut);
                    let (id, body) = take(&mut arms[*idx]);
                    *exp = Let(Box::new([(id, scrut)]), Box::new(body));
                    stop?;
                    rec(false, exp)
                }
                Ascribe(box (Inj(idx, box scrut), ty)) => match defs.resolve(ty) {
                    Sum(box tys) if idx < &mut arms.len() && idx < &mut tys.len() => {
                        let scrut = take(scrut);
                        let (id, body) = take(&mut arms[*idx]);
                        let ty = tys[*idx].clone();
                        let scrut = Ascribe(Box::new((scrut, ty)));
                        *exp = Let(Box::new([(id, scrut)]), Box::new(body));
                        stop?;
                        rec(false, exp)
                    }
                    _ => rec(false, exp)
                }
                _ => rec(false, exp)
            }
        }
        _ => rec(false, exp)
    }
}

fn simpl_proj_h<T>(exp: &mut Exp, stop: Result<(), T>, defs: &TypeDefs, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Proj(idx, box scrut) => {
            rec(true, scrut)?;
            match scrut {
                Tuple(box exps) if idx < &mut exps.len() => {
                    let body = take(&mut exps[*idx]);
                    *exp = body;
                    stop
                }
                Ascribe(box (Tuple(box exps), ty)) => match defs.resolve(ty) {
                    Prod(box tys) if idx < &mut exps.len() && idx < &mut tys.len() => {
                        let body = take(&mut exps[*idx]);
                        let ty = tys[*idx].clone();
                        *exp = Ascribe(Box::new((body, ty)));
                        stop
                    }
                    _ => Ok(())
                }
                _ => Ok(())
            }
        }
        _ => rec(false, exp)
    }
}

fn simpl_app_h<T>(exp: &mut Exp, stop: Result<(), T>, defs: &TypeDefs, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        App(box [f, arg]) => {
            rec(true, arg)?;
            rec(true, f)?;
            match f {
                Lambda(box binding) => {
                    let (id, body) = take(binding);
                    let arg = take(arg);
                    *exp = Let(Box::new([(id, arg)]), Box::new(body));
                    stop?;
                    rec(false, exp)
                }
                Ascribe(box (Lambda(box binding), ty)) => match defs.resolve(ty) {
                    Fun(box ty) => {
                        let (id, body) = take(binding);
                        let [arg_ty, res_ty] = ty.clone();
                        let arg = take(arg);
                        let arg = Ascribe(Box::new((arg, arg_ty)));
                        let body = Ascribe(Box::new((body, res_ty)));
                        *exp = Let(Box::new([(id, arg)]), Box::new(body));
                        stop?;
                        rec(false, exp)
                    }
                    _ => Ok(())
                }
                _ => Ok(())
            }
        }
        _ => rec(false, exp)
    }
}

fn erase_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Ascribe(box (expi, _)) => {
            *exp = take(expi);
            rec(true, exp)
        }
        _ => rec(false, exp)
    }
}

fn simpl_ascribe_h<T>(exp: &mut Exp, stop: Result<(), T>, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Ascribe(box (expi @ Ascribe(_), _)) => {
            *exp = take(expi);
            stop?;
            rec(true, exp)
        }
        _ => rec(false, exp)
    }
}


type Env<'a> = (&'a mut SPHashMap<Ident, Exp>, &'a mut SPHashMap<Ident, ()>);

fn subst_let(bindings: &mut [(Ident, Exp)], body: &mut Exp, already_done: &mut bool, (env1, env2): Env<'_>) -> () {
    match bindings {
        [(id, exp), rest @ ..] => {
            subst_let(rest, exp, already_done, (env1, &mut env2.remove_sp(id.clone())))
        }
        [] => {
            subst(body, already_done, (env1, env2))
        }
    }
}

fn subst(exp: &mut Exp, already_done: &mut bool, (env1, env2): Env<'_>) {
    if env2.is_empty() {
        return;
    }
    match exp {
        Var(id) if env2.contains_key(id) => {
            *already_done = false;
            *exp = env1.get(id).unwrap().clone();
        }
        Lambda(box (id, body)) =>
            subst(body, already_done, (env1, &mut env2.remove_sp(id.clone()))),
        Fix(box (id, body)) =>
            subst(body, already_done, (env1, &mut env2.remove_sp(id.clone()))),
        Match(_, box arms) =>
            arms.iter_mut().for_each(|(id, body)| {
                subst(body, already_done, (env1, &mut env2.remove_sp(id.clone())))
            }),
        Let(box bindings, box body) => subst_let(bindings, body, already_done, (env1, env2)),
        _ => resolve_never(try_recur2(exp, &mut |exp| Ok(subst(exp, already_done, (env1, env2))))),
    }
}

fn handle_let<T, U>(do_bindings: bool, bindings: &mut [(Ident, Exp)], body: &mut Exp, (env1, env2): Env<'_>, retry: &mut impl FnMut(&mut Exp, Env<'_>) -> Result<T, U>) -> Result<T, U> {
    match bindings {
        [(id, exp), rest @ ..] => {
            if do_bindings {
                retry(exp, (env1, env2))?;
            }
            let env = (&mut *env1.insert_sp(id.clone(), exp.clone()), &mut *env2.insert_sp(id.clone(), ()));
            handle_let(do_bindings, rest, body, env, retry)
        }
        [] => {
            retry(body, (env1, env2))
        }
    }
}

macro_rules! ite {
    ($i:expr, $t:expr, $e:expr) => (if $i {$t} else {$e});
}


fn eval_h<T: Copy>(exp: &mut Exp, mut env: Env<'_>, stop: Result<(), T>, defs: &TypeDefs) -> Result<(), T> {
    let mut do_bindings = true;
    match exp {
        App(box [fun, arg]) => {
            eval_h(arg, (&mut *env.0, &mut env.1.clear()), stop, defs)?;
            eval_h(fun, (&mut *env.0, &mut env.1.clear()), stop, defs)?;
            simpl_app_h(exp, stop, defs,&mut |_, _| Ok(()))?;
            do_bindings = false;
        }
        Match(box scrut, _) => {
            eval_h(scrut, (&mut *env.0, &mut *env.1), stop, defs)?;
            simpl_match_h(exp, stop, defs,&mut |_, _| Ok(()))?;
            do_bindings = false;
        }
        Proj(_, box scrut) => {
            eval_h(scrut, (&mut *env.0, &mut *env.1), stop, defs)?;
            return simpl_proj_h(exp, stop, defs,&mut |_, _| Ok(()));
        }
        Ascribe(box (scrut, _)) => {
            eval_h(scrut, (&mut *env.0, &mut *env.1), stop, defs)?;
            return simpl_ascribe_h(exp, stop, &mut |_, _| Ok(()));
        }
        _ => {}
    }
    match exp {
        Var(id) => {
            match env.0.get(id) {
                Some(val) => {
                    *exp = val.clone();
                    stop
                }
                None => Ok(())
            }
        }
        Let(box bindings, body) => {
            handle_let(do_bindings, bindings, body, env, &mut |exp, env| eval_h(exp, env, stop, defs))?;
            *exp = take(body);
            stop
        }
        Lambda(_) => {
            let mut already_done = true;
            subst(exp, &mut already_done, env);
            ite!(already_done, Ok(()), stop)
        }
        _ => try_recur2(exp, &mut |exp| eval_h(exp, (&mut env.0, &mut env.1), stop, defs))
    }
}

pub fn resolve_never<T>(r: Result<T, Never>) -> T {
    match r {
        Ok(x) => x,
        Err(n) => match n {}
    }
}

pub fn resolve_step(r: Result<(), ()>) {
    match r {
        Ok(()) => println!("stuck"),
        Err(()) => ()
    }
}

fn simpl_h<T: Copy>(exp: &mut Exp, stop: Result<(), T>, defs: &TypeDefs, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    simpl_match_h(exp, stop, defs, &mut |b, exp| ite!(b, rec(true, exp),
        simpl_proj_h(exp, stop, defs, &mut |b, exp| ite!(b, rec(true, exp),
            simpl_ascribe_h(exp, stop, &mut |b, exp| ite!(b, rec(true, exp),
                simpl_app_h(exp, stop, defs, rec)))))))
}

pub fn erase(exp: &mut Exp) -> Result<(), Never> {
    erase_h(exp, &mut |b, exp| ite!(b, erase(exp),
        try_recur(exp, &mut erase)))
}

pub fn simpl_match(exp: &mut Exp, defs: &TypeDefs) -> Result<(), Never> {
    simpl_match_h(exp, Ok(()), defs,&mut |b, exp| ite!(b, simpl_match(exp, defs),
        try_recur(exp, &mut |exp| simpl_match(exp, defs))))
}

pub fn simpl_proj(exp: &mut Exp, defs: &TypeDefs) -> Result<(), Never> {
    simpl_match_h(exp, Ok(()), defs,&mut |b, exp| ite!(b, simpl_proj(exp, defs),
        try_recur(exp, &mut |exp| simpl_proj(exp, defs))))
}

pub fn simpl_app(exp: &mut Exp, defs: &TypeDefs) -> Result<(), Never> {
    simpl_app_h(exp, Ok(()), defs,&mut |b, exp| ite!(b, simpl_app(exp, defs),
        try_recur(exp, &mut |exp| simpl_app(exp, defs))))
}

pub fn simpl(exp: &mut Exp, defs: &TypeDefs) -> Result<(), Never> {
    simpl_h(exp, Ok(()), defs,&mut |b, exp| ite!(b, simpl(exp, defs),
        try_recur(exp, &mut |exp| simpl(exp, defs))))
}

pub fn simpl_step(exp: &mut Exp, defs: &TypeDefs) -> Result<(), ()> {
    simpl_h(exp, Err(()), defs, &mut |b, exp| ite!(b, simpl_step(exp, defs),
        try_recur(exp, &mut |exp| simpl_step(exp, defs))))
}


pub fn eval(exp: &mut Exp, defs: &TypeDefs) -> Result<(), Never> {
    let (mut x, mut y) = Default::default();
    eval_h(exp, (&mut x, &mut y), Ok(()), defs)
}

pub fn step(exp: &mut Exp, defs: &TypeDefs) -> Result<(), ()> {
    let (mut x, mut y) = Default::default();
    eval_h(exp, (&mut x, &mut y), Err(()), defs)
}

pub fn collapse_lets(exp: &mut Exp) {
    fn collapse_lets_h(exp: &mut Exp, past: Option<&mut Vec<(Ident, Exp)>>) {
        match exp {
            Ascribe(box (l@Let(_, _), _)) => {
                let mut let_expr = take(l);
                let mut ascribe_expr = take(exp);
                match &mut let_expr {
                    Let(_, box body) => {
                        match &mut ascribe_expr {
                            Ascribe(box (new_body, _)) => *new_body = take(body),
                            _ => unreachable!()
                        };
                        *body = ascribe_expr
                    },
                    _ => unreachable!()
                };
                *exp = let_expr;
            }
            _ => {}
        }
        match exp {
            Let(bindings_ref, box body) => {
                let bindings = mem::replace(bindings_ref, Box::new([]));
                let mut bindings = bindings.into_vec();
                match past {
                    None => {
                        collapse_lets_h(body, Some(&mut bindings));
                        *bindings_ref = bindings.into_boxed_slice();
                    }
                    Some(past_bindings) => {
                        past_bindings.append(&mut bindings);
                        *exp = take(body);
                        collapse_lets_h(exp, Some(past_bindings))
                    }
                }
            }
            _ => resolve_never(try_recur(exp, &mut |exp| Ok(collapse_lets(exp))))
        }
    }

    collapse_lets_h(exp, None)
}


//(match (proj 0 (tuple (inj 0 (tuple)))) ( ("x" (var . "x")) ))
//(let  (("id" (lambda "x" (var . "x")))) (let (("v" ($ (var . "id") (tuple)))) ($ (var . "id") (var . "v")) ))
//(let  (("x" (tuple))) (let (("v" (lambda "x"  (var . "x")))) (var . "v")))
//($ ($ (lambda "y" (lambda "x" ($ (var . "y") (var . "x")))) (lambda "x" (tuple (var . "x")))) (tuple))
//($ (lambda "x" ($ (var . "x") (var . "x"))) (lambda "x" ($ (var . "x") (var . "x"))))
//(lambda "x" ($ (var . "f") (lambda "v" ($ ($ (var . "x") (var . "x")) (var . "v")))))
//(lambda "f" ($ (lambda "x" ($ (var . "f") (lambda "v" ($ ($ (var . "x") (var . "x")) (var . "v"))))) (lambda "x" ($ (var . "f") (lambda "v" ($ ($ (var . "x") (var . "x")) (var . "v")))))))
//(lambda "r" (lambda "x" ($ (var . "r") (tuple (var . "x")))))
//(let (("x" (as (tuple (tuple) (tuple (inj 1 (tuple)))) (x (x) (x (+ (+) (x)))))))  (as (match (proj 0 (proj 1 (var . "x"))) (("x" (tuple)) ("x" (var . "x"))) ) (x)) )
//($ (as (lambda "x" ($ (var . "x") (var . "x"))) (def . "Omega")) (lambda "x" ($ (var . "x") (var . "x"))))