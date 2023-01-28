use std::mem::take;
use crate::defs::*;
use crate::tenv::SPHashMap;


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

pub enum Never {}

fn simpl_match_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Match(box scrut, box arms) => {
            rec(true, scrut)?;
            match scrut {
                Inj(idx, box scrut) if idx < &mut arms.len() => {
                    let scrut = take(scrut);
                    let (id, body) = take(&mut arms[*idx]);
                    *exp = Let(Box::new([(id, scrut)]), Box::new(body));
                    rec(true, exp)
                }
                _ => arms.iter_mut().try_for_each(|x| rec(true, &mut x.1))
            }
        }
        _ => rec(false, exp)
    }
}

fn simpl_proj_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Proj(idx, box scrut) => {
            rec(true, scrut)?;
            match scrut {
                Tuple(box exps) if idx < &mut exps.len() => {
                    let body = take(&mut exps[*idx]);
                    *exp = body;
                    Ok(())
                }
                _ => Ok(())
            }
        }
        _ => rec(false, exp)
    }
}

fn simpl_app_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        App(box [f, arg]) => {
            rec(true, f)?;
            match f {
                Lambda(box binding) => {
                    let (id, body) = take(binding);
                    let arg = take(arg);
                    *exp = Let(Box::new([(id, arg)]), Box::new(body));
                    rec(true, exp)
                }
                _ => rec(true, arg)
            }
        }
        _ => rec(false, exp)
    }
}

fn erase_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Ascribe(box (expi, ty)) => {
            *exp = take(expi);
            rec(true, exp)
        }
        _ => rec(false, exp)
    }
}


type Env = SPHashMap<Ident, Exp>;

fn handle_let<T, U>(bindings: &mut [(Ident, Exp)], body: &mut Exp, env: &mut Env, retry: &mut impl FnMut(&mut Exp, &mut Env) -> Result<T, U>) -> Result<T, U> {
    match bindings {
        [(id, exp), rest @ ..] => {
            retry(exp, env)?;
            handle_let(rest, body, &mut env.insert_sp(id.clone(), take(exp)), retry)
        }
        [] => {
            retry(body, env)
        }
    }
}

fn subst_let_h<T>(exp: &mut Exp, env: &mut Env, rec: &mut impl Fn(bool, &mut Exp, &mut Env) -> Result<(), T>) -> Result<(), T> {
    match exp {
        Var(id) => {
            match env.get(id) {
                Some(val) => *exp = val.clone(),
                None => ()
            };
            Ok(())
        }
        Let(box bindings, body) => {
            let res = handle_let(bindings, body, env, &mut |exp, env| rec(true, exp, env));
            *exp = take(body);
            res
        }
        _ => rec(false, exp, env)
    }
}

pub fn resolve_never<T>(r: Result<T, Never>) -> T {
    match r {
        Ok(x) => x,
        Err(n) => match n {}
    }
}

macro_rules! ite {
    ($i:expr, $t:expr, $e:expr) => (if $i {$t} else {$e});
}

fn simpl_h<T>(exp: &mut Exp, rec: &mut impl FnMut(bool, &mut Exp) -> Result<(), T>) -> Result<(), T> {
    simpl_match_h(exp, &mut |b, exp| ite!(b, rec(true, exp),
        simpl_proj_h(exp, &mut |b, exp| ite!(b, rec(true, exp),
            simpl_app_h(exp, rec)))))
}

pub fn erase(exp: &mut Exp) -> Result<(), Never> {
    erase_h(exp, &mut |b, exp| ite!(b, erase(exp),
        try_recur(exp, &mut erase)))
}

pub fn simpl_match(exp: &mut Exp) -> Result<(), Never> {
    simpl_match_h(exp, &mut |b, exp| ite!(b, simpl_match(exp),
        try_recur(exp, &mut simpl_match)))
}

pub fn simpl_proj(exp: &mut Exp) -> Result<(), Never> {
    simpl_match_h(exp, &mut |b, exp| ite!(b, simpl_proj(exp),
        try_recur(exp, &mut simpl_proj)))
}

pub fn simpl_app(exp: &mut Exp) -> Result<(), Never> {
    simpl_app_h(exp, &mut |b, exp| ite!(b, simpl_proj(exp),
        try_recur(exp, &mut simpl_proj)))
}

pub fn simpl(exp: &mut Exp) -> Result<(), Never> {
    simpl_h(exp, &mut |b, exp| ite!(b, simpl(exp),
        try_recur(exp, &mut simpl)))
}

pub fn subst_let(exp: &mut Exp) -> Result<(), Never> {
    fn subst_let2(exp: &mut Exp, env: &mut Env) -> Result<(), Never> {
        subst_let_h(exp, env, &mut |b, exp, env| ite!(b, subst_let2(exp, env),
            try_recur(exp, &mut |exp| subst_let2(exp, env))))
    }
    let mut env = Env::default();
    subst_let2(exp, &mut env)
}

pub fn eval(exp: &mut Exp) -> Result<(), Never> {
    fn eval2(exp: &mut Exp, env: &mut Env) -> Result<(), Never> {
        subst_let_h(exp, env, &mut |b, exp, env| ite!(b, eval2(exp, env),
            simpl_h(exp, &mut |b, exp| ite!(b, eval2(exp, env),
                try_recur(exp, &mut |exp| eval2(exp, env))))))
    }
    let mut env = Env::default();
    eval2(exp, &mut env)
}



//(match (proj 0 (tuple (inj 0 (tuple)))) ( ("x" (var . "x")) ))