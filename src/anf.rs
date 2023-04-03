use crate::defs::{Exp, Ident, Predicate, Type};
use crate::util::SPHashMap;
use ahash::AHashMap;
use std::fmt::Write;
use std::mem;

#[derive(Default)]
struct Fresh(u32);

impl Fresh {
    fn fresh_id(&mut self, ident: &Ident) -> Ident {
        let mut res = Ident::new();
        write!(res, "{ident}${}", self.0).unwrap();
        self.0 += 1;
        res
    }

    fn fresh(&mut self) -> Ident {
        let mut res = Ident::new();
        write!(res, "${}", self.0).unwrap();
        self.0 += 1;
        res
    }
}

pub fn anf_translate(exp: &mut Exp) {
    let mut sp = SPHashMap::new(AHashMap::new());
    anf_translate_h(exp, &mut sp);
}

fn anf_translate_h(exp: &mut Exp, var_map: &mut SPHashMap<Ident, Ident>) {
    let mut bindings = Vec::new();
    let mut fresh = Fresh(0);
    anf_translate_bindings(exp, var_map, &mut bindings, &mut fresh);
    if !bindings.is_empty() {
        let exp_own = mem::take(exp);
        *exp = Exp::Let(bindings.into_boxed_slice(), Box::new(exp_own))
    }
}

fn subst_pred(pred: &mut Predicate, var_map: &impl Fn(&Ident) -> Predicate) {
    let recur = |pred| subst_pred(pred, var_map);
    match pred {
        Predicate::Res | Predicate::Lit(_) => {}
        Predicate::Not(box [x]) => recur(x),
        Predicate::If(box preds) => preds.iter_mut().for_each(recur),
        Predicate::Var(v) => *pred = var_map(v),
        Predicate::Op(box (_, pred1, pred2)) => {
            recur(pred1);
            recur(pred2)
        }
    }
}

pub fn subst_ty(ty: &mut Type, var_map: &impl Fn(&Ident) -> Predicate) {
    match ty {
        Type::Refined(box (ty, pred)) => {
            subst_ty(ty, var_map);
            subst_pred(pred, var_map)
        }
        Type::Fun(box (_, arg_ty, res_ty)) => {
            subst_ty(arg_ty, var_map);
            subst_ty(res_ty, var_map);
        }
        Type::Forall(box (_, ty)) => subst_ty(ty, var_map),
        Type::Var(_) | Type::Base(_) => {}
    }
}

fn anf_translate_ty(ty: &mut Type, var_map: &AHashMap<Ident, Ident>) {
    subst_ty(ty, &|id| {
        Predicate::Var(var_map.get(id).unwrap_or(id).clone())
    })
}

fn anf_translate_bindings(
    exp: &mut Exp,
    var_map: &mut SPHashMap<Ident, Ident>,
    bindings: &mut Vec<(Ident, Exp)>,
    fresh: &mut Fresh,
) {
    match exp {
        Exp::Lit(_) => {}
        Exp::Var(id) => {
            if let Some(id2) = var_map.get(id) {
                *id = id2.clone();
            }
        }
        Exp::Lambda(_, box exp) => anf_translate_h(exp, var_map),
        Exp::Inst(..) => {
            let Exp::Inst(box mut curr, tys) = mem::take(exp) else {
                unreachable!()
            };
            let tys = Vec::from(tys).into_iter();
            anf_translate_bindings(&mut curr, var_map, bindings, fresh);
            lift_to_let(bindings, fresh, &mut curr);
            for ty in tys {
                lift_to_let(bindings, fresh, &mut curr);
                curr = Exp::Inst(Box::new(curr), Box::new([ty]))
            }
            *exp = curr
        }
        Exp::App(box []) => {}
        Exp::App(_) => {
            let Exp::App(args) = mem::take(exp) else {
                unreachable!()
            };
            let mut args = Vec::from(args).into_iter();
            let mut curr = args.next().unwrap();
            anf_translate_bindings(&mut curr, var_map, bindings, fresh);
            for mut arg in args {
                lift_to_let(bindings, fresh, &mut curr);
                anf_translate_bindings(&mut arg, var_map, bindings, fresh);
                lift_to_let(bindings, fresh, &mut arg);
                curr = Exp::App(Box::new([curr, arg]))
            }
            *exp = curr
        }
        Exp::Ascribe(box (exp, ty)) => {
            anf_translate_ty(ty, &*var_map);
            anf_translate_h(exp, var_map)
        }
        exp @ Exp::Let(..) => {
            let Exp::Let(mut src_bindings, box inner_exp) = mem::take(exp) else {
                panic!()
            };
            *exp = inner_exp;
            anf_translate_let(&mut *src_bindings, exp, var_map, bindings, fresh)
        }
        Exp::Letrec(box bindings, exp) => {
            bindings.iter_mut().for_each(|(_, exp, ty)| {
                anf_translate_ty(ty, &*var_map);
                anf_translate_h(exp, var_map);
            });
            anf_translate_h(exp, var_map)
        }
        Exp::If(box [i, t, e]) => {
            anf_translate_bindings(i, var_map, bindings, fresh);
            lift_to_let(bindings, fresh, i);
            anf_translate(t);
            anf_translate(e);
        }
    }
}

fn lift_to_let(bindings: &mut Vec<(Ident, Exp)>, fresh: &mut Fresh, exp: &mut Exp) {
    if !matches!(exp, Exp::Var(_) | Exp::Lit(_) | Exp::Lambda(..)) {
        let fresh_var = fresh.fresh();
        let old_arg = mem::replace(exp, Exp::Var(fresh_var.clone()));
        bindings.push((fresh_var, old_arg));
    }
}

fn anf_translate_let(
    src: &mut [(Ident, Exp)],
    exp: &mut Exp,
    var_map: &mut SPHashMap<Ident, Ident>,
    dst: &mut Vec<(Ident, Exp)>,
    fresh: &mut Fresh,
) {
    match src {
        [] => anf_translate_bindings(exp, var_map, dst, fresh),
        [(id, Exp::Var(id2)), rest @ ..] => {
            let var_map =
                &mut *var_map.insert_sp(id.clone(), var_map.get(id2).unwrap_or(id2).clone());
            anf_translate_let(rest, exp, var_map, dst, fresh)
        }
        [(id, id_exp), rest @ ..] => {
            anf_translate_bindings(id_exp, var_map, dst, fresh);
            let fresh_id = fresh.fresh_id(id);
            dst.push((fresh_id.clone(), mem::take(id_exp)));
            let var_map = &mut *var_map.insert_sp(id.clone(), fresh_id);
            anf_translate_let(rest, exp, var_map, dst, fresh)
        }
    }
}
