use crate::defs::{Exp, Ident};
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
        Exp::App(box []) => {},
        Exp::App(box [f, args @ ..]) => {
            anf_translate_bindings(f, var_map, bindings, fresh);
            for arg in args {
                anf_translate_bindings(arg, var_map, bindings, fresh);
                if !matches!(arg, Exp::Var(_)) {
                    let fresh_var = fresh.fresh();
                    let old_arg = mem::replace(arg, Exp::Var(fresh_var.clone()));
                    bindings.push((fresh_var, old_arg));
                }
            }
        }
        Exp::Ascribe(box (exp, _)) => anf_translate_h(exp, var_map),
        exp @ Exp::Let(..) => {
            let Exp::Let(mut src_bindings, box inner_exp) = mem::take(exp) else {
                panic!()
            };
            *exp = inner_exp;
            anf_translate_let(&mut *src_bindings, exp, var_map, bindings, fresh)
        }
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
