#![feature(box_patterns)]
#![feature(assert_matches)]

mod anf;
mod ctxt;
mod defs;
mod error_reporting;
mod ty_check;
mod util;

use std::assert_matches::assert_matches;
use crate::ctxt::{make_context, make_tcx};
use defs::Exp;
use serde_lexpr::from_str;
use ty_check::TypeError::*;


macro_rules! test_ty_check_result {
    ($name:ident, $t:tt, $expect:pat) => {
        #[test]
        fn $name() {
            let mut exp = exp!($t);
            anf::anf_translate(&mut exp);
            let ctx = make_context();
            let mut tcx = make_tcx(&ctx);
            let res = ty_check::infer_type(dbg!(&exp), &mut tcx);
            assert_matches!(res, $expect)
        }
    };
}

macro_rules! test_ty_check {
    ($name:ident, $t:tt) => {
        test_ty_check_result!{$name, $t, Ok(_)}
    };
}

test_ty_check!{test1, (as ("add" 1) (-> "y" (: int #t) (: int (<= "y" res))))}
test_ty_check_result!{test2, (as ("add" ("add" 1 1)) (-> "y" (: int #t) (: int (<= res "y")))), Err(SubType{..})}
test_ty_check!{test3, (as (λ ("f" "x") ("f" ("f" "x"))) (-> "f" (-> "x" (: int #t) (: int (<= "x" res))) (-> "x" (: int #t) (: int (<= "x" res)))))}
test_ty_check!{test4, (as (λ ("f" "x") ("f" ("f" "x"))) (-> "f" (-> "x" (: int (<= 0 res)) (: int (<= "x" res))) (-> "x" (: int (<= 0 res)) (: int (<= "x" res)))))}
test_ty_check!{test5,
    (as (let (("f" (as (λ ("f" "x") ("f" ("f" "x"))) (-> "f" (-> "x" (: int (<= 0 res)) (: int (<= "x" res))) (-> "x" (: int (<= 0 res)) (: int (<= "x" res)))))))
          ("f" ("add" 1) 0))
      (: int (<= 0 res)))}
test_ty_check!(test6, (as (λ ("x") (if "x" (if "x" #t #f) #t)) (-> "x" (: bool #t) (: bool res))));
test_ty_check!(test_abs, (as (λ ("x") (if ("le" "x" 0) ("sub" 0 "x") "x")) (-> "x" (: int #t) (: int (<= 0 res)))));
test_ty_check!(test_let_bound_in_refinement, (as (let (("x" #t)) (as 0 (: int "x"))) (: int #t)));
test_ty_check!(test_add_slow,
    (as (letrec
          (("adds"
              (λ ("x" "y") (if ("eq" "x" 0) "y" ("adds" ("sub" "x" 1) ("add" 1 "y"))))
              (-> "x" (: int (<= 0 res)) (-> "y" (: int #t) (: int (= res (+ "x" "y")))))))
         ("adds" 2 2))
    (: int (= res 4))));
test_ty_check!(test_inf_loop,
    (as (letrec
          (("ping" (λ ("x") ("pong" "x")) (-> "x" (:bool #t) (: bool #f)))
           ("pong" (λ ("x") ("ping" "x")) (-> "x" (:bool #t) (: bool #f))))
         ("ping" #t))
    (: bool #f)));
test_ty_check_result!(test_bad_rec, (as (letrec (("bad" #t (: bool #f))) #t) (: bool #f)), Err(NotFun(..)));

fn main() {
    let mut buf = String::new();
    let mut exp = Exp::default();
    let context = make_context();
    let tyctx = || make_tcx(&context);
    loop{
        println!("{exp:?}");
        std::io::stdin().read_line(&mut buf).unwrap_or_default();
        match &*buf {
            "anf\n" => anf::anf_translate(&mut exp),
            "check\n" => println!("{:#?}", ty_check::infer_type(&exp, &mut tyctx())),
            x if x.trim().chars().all(char::is_numeric) => {
                let x = x.trim().parse().unwrap();
                buf.clear();
                for _ in 0..x {
                    std::io::stdin().read_line(&mut buf).unwrap_or_default();
                }
                match from_str(&buf) {
                    Ok(x) => exp = x,
                    Err(e) => eprintln!("{e:?}"),
                }
            }
            _ => match from_str(&buf) {
                Ok(x) => exp = x,
                Err(e) => eprintln!("{e:?}"),
            },
        }
        buf.clear()
    }
}
