#![feature(box_patterns)]
#![feature(assert_matches)]

mod anf;
mod ctxt;
mod defs;
mod error_reporting;
mod ty_check;
mod util;

use crate::ctxt::{make_context, make_tcx};
use defs::Exp;
use serde_lexpr::from_str;
use std::assert_matches::assert_matches;
use ty_check::TypeError::*;

macro_rules! test_ty_check_result {
    ($name:ident, $t:tt, $expect:pat) => {
        #[test]
        fn $name() {
            let mut exp = exp!($t);
            anf::anf_translate(&mut exp);
            let ctx = make_context();
            let mut tcx = make_tcx(&ctx, true);
            let res = dbg!(ty_check::type_check(dbg!(&exp), &mut tcx));
            assert_matches!(res, $expect)
        }
    };
}

macro_rules! test_ty_check {
    ($name:ident, $t:tt) => {
        test_ty_check_result! {$name, $t, Ok(_)}
    };
}

test_ty_check! {test1, (as ("add" 1) (-> "z" (: int #t) (: int (<= "z" res))))}
test_ty_check_result! {test2, (as ("add" ("add" 1 1)) (-> "z" (: int #t) (: int (<= res "z")))), Err(SubType{..})}
test_ty_check! {test3, (as (λ ("f" "x") ("f" ("f" "x"))) (-> "f" (-> "x" (: int #t) (: int (<= "x" res))) (-> "x" (: int #t) (: int (<= "x" res)))))}
test_ty_check! {test4, (as (λ ("f" "x") ("f" ("f" "x"))) (-> "f" (-> "x" (: int (<= 0 res)) (: int (<= "x" res))) (-> "x" (: int (<= 0 res)) (: int (<= "x" res)))))}
test_ty_check! {test5,
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
test_ty_check!(poly_id, (as (λ ("x") "x") (forall "X" (-> "x" "X" "X"))));
test_ty_check_result!(poly_bad, (as (λ ("x" "y") "x") (forall "X" (-> "x" "X" (forall "X" (-> "y" "X" "X"))))),
    Err(PredIllFormed(..)));
test_ty_check!(poly_sub, (as (let (("x" (as (λ ("x") "x") (forall "X" (-> "x" "X" "X"))))) "x") (forall "Y" (-> "y" "Y" "Y"))));
test_ty_check!(poly_sub2, (as (as (λ ("y" "x") "x") (forall "Y" (-> "y" "Y" (forall "X" (-> "x" "X" "X")))))
                            (forall "X" (-> "x" "X" (forall "Y" (-> "y" "Y" "Y"))))));
test_ty_check!(self_app, (as (λ ("id") ((inst "id" ((forall "X" (-> "x" "X" "X")))) "id")) (-> "id" (forall "X" (-> "x" "X" "X")) (forall "X" (-> "x" "X" "X")))));

test_ty_check!(test_shadow, (as (let (("x" (as (λ ("x" "x") "x") (-> "x" (: int #t) (-> "x" (: int #t) (: int (= res "x"))))))) ("x" 0))
    (-> "x" (: int #t) (: int (= res "x")))));

test_ty_check_result!(test_shadow_bad, (as (let (("x" (as (λ ("x" "x") "x") (-> "x" (: int #t) (-> "x" (: int #t) (: int (= res "x"))))))) ("x" 0))
    (-> "x" (: int #t) (: int (= res 0)))), Err(SubType{..}));

test_ty_check!(test_dep_pair, (as (λ ("f") ("f" 0 1))
    (forall "X" (-> "f" (-> "x" (: int #t) (-> "y" (: int (<= "x" res)) "X")) "X"))));

test_ty_check!(test_use_dep_pair, (as
    ((as (λ ("p") ((inst "p" ((: int (<= res 0)))) "sub"))
        (-> "p" (forall "X" (-> "f" (-> "x" (: int #t) (-> "y" (: int (<= "x" res)) "X")) "X"))
            (: int (<= res 0))))
     (as (λ ("f") ("f" 0 1)) (forall "X" (-> "f" (-> "x" (: int (= res 0)) (-> "y" (: int (= res 1)) "X")) "X"))))
 (: int (<= res 0))));

test_ty_check!(test_bind_inst,
    (as (let (("id" (as (λ ("x") "x") (forall "X" (-> "x" "X" "X"))))
              ("one" ((inst "id" ((: int (= res 1)))) 1)))
          "one") (: int (= res 1))));

test_ty_check!(test_sum, (as (λ ("b" "l" "r") (if "b" (λ ("f" "g") ("f" "l")) (λ ("f" "g") ("g" "r"))))
 (forall "X" (forall "Y" (-> "b" bool (-> "l" "X" (-> "r" "Y" (forall "Z" (-> "f" (-> "x" (: "X" "b") "Z") (-> "g" (-> "y" (: "Y" (! "b")) "Z") "Z"))))))))));

test_ty_check!(test_sum2, (as (let (
    ("mk_sum" (as (λ ("b" "l" "r" "f" "g") (if "b" ("f" "l") ("g" "r")))
        (forall "X" (forall "Y" (-> "b" bool (-> "l" "X" (-> "r" "Y" (forall "Z" (-> "f" (-> "x" (: "X" "b") "Z") (-> "g" (-> "y" (: "Y" (! "b")) "Z") "Z"))))))))))
    ("mk_sum_i" (inst "mk_sum" ((-> "x" int (: int (= res (+ "x" 1)))) (-> "x" int (: int (= res (sub 0 "x")))))))
    ("s1" ("mk_sum_i" #t ("add" 1) ("sub" 0)))
    ("s2" ("mk_sum_i" #f ("add" 1) ("sub" 0)))
    ("h" (as (λ ("l") ("l" 5)) (-> "l" (-> "x" int (: int (= res (+ "x" 1)))) (: int (= res 6)))))
    ("r1" ((inst "s1" ((: int (= res 6)))) "h" "h"))
    ("r2" ((inst "s2" ((: int (= res -5)))) (as (λ ("l") 10) (-> "l" (: (-> "x" int int) #f) (: int (= res (sub 0 5))))) (as (λ ("l") ("l" 5)) (-> "l" (-> "x" int (: int (= res (sub 0 "x")))) (: int (= res (sub 0 5)))))))
) ("add" "r1" "r2")) (: int (= res 1))));

// #[test]
// fn debug() {
//     let mut exp = exp!( (as (λ ("x" "y") "x") (forall "X" (-> "x" "X" (forall "X" (-> "y" "X" "X"))))) );
//     anf::anf_translate(&mut exp);
//     let ctx = make_context();
//     let mut tcx = make_tcx(&ctx);
//     let res = ty_check::infer_type(dbg!(&exp), &mut tcx).map(|_| ());
//     assert_matches!( res , Ok ( _ ) )
// }

fn main() {
    let mut buf = String::new();
    let mut exp = Exp::default();
    let context = make_context();
    let tyctx = |v| make_tcx(&context, v);
    loop {
        println!("{exp:?}");
        std::io::stdin().read_line(&mut buf).unwrap_or_default();
        match &*buf {
            "anf\n" => anf::anf_translate(&mut exp),
            "check\n" => println!("{:#?}", ty_check::type_check(&exp, &mut tyctx(false))),
            "vcheck\n" => println!("{:#?}", ty_check::type_check(&exp, &mut tyctx(true))),
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
