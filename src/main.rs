#![feature(box_patterns)]

use serde_lexpr::from_str;

mod tenv;
mod fmt;
mod defs;
mod ty_check;
mod simpl;

use ty_check::type_check;
use simpl::*;
use crate::defs::Exp;


#[test]
fn test() {
    assert_eq!(type_check(&exp!((proj 0 (as (tuple (tuple)) (x (x)))))), Ok(&ty!((x))));
    assert_eq!(type_check(&exp!((app (as (lambda "x" (var . "x")) (fun (x) (x))) (tuple)))), Ok(&ty!((x))));
    exp!((lambda "x" ($ (var . "f") (lambda "v" ($ ($ (var . "x") (var . "x")) (var . "v"))))))
}

fn main () {
    let mut buf = String::new();
    let mut exp = Exp::default();
    loop {
        println!("{exp:#?}");
        std::io::stdin().read_line(&mut buf).unwrap_or_default();
        match &*buf {
            "check\n" => println!("{:?}", type_check(&exp)),
            "simpl_match\n" => resolve_never(simpl_match(&mut exp)),
            "simpl_proj\n" => resolve_never(simpl_proj(&mut exp)),
            "simpl_app\n" => resolve_never(simpl_app(&mut exp)),
            "simpl\n" => resolve_never(simpl(&mut exp)),
            "erase\n" => resolve_never(erase(&mut exp)),
            "eval\n" => resolve_never(eval(&mut exp)),
            "simpl_step\n" => resolve_step(simpl_step(&mut exp)),
            "step\n" => resolve_step(step(&mut exp)),
            "collapse_let\n" => collapse_lets(&mut exp),
            x if x.trim().chars().all(char::is_numeric) => {
                let x = x.trim().parse().unwrap();
                buf.clear();
                for _ in 0..x {
                    std::io::stdin().read_line(&mut buf).unwrap_or_default();
                }
                match from_str(&buf) {
                    Ok(x) => exp = x,
                    Err(e) => eprintln!("{e:?}")
                }
            }
            _ => match from_str(&buf) {
                Ok(x) => exp = x,
                Err(e) => eprintln!("{e:?}")
            }
        }
        buf.clear()
    }
}