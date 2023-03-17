use serde_lexpr::from_str;

mod semi_persistent;
mod fmt;
mod defs;
mod ty_check;
mod simpl;

use ty_check::type_check;
use simpl::*;
use crate::defs::{Exp, TypeDefs};


#[test]
fn test() {
    assert_eq!(type_check(&exp!((proj 0 (as (tuple (tuple)) (x (x)))))), Ok(&ty!((x))));
    assert_eq!(type_check(&exp!((app (as (lambda "x" (var . "x")) (fun (x) (x))) (tuple)))), Ok(&ty!((x))));
    exp!((tuple))
}

fn main () {
    let mut buf = String::new();
    let mut exp = Exp::default();
    let mut defs = TypeDefs::new();
    defs.insert("Unit", ty!((x))).unwrap();
    defs.insert("Never", ty!((sum))).unwrap();
    defs.insert("Bool", ty!((sum (def . "Unit") (def . "Unit")))).unwrap();
    defs.insert("Nat", ty!((sum (def . "Unit") (def . "Nat")))).unwrap();
    defs.insert("Omega", ty!((fun (def . "Omega") (def . "Never")))).unwrap();
    loop {
        println!("{exp:#?}");
        std::io::stdin().read_line(&mut buf).unwrap_or_default();
        match &*buf {
            "check\n" => println!("{:?}", type_check(&exp, &defs)),
            "simpl_match\n" => resolve_never(simpl_match(&mut exp, &defs)),
            "simpl_proj\n" => resolve_never(simpl_proj(&mut exp, &defs)),
            "simpl_app\n" => resolve_never(simpl_app(&mut exp, &defs)),
            "simpl\n" => resolve_never(simpl(&mut exp, &defs)),
            "erase\n" => resolve_never(erase(&mut exp)),
            "eval\n" => resolve_never(eval(&mut exp, &defs)),
            "simpl_step\n" => resolve_step(simpl_step(&mut exp, &defs)),
            "step\n" => resolve_step(step(&mut exp, &defs)),
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