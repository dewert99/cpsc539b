#![feature(box_patterns)]

use serde_lexpr::from_str;

mod tenv;
mod fmt;
mod defs;
mod ty_check;
use ty_check::type_check;


#[test]
fn test() {
    assert_eq!(type_check(&mut exp!((proj 0 (as (tuple (tuple)) (x (x)))))), Ok(&ty!((x))));
    assert_eq!(type_check(&mut exp!((app (as (lambda "x" (var . "x")) (fun (x) (x))) (tuple)))), Ok(&ty!((x))));
}

fn main () {
    let mut buf = String::new();
    loop {
        std::io::stdin().read_line(&mut buf).unwrap_or_default();
        match from_str(&buf) {
            Ok(x) => println!("{:?}", type_check(&x)),
            Err(e) => eprintln!("{e:?}")
        }
        buf.clear()
    }
}