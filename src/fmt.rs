use std::fmt::{Debug, Formatter};
use core::mem;
use lexpr::{Cons, Value};
use serde::Serialize;
use crate::defs::{Exp, Type};

pub fn fix_lexpr_value(v: &mut Value) {
    match v {
        Value::String(_) => {
            match mem::replace(v, Value::Nil) {
                Value::String(s) => *v = Value::Symbol(s),
                _ => unreachable!()
            }
        }
        Value::Cons(c) => {
            fix_lexpr_value(c.car_mut());
            fix_lexpr_value(c.cdr_mut());
        }
        Value::Vector(_) => {
            match mem::replace(v, Value::Nil) {
                Value::Vector(vec) => *v = {
                    vec.into_vec().into_iter().rfold(Value::Null, |acc, mut x| {
                        fix_lexpr_value(&mut x);
                        Value::Cons(Cons::new(x, acc))
                    })
                },
                _ => unreachable!()
            }
        }
        _ => ()
    }
}

pub fn to_value_better<T>(value: &T) -> Value
    where
        T: Serialize,
{
    let mut value = serde_lexpr::to_value(value).unwrap();
    fix_lexpr_value(&mut value);
    value
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", to_value_better(self))
    }
}

impl Debug for Exp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", to_value_better(self))
    }
}