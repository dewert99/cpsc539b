use smallstr::SmallString;
use serde::{Serialize, Deserialize};

pub type Ident = SmallString<[u8; 16]>;

#[derive(Serialize, Deserialize, Clone, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum Type {
    #[serde(rename = "+")]
    Sum(Box<[Type]>),
    #[serde(rename = "x")]
    Prod(Box<[Type]>),
    #[serde(alias = "->")]
    #[serde(rename(serialize = "->"))]
    Fun(Box<[Type; 2]>),
}

impl Default for Type {
    fn default() -> Self {
        Prod(Box::new([]))
    }
}


pub use Type::*;

#[derive(Serialize, Deserialize, Eq, PartialEq, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum Exp {
    #[serde(alias = "λ")]
    #[serde(rename(serialize = "λ"))]
    Lambda(Box<(Ident, Exp)>),
    Var(Ident),
    #[serde(alias = "$")]
    #[serde(rename(serialize = "$"))]
    App(Box<[Exp; 2]>),
    #[serde(alias = "as")]
    #[serde(rename(serialize = "as"))]
    Ascribe(Box<(Exp, Type)>),
    Tuple(Box<[Exp]>),
    Proj(usize, Box<Exp>),
    Inj(usize, Box<Exp>),
    Match(Box<Exp>, Box<[(Ident, Exp)]>),
    Fix(Box<(Ident, Exp)>),
    Let(Box<[(Ident, Exp)]>, Box<Exp>)
}

impl Default for Exp {
    fn default() -> Self {
        Var(Ident::default())
    }
}

#[macro_export]
macro_rules! exp {
    ($t:tt) => {serde_lexpr::from_value::<crate::defs::Exp>(&lexpr::sexp!($t)).unwrap()}
}

#[macro_export]
macro_rules! ty {
    ($t:tt) => {serde_lexpr::from_value::<crate::defs::Type>(&lexpr::sexp!($t)).unwrap()}
}


pub use Exp::*;

