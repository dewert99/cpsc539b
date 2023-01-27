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


pub use Type::*;

#[derive(Serialize, Deserialize, Eq, PartialEq)]
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
}


macro_rules! exp {
    ($t:tt) => {serde_lexpr::from_value::<Exp>(&lexpr::sexp!($t)).unwrap()}
}

macro_rules! ty {
    ($t:tt) => {serde_lexpr::from_value::<Type>(&lexpr::sexp!($t)).unwrap()}
}

pub use Exp::*;

