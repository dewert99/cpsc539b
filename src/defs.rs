use serde::{Deserialize, Serialize};
use smallstr::SmallString;

pub type Ident = SmallString<[u8; 16]>;

#[derive(Serialize, Deserialize, Clone)]
#[serde(untagged)]
pub enum Lit {
    Bool(bool),
    Int(i32),
}

#[derive(Serialize, Deserialize, Copy, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum PrimOp {
    #[serde(alias = "+")]
    #[serde(rename(serialize = "+"))]
    Add,
    #[serde(alias = "-")]
    #[serde(rename(serialize = "-"))]
    Sub,
    #[serde(alias = "<=")]
    #[serde(rename(serialize = "<="))]
    Le,
    #[serde(alias = "=")]
    #[serde(rename(serialize = "="))]
    Eq,
    #[serde(alias = "&&")]
    #[serde(rename(serialize = "&&"))]
    And,
    #[serde(alias = "||")]
    #[serde(rename(serialize = "||"))]
    Or,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum Predicate {
    Res,
    #[serde(alias = "!")]
    #[serde(rename(serialize = "!"))]
    Not(Box<[Predicate; 1]>),
    If(Box<[Predicate; 3]>),
    #[serde(untagged)]
    Var(Ident),
    #[serde(untagged)]
    Lit(Lit),
    #[serde(untagged)]
    Op(Box<(PrimOp, Predicate, Predicate)>),
}

#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Debug)]
#[serde(rename_all = "kebab-case")]
pub enum BaseType {
    Int,
    Bool,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum Type {
    #[serde(alias = ":")]
    #[serde(rename(serialize = ":"))]
    Refined(BaseType, Box<Predicate>), // The value variable is always Res
    #[serde(alias = "->")]
    #[serde(rename(serialize = "->"))]
    Fun(Box<(Ident, Type, Type)>),
    #[serde(alias = "∀")]
    #[serde(rename(serialize = "∀"))]
    Forall(Box<(Ident, Type)>),
    #[serde(untagged)]
    Var(Ident)
}

pub use Type::*;

#[derive(Serialize, Deserialize, Clone)]
#[serde(rename_all = "kebab-case")]
pub enum Exp {
    #[serde(alias = "λ")]
    #[serde(rename(serialize = "λ"))]
    Lambda(Box<[Ident]>, Box<Exp>),
    #[serde(alias = "as")]
    #[serde(rename(serialize = "as"))]
    Ascribe(Box<(Exp, Type)>),
    Let(Box<[(Ident, Exp)]>, Box<Exp>),
    Letrec(Box<[(Ident, Exp, Type)]>, Box<Exp>),
    If(Box<[Exp; 3]>),
    #[serde(untagged)]
    App(Box<[Exp]>),
    #[serde(untagged)]
    Lit(Lit),
    #[serde(untagged)]
    Var(Ident),
}

impl Default for Exp {
    fn default() -> Self {
        Exp::Var(Ident::default())
    }
}

#[macro_export]
macro_rules! exp {
    ($t:tt) => {
        serde_lexpr::from_value::<crate::defs::Exp>(&lexpr::sexp!($t)).unwrap()
    };
}

#[macro_export]
macro_rules! ty {
    ($t:tt) => {serde_lexpr::from_value::<crate::defs::Type>(&lexpr::sexp!($t)).unwrap()}
}

pub use Exp::*;
