use std::collections::hash_map::Entry;
use ahash::AHashMap;
use smallstr::SmallString;
use serde::{Serialize, Deserialize};

pub type Ident = SmallString<[u8; 16]>;

#[derive(Serialize, Deserialize, Clone, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum Type {
    #[serde(alias = "+")]
    #[serde(rename(serialize = "+"))]
    Sum(Box<[Type]>),
    #[serde(alias = "x")]
    #[serde(rename(serialize = "x"))]
    Prod(Box<[Type]>),
    #[serde(alias = "->")]
    #[serde(rename(serialize = "->"))]
    Fun(Box<[Type; 2]>),
    Def(Ident),
}

pub struct TypeDefs(AHashMap<Ident, Type>);

impl TypeDefs {
    pub fn insert(&mut self, id: &str, ty: Type) -> Result<(), ()> {
        match self.0.entry(id.into()) {
            Entry::Occupied(_) => Err(()),
            Entry::Vacant(vac) => {
                vac.insert(ty);
                Ok(())
            }
        }
    }

    pub fn resolve<'a>(&'a self, ty: &'a Type) -> &'a Type {
        match ty {
            Def(id) => self.0.get(id).unwrap_or(ty), // Treat undefined type-defs opaquely
            _ => ty
        }
    }

    pub fn new() -> Self {
        TypeDefs(AHashMap::new())
    }
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

