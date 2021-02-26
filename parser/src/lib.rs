use std::fmt::Debug;

pub use enum_index::*;
pub use enum_index_derive::*;

pub use crate::syntax::{Rule, Syntax};

mod parser;
mod syntax;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Symbol<N, T> {
    NonTerminal(N),
    Terminal(T),
}

// pub trait EnumIndex: Sized {
//     fn enum_index(&self) -> usize;
//     fn default_from_number(number: usize) -> Option<Self>;
// }
