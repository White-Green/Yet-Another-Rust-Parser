use std::fmt::Debug;

pub use enum_index::*;
pub use enum_index_derive::*;

pub use crate::syntax::{Rule, Syntax};

mod parser;
mod syntax;
mod iter;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol<N, T> {
    NonTerminal(N),
    Terminal(T),
    Error,
}
