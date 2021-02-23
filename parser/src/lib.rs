use std::fmt::Debug;

pub use crate::syntax::{Rule, Syntax};

mod parser;
mod syntax;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Symbol<N, T> {
    NonTerminal(N),
    Terminal(T),
}

pub trait NumberMapped: Sized {
    fn get_number(&self) -> usize;
    fn default_from_number(number: usize) -> Option<Self>;
}
