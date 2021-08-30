use std::fmt::Debug;

pub use enum_index;
pub use enum_index_derive;

pub use crate::iter::{Parse, ParseError};
pub use crate::parser::{Action, LR1Parser};
pub use crate::syntax::{Rule, Syntax, TerminalSymbol};

mod iter;
mod parser;
mod syntax;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol<N, T, E> {
    NonTerminal(N),
    Terminal(T),
    Error(E),
}
