use std::convert::TryFrom;
use std::ops::Deref;

use crate::dfa::{DFAConstructWarning, TokenizerDFA};
use crate::nfa::{NFARegexConstructError, TokenizerNFA};

pub(crate) mod iter;

pub struct Tokenizer<'a, E, T> {
    dfa: TokenizerDFA<'a>,
    enum_maker: Vec<Box<dyn FnMut(&str, Vec<T>) -> E>>,
}

impl<'a, E, T> Tokenizer<'a, E, T> {
    pub(crate) fn new(dfa: TokenizerDFA<'a>, enum_maker: Vec<Box<dyn FnMut(&str, Vec<T>) -> E>>) -> Self {
        Self { dfa, enum_maker }
    }

    pub fn builder() -> TokenizerBuilder<E, T> {
        TokenizerBuilder::new()
    }
}

#[derive(Debug, Clone)]
pub enum TokenizerBuildError {
    NFAConstructError(NFARegexConstructError)
}

#[derive(Debug, Clone)]
pub enum TokenizerBuildWarning {
    DFAConstructWarning(DFAConstructWarning)
}

pub struct TokenizerBuilder<E, T> {
    patterns: Vec<(String, Box<dyn FnMut(&str, Vec<T>) -> E>)>,
}

impl<E, T> TokenizerBuilder<E, T> {
    pub fn new() -> Self {
        Self { patterns: Vec::new() }
    }

    pub fn add_pattern<F: 'static + FnMut(&str, Vec<T>) -> E>(mut self, regex: &str, f: F) -> Self {
        self.patterns.push((regex.to_string(), Box::new(f)));
        self
    }

    pub fn build<'a>(self) -> Result<(Tokenizer<'a, E, T>, Vec<TokenizerBuildWarning>), TokenizerBuildError> {
        let (regex, functions): (Vec<_>, Vec<_>) = self.patterns.into_iter().unzip();
        let nfa = TokenizerNFA::try_from(regex.iter().map(|s| s.deref()).collect::<Vec<&str>>()).map_err(|e| TokenizerBuildError::NFAConstructError(e))?;
        let (dfa, warnings) = nfa.into();
        let dfa = dfa.minify();
        Ok((Tokenizer::new(dfa, functions), warnings.into_iter().map(|i| TokenizerBuildWarning::DFAConstructWarning(i)).collect()))
    }
}
