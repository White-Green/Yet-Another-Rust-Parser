use std::collections::{BTreeMap, HashMap};
use std::convert::TryFrom;
use std::ops::Deref;

use crate::CharRange;
use crate::dfa::{DFAConstructWarning, TokenizerDFA};
use crate::nfa::{NFARegexConstructError, TokenizerNFA};
use crate::tokenizer::iter::Tokenizer;

pub(crate) mod iter;

pub struct DFATokenizer<E, T> {
    goto: Vec<BTreeMap<CharRange, usize>>,
    begin: usize,
    end: HashMap<usize, usize>,
    enum_maker: Vec<Box<dyn Fn(&str, Vec<T>) -> E>>,
}

impl<E, T> Tokenizer for DFATokenizer<E, T> {
    type Input = T;
    type Output = E;
    fn begin(&self) -> usize { self.begin }
    fn accept_index(&self, node: usize) -> Option<usize> { self.get_accept_index(node) }
    fn next_node(&self, node: usize, token: char) -> Option<usize> { self.get_next_node(node, token) }
    fn enum_maker(&self, pattern: usize) -> &dyn Fn(&str, Vec<T>) -> E { &self.enum_maker[pattern] }
}

impl<E, T> Tokenizer for &DFATokenizer<E, T> {
    type Input = T;
    type Output = E;
    fn begin(&self) -> usize { self.begin }
    fn accept_index(&self, node: usize) -> Option<usize> { self.get_accept_index(node) }
    fn next_node(&self, node: usize, token: char) -> Option<usize> { self.get_next_node(node, token) }
    fn enum_maker(&self, pattern: usize) -> &dyn Fn(&str, Vec<T>) -> E { &self.enum_maker[pattern] }
}

impl<E, T> DFATokenizer<E, T> {
    pub(crate) fn new(dfa: TokenizerDFA, enum_maker: Vec<Box<dyn Fn(&str, Vec<T>) -> E>>) -> Self {
        let index_map: HashMap<_, _> = dfa.node.iter().enumerate().map(|(i, node)| (node.reference(), i)).collect();
        let goto = dfa.node.iter().map(|node| node.next_map().iter().map(|(range, node)| (range.clone(), index_map[node])).collect()).collect();
        let begin = index_map[&dfa.begin];
        let end = dfa.end.iter().map(|(node, end)| (index_map[node], *end)).collect();
        Self { goto, begin, end, enum_maker }
    }

    pub(crate) fn get_accept_index(&self, node: usize) -> Option<usize> {
        self.end.get(&node).copied()
    }

    pub(crate) fn get_next_node(&self, node: usize, token: char) -> Option<usize> {
        let token = token as u32;
        self.goto[node].range(..=token).next_back().and_then(|(range, node_ref)| if token < range.range.end { Some(*node_ref) } else { None })
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
    patterns: Vec<(String, Box<dyn Fn(&str, Vec<T>) -> E>)>,
}

impl<E, T> TokenizerBuilder<E, T> {
    pub fn new() -> Self {
        Self { patterns: Vec::new() }
    }

    pub fn pattern<F: 'static + Fn(&str, Vec<T>) -> E>(mut self, regex: &str, f: F) -> Self {
        self.patterns.push((regex.to_string(), Box::new(f)));
        self
    }

    pub fn build(self) -> Result<(DFATokenizer<E, T>, Vec<TokenizerBuildWarning>), TokenizerBuildError> {
        let (regex, functions): (Vec<_>, Vec<_>) = self.patterns.into_iter().unzip();
        let nfa = TokenizerNFA::try_from(regex.iter().map(|s| s.deref()).collect::<Vec<&str>>()).map_err(|e| TokenizerBuildError::NFAConstructError(e))?;
        let (dfa, warnings) = nfa.into();
        let dfa = dfa.minify();
        Ok((DFATokenizer::new(dfa, functions), warnings.into_iter().map(|i| TokenizerBuildWarning::DFAConstructWarning(i)).collect()))
    }
}
