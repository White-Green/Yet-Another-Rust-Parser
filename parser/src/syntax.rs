use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::{EnumIndex, Symbol};

#[derive(Debug, PartialEq)]
pub struct Syntax<N, T> {
    pub(crate) rules: Vec<Rule<N, T>>,
    pub(crate) start: usize,
}

impl<N: EnumIndex, T: EnumIndex> Syntax<N, T> {
    pub fn builder() -> SyntaxBuilder<N, T> {
        Default::default()
    }
}

#[derive(Debug, PartialEq)]
pub struct SyntaxBuilder<N, T> {
    rules: Vec<Rule<N, T>>,
}

impl<N, T> Default for SyntaxBuilder<N, T> {
    fn default() -> Self {
        Self { rules: Vec::new() }
    }
}

impl<N: EnumIndex, T: EnumIndex> SyntaxBuilder<N, T> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn rule(mut self, rule: Rule<N, T>) -> Self {
        self.rules.push(rule);
        self
    }

    pub fn build(self, start: N) -> Syntax<N, T> {
        let SyntaxBuilder { rules } = self;
        Syntax {
            rules,
            start: start.enum_index(),
        }
    }
}


#[derive(Debug)]
pub struct Rule<N, T> {
    pub(crate) non_terminal: usize,
    pub(crate) symbols: Vec<Symbol<usize, TerminalSymbol<usize>>>,
    phantom: PhantomData<(N, T)>,
}

impl<N, T> Clone for Rule<N, T> {
    fn clone(&self) -> Self {
        Rule {
            non_terminal: self.non_terminal.clone(),
            symbols: self.symbols.clone(),
            phantom: Default::default(),
        }
    }
}

impl<N, T> PartialEq for Rule<N, T> {
    fn eq(&self, other: &Self) -> bool {
        self.non_terminal == other.non_terminal &&
            self.symbols == other.symbols
    }
}

impl<N, T> Eq for Rule<N, T> {}

impl<N, T> PartialOrd for Rule<N, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.non_terminal.partial_cmp(&other.non_terminal) {
            Some(Ordering::Equal) => {}
            other => return other
        }
        self.symbols.partial_cmp(&other.symbols)
    }
}

impl<N, T> Ord for Rule<N, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.non_terminal.cmp(&other.non_terminal) {
            Ordering::Equal => {}
            other => return other,
        }
        self.symbols.cmp(&other.symbols)
    }
}

impl<N, T> Hash for Rule<N, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.non_terminal.hash(state);
        self.symbols.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(crate) enum TerminalSymbol<T> {
    Symbol(T),
    EOI,
}

impl<N: EnumIndex, T: EnumIndex> Rule<N, T> {
    pub fn new(example: N) -> Self {
        Rule { non_terminal: example.enum_index(), symbols: Vec::new(), phantom: Default::default() }
    }

    pub(crate) fn new_raw(non_terminal: usize) -> Self {
        Rule {
            non_terminal,
            symbols: Vec::new(),
            phantom: Default::default(),
        }
    }

    pub fn non_terminal(mut self, example: N) -> Self {
        self.symbols.push(Symbol::NonTerminal(example.enum_index()));
        self
    }

    pub(crate) fn non_terminal_raw(mut self, non_terminal: usize) -> Self {
        self.symbols.push(Symbol::NonTerminal(non_terminal));
        self
    }

    pub fn terminal(mut self, example: T) -> Self {
        self.symbols.push(Symbol::Terminal(TerminalSymbol::Symbol(example.enum_index())));
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::{EnumIndex, Symbol};
    use crate::syntax::{Rule, Syntax, TerminalSymbol};

    #[test]
    fn syntax() {
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N { A, B, C }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T { A, B, C }
        let syntax = Syntax::builder()
            .rule(Rule::new(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A))
            .rule(Rule::new(N::A).non_terminal(N::C).terminal(T::B))
            .rule(Rule::new(N::B).non_terminal(N::C))
            .rule(Rule::new(N::C).terminal(T::C))
            .build(N::A);
        assert_eq!(syntax,
                   Syntax::<N, T> {
                       rules: vec![
                           Rule {
                               non_terminal: 0,
                               symbols: vec![Symbol::NonTerminal(1), Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbol::Symbol(0))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 0,
                               symbols: vec![Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbol::Symbol(1))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 1,
                               symbols: vec![Symbol::NonTerminal(2)],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 2,
                               symbols: vec![Symbol::Terminal(TerminalSymbol::Symbol(2))],
                               phantom: Default::default(),
                           },
                       ],
                       start: 0,
                   });
    }
}
