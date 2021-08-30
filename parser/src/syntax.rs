use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use enum_index::EnumIndex;

use crate::parser::SymbolInternal;
use crate::Symbol;

#[derive(Debug, PartialEq)]
pub struct Syntax<N, T, E = Box<dyn Error + Send + Sync + 'static>> {
    pub(crate) rules: Vec<Rule<N, T, E>>,
    pub(crate) start: usize,
}

impl<N: EnumIndex, T: EnumIndex, E> Syntax<N, T, E> {
    pub fn builder() -> SyntaxBuilder<N, T, E> {
        Default::default()
    }

    pub fn into_rules(self) -> Vec<Rule<N, T, E>> {
        self.rules
    }
}

#[derive(Debug, PartialEq)]
pub struct SyntaxBuilder<N, T, E = Box<dyn Error + Send + Sync + 'static>> {
    rules: Vec<Rule<N, T, E>>,
}

impl<N, T, E> Default for SyntaxBuilder<N, T, E> {
    fn default() -> Self {
        Self { rules: Vec::new() }
    }
}

impl<N: EnumIndex, T: EnumIndex, E> SyntaxBuilder<N, T, E> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn rule(mut self, rule: Rule<N, T, E>) -> Self {
        self.rules.push(rule);
        self
    }

    pub fn build(self, start: N) -> Syntax<N, T, E> {
        let SyntaxBuilder { rules } = self;
        Syntax { rules, start: start.enum_index() }
    }

    pub fn build_raw(self, start: usize) -> Syntax<N, T, E> {
        let SyntaxBuilder { rules } = self;
        Syntax { rules, start }
    }
}

pub struct Rule<N, T, E = Box<dyn Error + Send + Sync + 'static>> {
    pub(crate) non_terminal: usize,
    pub(crate) symbols: Vec<SymbolInternal<usize, TerminalSymbol<usize, ()>>>,
    pub(crate) generator: Box<dyn Fn(&mut [Symbol<&mut N, &T, &[T]>]) -> Result<N, E>>,
    phantom: PhantomData<(N, T, E)>,
}

#[derive(Debug)]
pub struct RuleBuilder<N, T> {
    pub(crate) non_terminal: usize,
    pub(crate) symbols: Vec<SymbolInternal<usize, TerminalSymbol<usize, ()>>>,
    phantom: PhantomData<(N, T)>,
}

impl<N, T, E> Debug for Rule<N, T, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rule").field("non_terminal", &self.non_terminal).field("symbols", &self.symbols).finish()
    }
}

impl<N, T, E> PartialEq for Rule<N, T, E> {
    fn eq(&self, other: &Self) -> bool {
        self.non_terminal == other.non_terminal && self.symbols == other.symbols
    }
}

impl<N, T, E> Eq for Rule<N, T, E> {}

impl<N, T, E> PartialOrd for Rule<N, T, E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.non_terminal.partial_cmp(&other.non_terminal) {
            Some(Ordering::Equal) => {}
            other => return other,
        }
        self.symbols.partial_cmp(&other.symbols)
    }
}

impl<N, T, E> Ord for Rule<N, T, E> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.non_terminal.cmp(&other.non_terminal) {
            Ordering::Equal => {}
            other => return other,
        }
        self.symbols.cmp(&other.symbols)
    }
}

impl<N, T, E> Hash for Rule<N, T, E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.non_terminal.hash(state);
        self.symbols.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum TerminalSymbol<T, E> {
    Symbol(T),
    Error(E),
    EOI,
}

impl<N: EnumIndex, T: EnumIndex, E> Rule<N, T, E> {
    pub fn new<F: 'static + Fn(&mut [Symbol<&mut N, &T, &[T]>]) -> Result<N, E>>(start: N, rule: &[Symbol<N, T, ()>], generator: F) -> Rule<N, T, E> {
        Rule {
            non_terminal: start.enum_index(),
            symbols: rule
                .iter()
                .map(|symbol| match symbol {
                    Symbol::NonTerminal(n) => SymbolInternal::NonTerminal(n.enum_index()),
                    Symbol::Terminal(t) => SymbolInternal::Terminal(TerminalSymbol::Symbol(t.enum_index())),
                    Symbol::Error(_) => SymbolInternal::Terminal(TerminalSymbol::Error(())),
                })
                .collect(),
            generator: Box::new(generator),
            phantom: Default::default(),
        }
    }

    pub fn new_raw<F: 'static + Fn(&mut [Symbol<&mut N, &T, &[T]>]) -> Result<N, E>>(start: usize, rule: &[Symbol<usize, usize, ()>], generator: F) -> Rule<N, T, E> {
        Rule {
            non_terminal: start,
            symbols: rule
                .iter()
                .map(|symbol| match symbol {
                    Symbol::NonTerminal(n) => SymbolInternal::NonTerminal(*n),
                    Symbol::Terminal(t) => SymbolInternal::Terminal(TerminalSymbol::Symbol(*t)),
                    Symbol::Error(_) => SymbolInternal::Terminal(TerminalSymbol::Error(())),
                })
                .collect(),
            generator: Box::new(generator),
            phantom: Default::default(),
        }
    }

    pub fn builder(example: N) -> RuleBuilder<N, T> {
        RuleBuilder {
            non_terminal: example.enum_index(),
            symbols: Vec::new(),
            phantom: Default::default(),
        }
    }

    pub(crate) fn builder_raw(non_terminal: usize) -> RuleBuilder<N, T> {
        RuleBuilder { non_terminal, symbols: Vec::new(), phantom: Default::default() }
    }
}

impl<N: EnumIndex, T: EnumIndex> RuleBuilder<N, T> {
    pub fn non_terminal(mut self, example: N) -> Self {
        self.symbols.push(SymbolInternal::NonTerminal(example.enum_index()));
        self
    }

    pub(crate) fn non_terminal_raw(mut self, non_terminal: usize) -> Self {
        self.symbols.push(SymbolInternal::NonTerminal(non_terminal));
        self
    }

    pub fn terminal(mut self, example: T) -> Self {
        self.symbols.push(SymbolInternal::Terminal(TerminalSymbol::Symbol(example.enum_index())));
        self
    }

    pub fn error(mut self) -> Self {
        self.symbols.push(SymbolInternal::Terminal(TerminalSymbol::Error(())));
        self
    }

    pub fn build<E, F: 'static + Fn(&mut [Symbol<&mut N, &T, &[T]>]) -> Result<N, E>>(self, generator: F) -> Rule<N, T, E> {
        Rule {
            non_terminal: self.non_terminal,
            symbols: self.symbols,
            generator: Box::new(generator),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use enum_index_derive::*;

    use crate::parser::SymbolInternal;
    use crate::syntax::{Rule, Syntax, TerminalSymbol};

    #[test]
    fn syntax() {
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N {
            A,
            B,
            C,
        }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T {
            A,
            B,
            C,
        }
        let syntax = Syntax::<_, _>::builder()
            .rule(Rule::<_, _>::builder(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A).build(|_| Ok(N::A)))
            .rule(Rule::<_, _>::builder(N::A).non_terminal(N::C).terminal(T::B).build(|_| Ok(N::A)))
            .rule(Rule::<_, _>::builder(N::B).non_terminal(N::C).build(|_| Ok(N::B)))
            .rule(Rule::<_, _>::builder(N::C).terminal(T::C).build(|_| Ok(N::C)))
            .build(N::A);
        assert_eq!(syntax.start, 0);

        assert_eq!(syntax.rules[0].non_terminal, 0);
        assert_eq!(syntax.rules[1].non_terminal, 0);
        assert_eq!(syntax.rules[2].non_terminal, 1);
        assert_eq!(syntax.rules[3].non_terminal, 2);

        assert_eq!(syntax.rules[0].symbols, vec![SymbolInternal::NonTerminal(1), SymbolInternal::NonTerminal(2), SymbolInternal::Terminal(TerminalSymbol::Symbol(0))]);
        assert_eq!(syntax.rules[1].symbols, vec![SymbolInternal::NonTerminal(2), SymbolInternal::Terminal(TerminalSymbol::Symbol(1))]);
        assert_eq!(syntax.rules[2].symbols, vec![SymbolInternal::NonTerminal(2)]);
        assert_eq!(syntax.rules[3].symbols, vec![SymbolInternal::Terminal(TerminalSymbol::Symbol(2))]);

        let syntax = Syntax::<_, _>::builder()
            .rule(Rule::<_, _>::builder(N::A).error().non_terminal(N::C).terminal(T::A).build(|_| Ok(N::A)))
            .rule(Rule::<_, _>::builder(N::A).non_terminal(N::C).error().build(|_| Ok(N::A)))
            .rule(Rule::<_, _>::builder(N::B).non_terminal(N::C).build(|_| Ok(N::B)))
            .rule(Rule::<_, _>::builder(N::C).terminal(T::C).build(|_| Ok(N::C)))
            .build(N::A);

        assert_eq!(syntax.start, 0);

        assert_eq!(syntax.rules[0].non_terminal, 0);
        assert_eq!(syntax.rules[1].non_terminal, 0);
        assert_eq!(syntax.rules[2].non_terminal, 1);
        assert_eq!(syntax.rules[3].non_terminal, 2);

        assert_eq!(syntax.rules[0].symbols, vec![SymbolInternal::Terminal(TerminalSymbol::Error(())), SymbolInternal::NonTerminal(2), SymbolInternal::Terminal(TerminalSymbol::Symbol(0))]);
        assert_eq!(syntax.rules[1].symbols, vec![SymbolInternal::NonTerminal(2), SymbolInternal::Terminal(TerminalSymbol::Error(()))]);
        assert_eq!(syntax.rules[2].symbols, vec![SymbolInternal::NonTerminal(2)]);
        assert_eq!(syntax.rules[3].symbols, vec![SymbolInternal::Terminal(TerminalSymbol::Symbol(2))]);
    }
}
