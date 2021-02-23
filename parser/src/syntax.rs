use core::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::rc::Rc;

use crate::{NumberMapped, Symbol};

#[derive(Debug, PartialEq, Default)]
pub struct Syntax<N: NumberMapped, T> {
    pub(crate) rules: Vec<Rule<N, T>>,
}

impl<N: NumberMapped, T> Syntax<N, T> {
    pub fn new() -> Self {
        Syntax {
            rules: Vec::new(),
        }
    }

    pub fn rule(mut self, rule: Rule<N, T>) -> Self {
        self.rules.push(rule);
        self
    }
}

#[derive(Debug)]
pub struct Rule<N: NumberMapped, T> {
    pub(crate) non_terminal: usize,
    pub(crate) symbols: Vec<Symbol<usize, TerminalSymbol<T>>>,
    phantom: PhantomData<N>,
}

impl<N: NumberMapped, T> Clone for Rule<N, T> {
    fn clone(&self) -> Self {
        Rule {
            non_terminal: self.non_terminal.clone(),
            symbols: self.symbols.clone(),
            phantom: Default::default(),
        }
    }
}

impl<N: NumberMapped, T> PartialEq for Rule<N, T> {
    fn eq(&self, other: &Self) -> bool {
        self.non_terminal == other.non_terminal &&
            self.symbols == other.symbols
    }
}

impl<N: NumberMapped, T> Eq for Rule<N, T> {}

impl<N: NumberMapped, T> Hash for Rule<N, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.non_terminal.hash(state);
        self.symbols.hash(state);
    }
}

pub(crate) enum TerminalSymbol<T> {
    Symbol(Rc<dyn Fn(&T) -> bool>),
    EOI,
}

impl<T> Debug for TerminalSymbol<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TerminalSymbol::Symbol(func) => f.debug_tuple("TerminalSymbol").field(&Rc::as_ptr(func)).finish(),
            TerminalSymbol::EOI => f.debug_tuple("EOI").finish()
        }
    }
}

impl<T> Clone for TerminalSymbol<T> {
    fn clone(&self) -> Self {
        match self {
            TerminalSymbol::Symbol(f) => TerminalSymbol::Symbol(Rc::clone(f)),
            TerminalSymbol::EOI => TerminalSymbol::EOI
        }
    }
}

impl<T> PartialEq for TerminalSymbol<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TerminalSymbol::Symbol(f1), TerminalSymbol::Symbol(f2)) => Rc::ptr_eq(f1, f2),
            (TerminalSymbol::EOI, TerminalSymbol::EOI) => true,
            _ => false,
        }
    }
}

impl<T> Eq for TerminalSymbol<T> {}

impl<T> Hash for TerminalSymbol<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            TerminalSymbol::Symbol(f) => Rc::as_ptr(f).hash(state),
            TerminalSymbol::EOI => 0usize.hash(state),
        }
    }
}

impl<N: NumberMapped, T> Rule<N, T> {
    pub fn new(example: N) -> Self {
        Rule { non_terminal: example.get_number(), symbols: Vec::new(), phantom: Default::default() }
    }

    pub fn non_terminal(mut self, example: N) -> Self {
        self.symbols.push(Symbol::NonTerminal(example.get_number()));
        self
    }

    pub fn terminal<F: Fn(&T) -> bool + 'static>(mut self, f: F) -> Self {
        self.symbols.push(Symbol::Terminal(TerminalSymbol::Symbol(Rc::new(f) as Rc<dyn Fn(&T) -> bool>)));
        self
    }

    pub fn terminal_rc(mut self, f: Rc<dyn Fn(&T) -> bool>) -> Self {
        self.symbols.push(Symbol::Terminal(TerminalSymbol::Symbol(f)));
        self
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{NumberMapped, Symbol};
    use crate::syntax::{Rule, Syntax, TerminalSymbol};

    #[test]
    fn syntax() {
        #[derive(Debug, PartialEq)]
        enum E { A, B, C }
        impl NumberMapped for E {
            fn get_number(&self) -> usize {
                match self {
                    E::A => 0,
                    E::B => 1,
                    E::C => 2,
                }
            }

            fn default_from_number(number: usize) -> Option<Self> {
                match number {
                    0 => Some(E::A),
                    1 => Some(E::B),
                    2 => Some(E::C),
                    _ => None
                }
            }
        }
        let term0 = Rc::new(|v: &i32| *v == 0) as Rc<dyn Fn(&i32) -> bool>;
        let term1 = Rc::new(|v: &i32| *v == 1) as Rc<dyn Fn(&i32) -> bool>;
        let term2 = Rc::new(|v: &i32| *v == 2) as Rc<dyn Fn(&i32) -> bool>;
        let syntax = Syntax::new()
            .rule(Rule::new(E::A).non_terminal(E::B).non_terminal(E::C).terminal_rc(Rc::clone(&term0)))
            .rule(Rule::new(E::A).non_terminal(E::C).terminal_rc(Rc::clone(&term1)))
            .rule(Rule::new(E::B).non_terminal(E::C))
            .rule(Rule::new(E::C).terminal_rc(Rc::clone(&term2)));
        assert_eq!(syntax,
                   Syntax::<E, _> {
                       rules: vec![
                           Rule {
                               non_terminal: 0,
                               symbols: vec![Symbol::NonTerminal(1), Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbol::Symbol(term0))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 0,
                               symbols: vec![Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbol::Symbol(term1))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 1,
                               symbols: vec![Symbol::NonTerminal(2)],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 2,
                               symbols: vec![Symbol::Terminal(TerminalSymbol::Symbol(term2))],
                               phantom: Default::default(),
                           },
                       ]
                   });
    }
}
