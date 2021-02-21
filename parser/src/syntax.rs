use core::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

use crate::{NumberMapped, Symbol};

#[derive(Debug, PartialEq, Default)]
pub struct Syntax<N: NumberMapped, T> {
    rules: Vec<Rule<N, T>>,
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

#[derive(Debug, PartialEq)]
pub struct Rule<N: NumberMapped, T> {
    non_terminal: usize,
    symbols: Vec<Symbol<usize, TerminalSymbolFunc<T>>>,
    phantom: PhantomData<N>,
}

struct TerminalSymbolFunc<T>(Rc<dyn Fn(&T) -> bool>);

impl<T> Debug for TerminalSymbolFunc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TerminalSymbolFunc").field(&Rc::as_ptr(&self.0)).finish()
    }
}

impl<T> PartialEq for TerminalSymbolFunc<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
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
        self.symbols.push(Symbol::Terminal(TerminalSymbolFunc(Rc::new(f) as Rc<dyn Fn(&T) -> bool>)));
        self
    }

    pub fn terminal_rc(mut self, f: Rc<dyn Fn(&T) -> bool>) -> Self {
        self.symbols.push(Symbol::Terminal(TerminalSymbolFunc(f)));
        self
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{NumberMapped, Symbol};
    use crate::syntax::{Rule, Syntax, TerminalSymbolFunc};

    #[test]
    fn test_syntax() {
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
                               symbols: vec![Symbol::NonTerminal(1), Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbolFunc(term0))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 0,
                               symbols: vec![Symbol::NonTerminal(2), Symbol::Terminal(TerminalSymbolFunc(term1))],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 1,
                               symbols: vec![Symbol::NonTerminal(2)],
                               phantom: Default::default(),
                           },
                           Rule {
                               non_terminal: 2,
                               symbols: vec![Symbol::Terminal(TerminalSymbolFunc(term2))],
                               phantom: Default::default(),
                           },
                       ]
                   });
    }
}
