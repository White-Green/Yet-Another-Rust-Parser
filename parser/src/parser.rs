use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

use crate::{NumberMapped, Rule, Symbol, Syntax};
use crate::syntax::TerminalSymbolFunc;

#[derive(Debug)]
struct LR1Item<N: NumberMapped, T> {
    rule: Rule<N, T>,
    position: usize,
    lookahead_symbol: Option<TerminalSymbolFunc<T>>,
}

fn calc_null<N: NumberMapped, T>(syntax: &Syntax<N, T>) -> HashSet<Symbol<usize, TerminalSymbolFunc<T>>> {
    let mut null = HashSet::new();
    loop {
        let mut updated = false;
        for rule in &syntax.rules {
            if null.contains(&Symbol::NonTerminal(rule.non_terminal)) { continue; }
            if rule.symbols.iter().all(|symbol| null.contains(symbol))
            {
                null.insert(Symbol::NonTerminal(rule.non_terminal));
                updated = true;
            }
        }
        if !updated { break; }
    }
    null
}

fn calc_first<N: NumberMapped, T>(syntax: &Syntax<N, T>, null: &HashSet<Symbol<usize, TerminalSymbolFunc<T>>>) -> HashMap<Symbol<usize, TerminalSymbolFunc<T>>, HashSet<TerminalSymbolFunc<T>>> {
    let mut first = HashMap::new();
    for rule in &syntax.rules {
        for symbol in &rule.symbols {
            if let Symbol::Terminal(t) = symbol {
                first.entry(symbol.clone())
                    .or_insert_with(|| HashSet::new())
                    .insert(t.clone());
            }
        }
    }

    loop {
        let mut updated = false;
        for rule in &syntax.rules {
            let mut update = HashSet::new();
            for symbol in &rule.symbols {
                if let Some(first) = first.get(&symbol) {
                    first.iter().cloned().for_each(|item| { update.insert(item); });
                }
                if !null.contains(&symbol) { break; }
            }
            let set = first.entry(Symbol::NonTerminal(rule.non_terminal))
                .or_insert_with(|| HashSet::new());
            for item in update {
                updated |= set.insert(item);
            }
        }
        if !updated { break; }
    }

    first
}

struct Parser<N: NumberMapped, T> { p: PhantomData<(N, T)> }

impl<N: NumberMapped, T> Parser<N, T> {
    pub fn new(syntax: Syntax<N, T>) -> Self {
        unimplemented!()
    }
}

impl<N: NumberMapped, T> From<Syntax<N, T>> for Parser<N, T> {
    fn from(syntax: Syntax<N, T>) -> Self {
        Self::new(syntax)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{NumberMapped, Rule, Symbol, Syntax};
    use crate::parser::{calc_first, calc_null};
    use crate::syntax::TerminalSymbolFunc;

    #[test]
    fn null() {
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
        let syntax = Syntax::new()
            .rule(Rule::new(E::A).non_terminal(E::B).non_terminal(E::C).terminal_rc(Rc::clone(&term0)))
            .rule(Rule::new(E::A).non_terminal(E::C).terminal_rc(Rc::clone(&term1)))
            .rule(Rule::new(E::B).non_terminal(E::C))
            .rule(Rule::new(E::B).non_terminal(E::A))
            .rule(Rule::new(E::C));
        assert_eq!(calc_null(&syntax), vec![Symbol::NonTerminal(E::C.get_number()), Symbol::NonTerminal(E::B.get_number())].into_iter().collect())
    }

    #[test]
    fn first() {
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
        let syntax = Syntax::new()
            .rule(Rule::new(E::A).non_terminal(E::B).non_terminal(E::C).terminal_rc(Rc::clone(&term0)))
            .rule(Rule::new(E::A).non_terminal(E::C).terminal_rc(Rc::clone(&term1)))
            .rule(Rule::new(E::B).non_terminal(E::C))
            .rule(Rule::new(E::B).non_terminal(E::A))
            .rule(Rule::new(E::C));
        let first = calc_first(&syntax, &calc_null(&syntax));
        assert_eq!(first[&Symbol::NonTerminal(E::A.get_number())], vec![(TerminalSymbolFunc(Rc::clone(&term0))), (TerminalSymbolFunc(Rc::clone(&term1)))].into_iter().collect());
        assert_eq!(first[&Symbol::NonTerminal(E::B.get_number())], vec![(TerminalSymbolFunc(Rc::clone(&term0))), (TerminalSymbolFunc(Rc::clone(&term1)))].into_iter().collect());
        assert_eq!(first[&Symbol::NonTerminal(E::C.get_number())], vec![].into_iter().collect());
        assert_eq!(first[&Symbol::Terminal(TerminalSymbolFunc(Rc::clone(&term0)))], vec![(TerminalSymbolFunc(Rc::clone(&term0)))].into_iter().collect());
        assert_eq!(first[&Symbol::Terminal(TerminalSymbolFunc(Rc::clone(&term1)))], vec![(TerminalSymbolFunc(Rc::clone(&term1)))].into_iter().collect());
    }
}
