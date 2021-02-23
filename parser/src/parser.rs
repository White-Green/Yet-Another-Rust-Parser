use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use crate::{NumberMapped, Rule, Symbol, Syntax};
use crate::syntax::TerminalSymbol;

#[derive(Debug)]
struct LR1Item<N: NumberMapped, T> {
    rule: Rule<N, T>,
    position: usize,
    lookahead_symbol: TerminalSymbol<T>,
}

impl<N: NumberMapped, T> PartialEq for LR1Item<N, T> {
    fn eq(&self, other: &Self) -> bool {
        self.rule == other.rule &&
            self.position == other.position &&
            self.lookahead_symbol == other.lookahead_symbol
    }
}

impl<N: NumberMapped, T> Eq for LR1Item<N, T> {}

impl<N: NumberMapped, T> Hash for LR1Item<N, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rule.hash(state);
        self.position.hash(state);
        self.lookahead_symbol.hash(state);
    }
}


fn calc_closure<N: NumberMapped, T>(mut set: HashSet<LR1Item<N, T>>, syntax: &Syntax<N, T>, null: &HashSet<Symbol<usize, TerminalSymbol<T>>>, first: &HashMap<Symbol<usize, TerminalSymbol<T>>, HashSet<TerminalSymbol<T>>>) -> HashSet<LR1Item<N, T>> {
    let mut rules = HashMap::new();
    for rule in &syntax.rules {
        rules.entry(rule.non_terminal)
            .or_insert_with(|| HashSet::new())
            .insert(rule);
    }
    loop {
        let mut update = HashSet::new();
        for item in &set {
            let non_terminal = if let Some(Symbol::NonTerminal(non_terminal)) = item.rule.symbols.get(item.position) {
                *non_terminal
            } else {
                continue;
            };
            let lookahead_symbol = Symbol::Terminal(item.lookahead_symbol.clone());
            let follow = item.rule.symbols.get(item.position + 1..).unwrap_or(&[]).iter().chain(Some(&lookahead_symbol));
            for lookahead_symbol in get_first(follow, null, first) {
                for rule in &rules[&non_terminal] {
                    update.insert(LR1Item {
                        rule: Rule::clone(rule),
                        position: 0,
                        lookahead_symbol: lookahead_symbol.clone(),
                    });
                }
            }
        }
        let mut updated = false;
        for item in update {
            updated |= set.insert(item);
        }
        if !updated { break; }
    }
    set
}

fn get_first<'a, T: 'a>(string: impl Iterator<Item=&'a Symbol<usize, TerminalSymbol<T>>>, null: &HashSet<Symbol<usize, TerminalSymbol<T>>>, first: &HashMap<Symbol<usize, TerminalSymbol<T>>, HashSet<TerminalSymbol<T>>>) -> HashSet<TerminalSymbol<T>> {
    let mut result = HashSet::new();
    for symbol in string {
        for symbol in first.get(symbol).map(|set| set.iter()).into_iter().flatten() {
            result.insert(symbol.clone());
        }
        if !null.contains(symbol) { break; }
    }
    result
}

fn calc_null<N: NumberMapped, T>(syntax: &Syntax<N, T>) -> HashSet<Symbol<usize, TerminalSymbol<T>>> {
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

fn calc_first<N: NumberMapped, T>(syntax: &Syntax<N, T>, null: &HashSet<Symbol<usize, TerminalSymbol<T>>>) -> HashMap<Symbol<usize, TerminalSymbol<T>>, HashSet<TerminalSymbol<T>>> {
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
    use std::collections::HashSet;
    use std::rc::Rc;

    use crate::{NumberMapped, Rule, Symbol, Syntax};
    use crate::parser::{calc_closure, calc_first, calc_null, LR1Item};
    use crate::syntax::TerminalSymbol;

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
        assert_eq!(first[&Symbol::NonTerminal(E::A.get_number())], vec![(TerminalSymbol::Symbol(Rc::clone(&term0))), (TerminalSymbol::Symbol(Rc::clone(&term1)))].into_iter().collect());
        assert_eq!(first[&Symbol::NonTerminal(E::B.get_number())], vec![(TerminalSymbol::Symbol(Rc::clone(&term0))), (TerminalSymbol::Symbol(Rc::clone(&term1)))].into_iter().collect());
        assert_eq!(first[&Symbol::NonTerminal(E::C.get_number())], vec![].into_iter().collect());
        assert_eq!(first[&Symbol::Terminal(TerminalSymbol::Symbol(Rc::clone(&term0)))], vec![(TerminalSymbol::Symbol(Rc::clone(&term0)))].into_iter().collect());
        assert_eq!(first[&Symbol::Terminal(TerminalSymbol::Symbol(Rc::clone(&term1)))], vec![(TerminalSymbol::Symbol(Rc::clone(&term1)))].into_iter().collect());
    }

    #[test]
    fn closure() {
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
            .rule(Rule::new(E::B).non_terminal(E::A))
            .rule(Rule::new(E::C).terminal_rc(Rc::clone(&term2)))
            .rule(Rule::new(E::C));
        let null = calc_null(&syntax);
        let first = calc_first(&syntax, &null);
        let closure = calc_closure(vec![LR1Item {
            rule: syntax.rules[0].clone(),
            position: 0,
            lookahead_symbol: TerminalSymbol::EOI,
        }].into_iter().collect(), &syntax, &null, &first);
        assert_eq!(closure, vec![
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term1)),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term0)),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term1)),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Rc::clone(&term2)),
            },
        ].into_iter().collect());
    }
}
