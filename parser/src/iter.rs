use std::collections::{HashSet, VecDeque};
use std::error::Error;
use std::fmt::{Display, Formatter};

use enum_index::EnumIndex;

use crate::parser::{Action, LR1Parser, SymbolInternal};
use crate::Symbol;
use crate::syntax::TerminalSymbol;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    SyntaxError
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Error for ParseError {}

pub trait Parse<N>: Iterator {
    fn parse(self, parser: &LR1Parser<N, Self::Item>) -> Result<N, ParseError>;
}

impl<I: Iterator, N> Parse<N> for I
    where I::Item: EnumIndex {
    fn parse(mut self, parser: &LR1Parser<N, Self::Item>) -> Result<N, ParseError> {
        let mut current_state = parser.start;
        let mut symbols = Vec::new();
        let mut buffer = VecDeque::new();
        let mut stack = Vec::new();
        let mut error_recovery_state = HashSet::new();
        loop {
            if buffer.is_empty() {
                if let Some(symbol) = self.next() {
                    buffer.push_back((TerminalSymbol::Symbol(symbol.enum_index()), symbols.len()));
                    symbols.push(symbol);
                } else {
                    buffer.push_back((TerminalSymbol::EOI, 0));
                }
            }
            let (symbol, symbol_index) = buffer.front().unwrap();
            match parser.action_table.get(&current_state).unwrap().get(symbol) {
                Some(Action::Shift(state)) => {
                    let symbol = SymbolInternal::Terminal((symbol.clone(), *symbol_index));
                    stack.push((current_state, symbol));
                    current_state = *state;
                    buffer.pop_front();
                }
                Some(Action::Reduce(rule)) => {
                    let (state, mut rule_symbols): (Vec<_>, Vec<_>) = stack.drain(stack.len() - parser.rules[*rule].symbols.len()..).unzip();
                    let first_index: usize = rule_symbols.iter()
                        .find_map(|symbol| match symbol {
                            SymbolInternal::NonTerminal((_, i)) => Some(*i),
                            SymbolInternal::Terminal((TerminalSymbol::Symbol(_), i)) => Some(*i),
                            _ => None
                        })
                        .unwrap_or(symbols.len());
                    let mut rule_symbols = {
                        let mut rule_symbols_ = Vec::new();
                        let mut symbols = &symbols[..];
                        let mut symbols_index = 0;
                        for symbol in rule_symbols.iter_mut() {
                            let symbol = match symbol {
                                SymbolInternal::NonTerminal((n, _)) => Symbol::NonTerminal(n),
                                SymbolInternal::Terminal((TerminalSymbol::Symbol(_), i)) => {
                                    let (symbol, follow) = symbols[*i - symbols_index..].split_first().unwrap();
                                    symbols = follow;
                                    symbols_index = *i + 1;
                                    Symbol::Terminal(symbol)
                                }
                                SymbolInternal::Terminal((TerminalSymbol::Error, _)) => Symbol::Error,
                                SymbolInternal::Terminal((TerminalSymbol::EOI, _)) => unreachable!(),
                            };
                            rule_symbols_.push(symbol);
                        }
                        rule_symbols_
                    };
                    current_state = state.first().copied().unwrap_or(current_state);
                    let reduced_symbol = SymbolInternal::NonTerminal(((parser.rules[*rule].generator)(&mut rule_symbols[..]), first_index));
                    stack.push((current_state, reduced_symbol));
                    current_state = *parser.goto_table.get(&current_state).unwrap().get(&parser.rules[*rule].non_terminal).unwrap();
                    if error_recovery_state.contains(rule) {
                        error_recovery_state.clear();
                    }
                }
                Some(Action::Accept) => {
                    if let Some((_, SymbolInternal::NonTerminal((symbol, _)))) = stack.pop() {
                        return Ok(symbol);
                    } else {
                        unreachable!()
                    }
                }
                None => {
                    if let TerminalSymbol::EOI = symbol {
                        return Err(ParseError::SyntaxError);
                    }
                    let mut backtracked = false;
                    let tail = *symbol_index;
                    let mut head = tail;
                    loop {
                        if let Some(error_rules) = parser.error_rules.get(&current_state) {
                            if error_recovery_state.is_empty() {
                                error_recovery_state = error_rules.iter().cloned().collect();
                                break;
                            }
                            if !error_recovery_state.is_disjoint(error_rules) {
                                error_recovery_state = error_recovery_state.intersection(error_rules).cloned().collect();
                                break;
                            }
                        }
                        backtracked = true;
                        if let Some((state, symbol)) = stack.pop() {
                            current_state = state;
                            match symbol {
                                SymbolInternal::NonTerminal((_, i)) | SymbolInternal::Terminal((TerminalSymbol::Symbol(_), i)) => { head = i; }
                                _ => {}
                            }
                        } else {
                            return Err(ParseError::SyntaxError);
                        }
                    }
                    for index in (head..tail).into_iter().rev() {
                        buffer.push_front((TerminalSymbol::Symbol(symbols[index].enum_index()), index));
                    }
                    if backtracked {
                        buffer.pop_front();
                    }
                    if let Some(Action::Shift(s)) = parser.action_table.get(&current_state).unwrap().get(&TerminalSymbol::Error) {
                        stack.push((current_state, SymbolInternal::Terminal((TerminalSymbol::Error, 0))));
                        current_state = *s;
                    } else { unreachable!() }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use enum_index_derive::*;

    use crate::{Rule, Syntax};
    use crate::*;
    use crate::iter::{Parse, ParseError};
    use crate::parser::LR1Parser;

    #[test]
    fn parse() {
        #[derive(Debug, PartialEq, EnumIndex, Clone)]
        enum Terminal {
            Number(usize),
            Plus,
            Star,
        }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum NonTerminal {
            E(Vec<NonTerminal>),
            T(Vec<NonTerminal>),
            F(Terminal),
        }

        use Terminal::*;
        use NonTerminal::*;

        let (parser, _) = LR1Parser::new(Syntax::builder()
            .rule(Rule::new(
                E(Vec::new()),
                &[Symbol::NonTerminal(E(Vec::new())), Symbol::Terminal(Plus), Symbol::NonTerminal(T(Vec::new()))],
                |list|
                    if let [Symbol::NonTerminal(E(vec)), _, Symbol::NonTerminal(T(v))] = *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(T(std::mem::take(v)));
                        E(vec)
                    } else { unreachable!() }))
            .rule(Rule::new(
                E(Vec::new()),
                &[Symbol::NonTerminal(T(Vec::new()))],
                |list|
                    if let [Symbol::NonTerminal(T(vec))] = *list {
                        E(vec![T(std::mem::take(vec))])
                    } else { unreachable!() }))
            .rule(Rule::new(
                T(Vec::new()),
                &[Symbol::NonTerminal(T(Vec::new())), Symbol::Terminal(Star), Symbol::NonTerminal(F(Plus))],
                |list|
                    if let [Symbol::NonTerminal(T(vec)), _, Symbol::NonTerminal(f)] = &mut *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, F(Number(0))));
                        T(vec)
                    } else { unreachable!() }))
            .rule(Rule::new(
                T(Vec::new()),
                &[Symbol::NonTerminal(F(Plus))],
                |list|
                    if let [Symbol::NonTerminal(f)] = list {
                        T(vec![std::mem::replace(f, F(Number(0)))])
                    } else { unreachable!() }))
            .rule(Rule::new(
                F(Plus),
                &[Symbol::Terminal(Number(0))],
                |list|
                    if let [Symbol::Terminal(n)] = list {
                        F(n.clone())
                    } else { unreachable!() }))
            .build(E(Vec::new()))
        );
        assert_eq!(vec![Number(1), Plus, Number(2), Star, Number(3), Plus, Number(4)].into_iter().parse(&parser),
                   Ok(E(vec![
                       T(vec![F(Number(1))]),
                       T(vec![F(Number(2)), F(Number(3))]),
                       T(vec![F(Number(4))]),
                   ])));
    }

    #[test]
    fn parse_error() {
        #[derive(EnumIndex, Debug, PartialEq)]
        enum NonTerminal { Add(Vec<NonTerminal>), Prod(Vec<NonTerminal>), Item(Union) }
        #[derive(EnumIndex, Debug, PartialEq, Clone)]
        enum Terminal { Plus, Star, Bracket, CloseBracket, I(usize) }
        #[derive(Debug, PartialEq)]
        enum Union {
            Number(usize),
            NonTerminal(Box<NonTerminal>),
            Error,
        }
        use NonTerminal::*;
        use Terminal::*;
        let parser = LR1Parser::from(Syntax::builder()
            .rule(Rule::new(
                Add(Vec::new()),
                &[Symbol::NonTerminal(Add(Vec::new())), Symbol::Terminal(Plus), Symbol::NonTerminal(Prod(Vec::new()))],
                |list|
                    if let [Symbol::NonTerminal(Add(vec)), _, Symbol::NonTerminal(t)] = list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(t, Prod(Vec::new())));
                        Add(vec)
                    } else { unreachable!() }))
            .rule(Rule::new(
                Add(Vec::new()),
                &[Symbol::Error, Symbol::Terminal(Plus), Symbol::NonTerminal(Prod(Vec::new()))],
                |list|
                    if let [_, _, Symbol::NonTerminal(t)] = list {
                        Add(vec![Item(Union::Error), std::mem::replace(t, Prod(Vec::new()))])
                    } else { unreachable!() }))
            .rule(Rule::new(
                Add(Vec::new()),
                &[Symbol::Error, Symbol::Terminal(Plus), Symbol::Error],
                |list|
                    if let [_, _, _] = list {
                        Add(vec![Item(Union::Error)])
                    } else { unreachable!() }))
            .rule(Rule::new(
                Add(Vec::new()),
                &[Symbol::NonTerminal(Prod(Vec::new()))],
                |list|
                    if let [Symbol::NonTerminal(t)] = list {
                        Add(vec![std::mem::replace(t, Prod(Vec::new()))])
                    } else { unreachable!() }))
            .rule(Rule::new(
                Prod(Vec::new()),
                &[Symbol::NonTerminal(Prod(Vec::new())), Symbol::Terminal(Star), Symbol::NonTerminal(Item(Union::Error))],
                |list|
                    if let [Symbol::NonTerminal(Prod(vec)), _, Symbol::NonTerminal(f)] = list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, Item(Union::Error)));
                        Prod(vec)
                    } else { unreachable!() }))
            .rule(Rule::new(
                Prod(Vec::new()),
                &[Symbol::NonTerminal(Item(Union::Error))],
                |list|
                    if let [Symbol::NonTerminal(n)] = list {
                        Prod(vec![std::mem::replace(n, Item(Union::Error))])
                    } else { unreachable!() }))
            .rule(Rule::new(
                Item(Union::Error),
                &[Symbol::Terminal(Bracket), Symbol::NonTerminal(Add(Vec::new())), Symbol::Terminal(CloseBracket)],
                |list|
                    if let [_, Symbol::NonTerminal(e), _] = list {
                        Item(Union::NonTerminal(Box::new(std::mem::replace(e, Add(Vec::new())))))
                    } else { unreachable!() }))
            .rule(Rule::new(
                Item(Union::Error),
                &[Symbol::Terminal(Bracket), Symbol::Error, Symbol::Terminal(CloseBracket)],
                |list|
                    if let [_, _, _] = list {
                        Item(Union::Error)
                    } else { unreachable!() }))
            .rule(Rule::new(
                Item(Union::Error),
                &[Symbol::Terminal(I(0))],
                |list|
                    if let [Symbol::Terminal(Terminal::I(n))] = list {
                        Item(Union::Number(*n))
                    } else { unreachable!() }))
            .build(Add(Vec::new())));

        assert_eq!(vec![I(1), Plus, I(2), Star, Bracket, I(3), Plus, I(4), CloseBracket].into_iter().parse(&parser),
                   Ok(
                       Add(vec![
                           Prod(vec![Item(Union::Number(1))]),
                           Prod(vec![
                               Item(Union::Number(2)),
                               Item(Union::NonTerminal(
                                   Box::new(Add(vec![
                                       Prod(vec![Item(Union::Number(3))]),
                                       Prod(vec![Item(Union::Number(4))]),
                                   ])),
                               )),
                           ]),
                       ]),
                   ));
        assert_eq!(vec![I(1), Plus, I(2), Star, Bracket, I(3), CloseBracket].into_iter().parse(&parser),
                   Ok(
                       Add(vec![
                           Prod(vec![
                               Item(Union::Number(1))
                           ]),
                           Prod(vec![
                               Item(Union::Number(2)),
                               Item(Union::NonTerminal(
                                   Box::new(Add(vec![Prod(vec![Item(Union::Number(3))])]))))
                           ])
                       ])
                   ));
        assert_eq!(vec![I(1), Plus, I(2), Star, Bracket, I(3), I(4), CloseBracket].into_iter().parse(&parser),
                   Ok(
                       Add(vec![
                           Prod(vec![Item(Union::Number(1))]),
                           Prod(vec![
                               Item(Union::Number(2)),
                               Item(Union::Error)
                           ])
                       ])
                   ));
        assert_eq!(vec![I(1), Plus, Bracket, I(2), I(3), CloseBracket, Star, I(4)].into_iter().parse(&parser),
                   Ok(
                       Add(vec![
                           Prod(vec![Item(Union::Number(1))]),
                           Prod(vec![
                               Item(Union::Error),
                               Item(Union::Number(4))
                           ])
                       ])
                   ));
        assert_eq!(vec![Plus, I(2), Star, Bracket, I(3), CloseBracket].into_iter().parse(&parser),
                   Ok(
                       Add(vec![
                           Item(Union::Error),
                           Prod(vec![
                               Item(Union::Number(2)),
                               Item(Union::NonTerminal(Box::new(Add(vec![Prod(vec![Item(Union::Number(3))])]))))
                           ])
                       ])
                   ));
        assert_eq!(vec![I(1), Plus, I(2), Star, Bracket, I(3)].into_iter().parse(&parser),
                   Err(ParseError::SyntaxError));
    }
}
