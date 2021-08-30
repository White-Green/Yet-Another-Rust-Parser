use std::collections::{HashSet, VecDeque};
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::ops::RangeInclusive;

use enum_index::EnumIndex;

use crate::parser::{Action, LR1Parser, SymbolInternal};
use crate::syntax::TerminalSymbol;
use crate::Symbol;

#[derive(Debug)]
pub enum ParseError<E> {
    RecoveryRuleNotFound,
    ErrorInReducer(E),
}

impl<E: Display> Display for ParseError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::ErrorInReducer(e) => e.fmt(f),
            ParseError::RecoveryRuleNotFound => write!(f, "recovery rule is not found"),
        }
    }
}

impl<E: 'static + Error> Error for ParseError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParseError::RecoveryRuleNotFound => None,
            ParseError::ErrorInReducer(e) => Some(e),
        }
    }
}

pub trait Parse<N, E>: IntoIterator {
    fn parse(self, parser: &LR1Parser<N, Self::Item, E>) -> Result<N, ParseError<E>>;
}

impl<I: IntoIterator, N, E> Parse<N, E> for I
where
    I::Item: EnumIndex,
{
    fn parse(self, parser: &LR1Parser<N, Self::Item, E>) -> Result<N, ParseError<E>> {
        let mut iter = self.into_iter();
        let mut current_state = parser.start;
        let mut symbols = Vec::new();
        let mut buffer = VecDeque::new();
        let mut stack = Vec::new();
        let mut error_recovery_state = HashSet::new();
        loop {
            if buffer.is_empty() {
                if let Some(symbol) = iter.next() {
                    buffer.push_back((TerminalSymbol::Symbol(symbol.enum_index()), symbols.len()));
                    symbols.push(symbol);
                } else {
                    buffer.push_back((TerminalSymbol::EOI, 0));
                }
            }
            let (symbol, symbol_index) = buffer.front().unwrap();
            match parser.action_table.get(&current_state).unwrap().get(symbol) {
                Some(Action::Shift(state)) => {
                    let symbol = match symbol {
                        TerminalSymbol::Symbol(symbol) => TerminalSymbol::Symbol(*symbol),
                        TerminalSymbol::Error(_) => unreachable!(),
                        TerminalSymbol::EOI => TerminalSymbol::EOI,
                    };
                    let symbol = SymbolInternal::Terminal((symbol, *symbol_index));
                    stack.push((current_state, symbol));
                    current_state = *state;
                    buffer.pop_front();
                }
                Some(Action::Reduce(rule)) => {
                    let (state, mut rule_symbols): (Vec<_>, Vec<_>) = stack.drain(stack.len() - parser.rules[*rule].symbols.len()..).unzip();
                    let first_index: usize = rule_symbols
                        .iter()
                        .find_map(|symbol: &SymbolInternal<_, (TerminalSymbol<_, RangeInclusive<usize>>, _)>| match symbol {
                            SymbolInternal::NonTerminal((_, i)) => Some(*i),
                            SymbolInternal::Terminal((TerminalSymbol::Symbol(_), i)) => Some(*i),
                            _ => None,
                        })
                        .unwrap_or(symbols.len());
                    let mut rule_symbols = {
                        let mut rule_symbols_ = Vec::new();
                        let all_symbols = &symbols;
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
                                SymbolInternal::Terminal((TerminalSymbol::Error(range), _)) => Symbol::Error(&all_symbols[range.clone()]),
                                SymbolInternal::Terminal((TerminalSymbol::EOI, _)) => {
                                    unreachable!()
                                }
                            };
                            rule_symbols_.push(symbol);
                        }
                        rule_symbols_
                    };
                    current_state = state.first().copied().unwrap_or(current_state);
                    let reduced_symbol = SymbolInternal::NonTerminal(((parser.rules[*rule].generator)(&mut rule_symbols[..]).map_err(ParseError::ErrorInReducer)?, first_index));
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
                    let is_eoi = if let TerminalSymbol::EOI = symbol { true } else { false };
                    let mut backtracked = false;
                    let tail = *symbol_index;
                    let mut head = tail;
                    let mut error_head = head;
                    loop {
                        if !is_eoi || !backtracked {
                            if let Some(error_rules) = parser.error_rules.get(&current_state) {
                                if error_recovery_state.is_empty() {
                                    error_recovery_state = error_rules.clone();
                                    break;
                                }
                                if !error_recovery_state.is_disjoint(error_rules) {
                                    error_recovery_state = error_recovery_state.intersection(error_rules).cloned().collect();
                                    break;
                                }
                            }
                        }
                        backtracked = true;
                        if let Some((state, symbol)) = stack.pop() {
                            current_state = state;
                            match symbol {
                                SymbolInternal::NonTerminal((_, i)) | SymbolInternal::Terminal((TerminalSymbol::Symbol(_), i)) => {
                                    head = i;
                                }
                                SymbolInternal::Terminal((TerminalSymbol::Error(range), _)) => {
                                    error_head = *range.start();
                                }
                                SymbolInternal::Terminal((TerminalSymbol::EOI, _)) => {}
                            }
                        } else {
                            return Err(ParseError::RecoveryRuleNotFound);
                        }
                    }
                    for index in (head..tail).into_iter().rev() {
                        buffer.push_front((TerminalSymbol::Symbol(symbols[index].enum_index()), index));
                    }
                    if backtracked {
                        buffer.pop_front();
                    }
                    if let Some(Action::Shift(s)) = parser.action_table.get(&current_state).unwrap().get(&TerminalSymbol::Error(())) {
                        stack.push((current_state, SymbolInternal::Terminal((TerminalSymbol::Error(head.min(error_head)..=tail), 0))));
                        current_state = *s;
                    } else {
                        unreachable!()
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use enum_index_derive::*;

    use crate::iter::{Parse, ParseError};
    use crate::parser::LR1Parser;
    use crate::*;
    use crate::{Rule, Syntax};

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

        use NonTerminal::*;
        use Terminal::*;

        let (parser, _) = LR1Parser::<_, _>::new(
            Syntax::builder()
                .rule(Rule::new(E(Vec::new()), &[Symbol::NonTerminal(E(Vec::new())), Symbol::Terminal(Plus), Symbol::NonTerminal(T(Vec::new()))], |list| {
                    if let [Symbol::NonTerminal(E(vec)), _, Symbol::NonTerminal(T(v))] = *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(T(std::mem::take(v)));
                        Ok(E(vec))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(E(Vec::new()), &[Symbol::NonTerminal(T(Vec::new()))], |list| if let [Symbol::NonTerminal(T(vec))] = *list { Ok(E(vec![T(std::mem::take(vec))])) } else { unreachable!() }))
                .rule(Rule::new(T(Vec::new()), &[Symbol::NonTerminal(T(Vec::new())), Symbol::Terminal(Star), Symbol::NonTerminal(F(Plus))], |list| {
                    if let [Symbol::NonTerminal(T(vec)), _, Symbol::NonTerminal(f)] = &mut *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, F(Number(0))));
                        Ok(T(vec))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(T(Vec::new()), &[Symbol::NonTerminal(F(Plus))], |list| if let [Symbol::NonTerminal(f)] = list { Ok(T(vec![std::mem::replace(f, F(Number(0)))])) } else { unreachable!() }))
                .rule(Rule::new(F(Plus), &[Symbol::Terminal(Number(0))], |list| if let [Symbol::Terminal(n)] = list { Ok(F(n.clone())) } else { unreachable!() }))
                .build(E(Vec::new())),
        );
        assert_eq!(vec![Number(1), Plus, Number(2), Star, Number(3), Plus, Number(4)].into_iter().parse(&parser).unwrap(), E(vec![T(vec![F(Number(1))]), T(vec![F(Number(2)), F(Number(3))]), T(vec![F(Number(4))])]));
    }

    #[test]
    fn parse_error() {
        #[derive(EnumIndex, Debug, PartialEq)]
        enum NonTerminal {
            Add(Vec<NonTerminal>),
            Prod(Vec<NonTerminal>),
            Item(Union),
        }
        #[derive(EnumIndex, Debug, PartialEq, Clone)]
        enum Terminal {
            Plus,
            Star,
            Bracket,
            CloseBracket,
            I(usize),
        }
        #[derive(Debug, PartialEq)]
        enum Union {
            Number(usize),
            NonTerminal(Box<NonTerminal>),
            Error(Vec<Terminal>),
        }
        use NonTerminal::*;
        use Terminal::*;
        let parser = LR1Parser::<_, _>::from(
            Syntax::builder()
                .rule(Rule::new(Add(Vec::new()), &[Symbol::NonTerminal(Add(Vec::new())), Symbol::Terminal(Plus), Symbol::NonTerminal(Prod(Vec::new()))], |list| {
                    if let [Symbol::NonTerminal(Add(vec)), _, Symbol::NonTerminal(t)] = list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(t, Prod(Vec::new())));
                        Ok(Add(vec))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(Add(Vec::new()), &[Symbol::Error(()), Symbol::Terminal(Plus), Symbol::NonTerminal(Prod(Vec::new()))], |list| {
                    if let [Symbol::Error(error), _, Symbol::NonTerminal(t)] = list {
                        Ok(Add(vec![Item(Union::Error(error.to_vec())), std::mem::replace(t, Prod(Vec::new()))]))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(Add(Vec::new()), &[Symbol::Error(()), Symbol::Terminal(Plus), Symbol::Error(())], |list| {
                    if let [Symbol::Error(err1), _, Symbol::Error(err2)] = list {
                        Ok(Add(vec![Item(Union::Error(dbg!(err1).iter().chain(dbg!(err2).iter()).cloned().collect()))]))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(Add(Vec::new()), &[Symbol::NonTerminal(Prod(Vec::new()))], |list| if let [Symbol::NonTerminal(t)] = list { Ok(Add(vec![std::mem::replace(t, Prod(Vec::new()))])) } else { unreachable!() }))
                .rule(Rule::new(Prod(Vec::new()), &[Symbol::NonTerminal(Prod(Vec::new())), Symbol::Terminal(Star), Symbol::NonTerminal(Item(Union::Error(Vec::new())))], |list| {
                    if let [Symbol::NonTerminal(Prod(vec)), _, Symbol::NonTerminal(f)] = list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, Item(Union::Error(Vec::new()))));
                        Ok(Prod(vec))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(Prod(Vec::new()), &[Symbol::NonTerminal(Item(Union::Error(Vec::new())))], |list| if let [Symbol::NonTerminal(n)] = list { Ok(Prod(vec![std::mem::replace(n, Item(Union::Error(Vec::new())))])) } else { unreachable!() }))
                .rule(Rule::new(Item(Union::Error(Vec::new())), &[Symbol::Terminal(Bracket), Symbol::NonTerminal(Add(Vec::new())), Symbol::Terminal(CloseBracket)], |list| {
                    if let [_, Symbol::NonTerminal(e), _] = list {
                        Ok(Item(Union::NonTerminal(Box::new(std::mem::replace(e, Add(Vec::new()))))))
                    } else {
                        unreachable!()
                    }
                }))
                .rule(Rule::new(Item(Union::Error(Vec::new())), &[Symbol::Terminal(Bracket), Symbol::Error(()), Symbol::Terminal(CloseBracket)], |list| if let [_, Symbol::Error(err), _] = list { Ok(Item(Union::Error(err.to_vec()))) } else { unreachable!() }))
                .rule(Rule::new(Item(Union::Error(Vec::new())), &[Symbol::Terminal(I(0))], |list| if let [Symbol::Terminal(Terminal::I(n))] = list { Ok(Item(Union::Number(*n))) } else { unreachable!() }))
                .build(Add(Vec::new())),
        );

        assert_eq!(
            vec![I(1), Plus, I(2), Star, Bracket, I(3), Plus, I(4), CloseBracket].into_iter().parse(&parser).unwrap(),
            Add(vec![Prod(vec![Item(Union::Number(1))]), Prod(vec![Item(Union::Number(2)), Item(Union::NonTerminal(Box::new(Add(vec![Prod(vec![Item(Union::Number(3))]), Prod(vec![Item(Union::Number(4))])]))))])]),
        );
        assert_eq!(
            vec![I(1), Plus, I(2), Star, Bracket, I(3), CloseBracket].into_iter().parse(&parser).unwrap(),
            Add(vec![Prod(vec![Item(Union::Number(1))]), Prod(vec![Item(Union::Number(2)), Item(Union::NonTerminal(Box::new(Add(vec![Prod(vec![Item(Union::Number(3))])]))))])])
        );
        assert_eq!(vec![I(1), Plus, I(2), Star, Bracket, I(3), I(4), CloseBracket].into_iter().parse(&parser).unwrap(), Add(vec![Prod(vec![Item(Union::Number(1))]), Prod(vec![Item(Union::Number(2)), Item(Union::Error(vec![I(3), I(4)]))])]));
        assert_eq!(vec![I(1), Plus, Bracket, I(2), I(3), CloseBracket, Star, I(4)].into_iter().parse(&parser).unwrap(), Add(vec![Prod(vec![Item(Union::Number(1))]), Prod(vec![Item(Union::Error(vec![I(2), I(3)])), Item(Union::Number(4))])]));
        assert_eq!(
            vec![Plus, I(2), Star, Bracket, I(3), CloseBracket].into_iter().parse(&parser).unwrap(),
            Add(vec![Item(Union::Error(vec![Plus])), Prod(vec![Item(Union::Number(2)), Item(Union::NonTerminal(Box::new(Add(vec![Prod(vec![Item(Union::Number(3))])]))))])])
        );
        assert!(if let Err(ParseError::RecoveryRuleNotFound) = vec![I(1), Plus, I(2), Star, Bracket, I(3)].into_iter().parse(&parser) { true } else { false });
    }
}
