use std::error::Error;

use parser::enum_index_derive::EnumIndex;
use parser::Symbol;
use parser::{enum_index, Parse};
use parser_generator::parser;
use std::mem;

#[derive(Debug, PartialEq, EnumIndex, Clone)]
pub enum Terminal {
    Number(usize),
    Plus,
    Star,
}

#[derive(Debug, PartialEq, EnumIndex)]
pub enum NonTerminal {
    E(Vec<NonTerminal>),
    T(Vec<NonTerminal>),
    F(Terminal),
}

parser! {
    fn create_parser() -> LR1Parser {
        token Terminal{
            Number = Number(0),
            "+" = Plus,
            "*" = Star,
        }
        symbol NonTerminal{
            E = E(Vec::new()),
            T = T(Vec::new()),
            F = F(Terminal::Plus),
        }
        errortype Box<dyn Error + Send + Sync + 'static>;
        start E;
        <E>::=<E> "+" <T>: [Symbol::NonTerminal(NonTerminal::E(vec)), _, Symbol::NonTerminal(NonTerminal::T(v))] => {
                            vec.push(NonTerminal::T(mem::take(v)));
                            Ok(NonTerminal::E(mem::take(vec)))
                        };
        <E>::=<T>: [Symbol::NonTerminal(NonTerminal::T(vec))] => Ok(NonTerminal::E(vec![NonTerminal::T(std::mem::take(vec))]));
        <T>::=<T> "*" <F>: [Symbol::NonTerminal(NonTerminal::T(vec)), _, Symbol::NonTerminal(f)] => {
                            vec.push(std::mem::replace(f, NonTerminal::F(Terminal::Number(0))));
                            Ok(NonTerminal::T(mem::take(vec)))
                        };
        <T>::=<F>: [Symbol::NonTerminal(f)] => Ok(NonTerminal::T(vec![std::mem::replace(f, NonTerminal::F(Terminal::Number(0)))]));
        <F>::=[Number]: [Symbol::Terminal(n)] => Ok(NonTerminal::F(n.clone()));
        <F>::=ERROR: [Symbol::Error(list)] => Err(format!("{:?}", list).into());
    }
}

#[test]
fn test_parser_generator() {
    let parser = create_parser();
    use NonTerminal::*;
    use Terminal::*;
    assert_eq!(vec![Number(1), Plus, Number(2), Star, Number(3), Plus, Number(4)].into_iter().parse(&parser).unwrap(), E(vec![T(vec![F(Number(1))]), T(vec![F(Number(2)), F(Number(3))]), T(vec![F(Number(4))])]));
    assert_eq!(format!("{}", vec![Number(1), Plus, Plus, Star, Number(3), Plus, Number(4)].into_iter().parse(&parser).unwrap_err()), "[Plus]");
}
