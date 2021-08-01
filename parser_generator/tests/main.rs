use parser::enum_index_derive::EnumIndex;
use parser::{enum_index, Parse};
use parser_generator::parser;

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

use parser::Symbol;

parser! {
    token Terminal{
        Number(0,),
        Plus,
        Star,
    }
    symbol NonTerminal{
        E(Vec::new(),),
        T(Vec::new(),),
        F(Terminal::Plus,),
    }
    E
    <E>::=(<E>[Plus]<T>)                  (|list|
                    if let [Symbol::NonTerminal(NonTerminal::E(vec)), _, Symbol::NonTerminal(NonTerminal::T(v))] = *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(NonTerminal::T(std::mem::take(v)));
                        NonTerminal::E(vec)
                    } else { unreachable!() })
    <E>::=(<T>)                         (|list|
                    if let [Symbol::NonTerminal(NonTerminal::T(vec))] = *list {
                        NonTerminal::E(vec![NonTerminal::T(std::mem::take(vec))])
                    } else { unreachable!() })
    <T>::=(<T>[Star]<F>)                  (|list|
                    if let [Symbol::NonTerminal(NonTerminal::T(vec)), _, Symbol::NonTerminal(f)] = &mut *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, NonTerminal::F(Terminal::Number(0))));
                        NonTerminal::T(vec)
                    } else { unreachable!() })
    <T>::=(<F>)                         (|list|
                    if let [Symbol::NonTerminal(f)] = list {
                        NonTerminal::T(vec![std::mem::replace(f, NonTerminal::F(Terminal::Number(0)))])
                    } else { unreachable!() })
    <F>::=([Number])                         (|list|
                    if let [Symbol::Terminal(n)] = list {
                        NonTerminal::F(n.clone())
                    } else { unreachable!() })
}

#[test]
fn test_parser_generator() {
    let parser = get_parser();
    use NonTerminal::*;
    use Terminal::*;
    assert_eq!(
        vec![Number(1), Plus, Number(2), Star, Number(3), Plus, Number(4)]
            .into_iter()
            .parse(&parser),
        Ok(E(vec![
            T(vec![F(Number(1))]),
            T(vec![F(Number(2)), F(Number(3))]),
            T(vec![F(Number(4))]),
        ]))
    );
}
