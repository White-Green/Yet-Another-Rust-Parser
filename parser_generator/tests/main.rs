use parser::enum_index_derive::EnumIndex;
use parser::{enum_index, Parse};
use parser_generator::parser;

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
        F(Plus,),
    }
    E
    <E>::=(<E>[Plus]<T>)                  (|list|
                    if let [Symbol::NonTerminal(E(vec)), _, Symbol::NonTerminal(T(v))] = *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(T(std::mem::take(v)));
                        E(vec)
                    } else { unreachable!() })
    <E>::=(<T>)                         (|list|
                    if let [Symbol::NonTerminal(T(vec))] = *list {
                        E(vec![T(std::mem::take(vec))])
                    } else { unreachable!() })
    <T>::=(<T>[Star]<F>)                  (|list|
                    if let [Symbol::NonTerminal(T(vec)), _, Symbol::NonTerminal(f)] = &mut *list {
                        let mut vec = std::mem::take(vec);
                        vec.push(std::mem::replace(f, F(Number(0))));
                        T(vec)
                    } else { unreachable!() })
    <T>::=(<F>)                         (|list|
                    if let [Symbol::NonTerminal(f)] = list {
                        T(vec![std::mem::replace(f, F(Number(0)))])
                    } else { unreachable!() })
    <F>::=([Number])                         (|list|
                    if let [Symbol::Terminal(n)] = list {
                        F(n.clone())
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
