use parser::{enum_index, LR1Parser, Parse, Rule, Syntax};
use parser::enum_index_derive::*;
use parser::Symbol::{NonTerminal, Terminal};
use tokenizer::{DFATokenizer, Tokenize};

fn main() {
    #[derive(Debug, EnumIndex)]
    enum Token {
        Number(f64),
        Add,
        Sub,
        Mul,
        Div,
        Bracket,
        CloseBracket,
        Sqrt,
    }

    #[derive(Debug, EnumIndex)]
    enum ParseResult {
        Sum(Option<f64>),
        Product(Option<f64>),
        Block(Option<f64>),
    }

    let (tokenizer, _) = DFATokenizer::builder()
        .pattern("([0-9]+|[0-9]+\\.[0-9]*|[0-9]*\\.[0-9]+)([eE][\\+\\-]?[0-9]+)?", |s, _| Some(Token::Number(s.parse().unwrap())))
        .pattern("\\+", |_, _| Some(Token::Add))
        .pattern("\\-", |_, _| Some(Token::Sub))
        .pattern("\\*", |_, _| Some(Token::Mul))
        .pattern("/", |_, _| Some(Token::Div))
        .pattern("\\(", |_, _| Some(Token::Bracket))
        .pattern("\\)", |_, _| Some(Token::CloseBracket))
        .pattern("sqrt", |_, _| Some(Token::Sqrt))
        .pattern(".|\n", |_, _| None)
        .build().unwrap();
    let (parser, _) = LR1Parser::new(Syntax::builder()
        .rule(Rule::new(ParseResult::Sum(None),
                        &[NonTerminal(ParseResult::Sum(None)), Terminal(Token::Add), NonTerminal(ParseResult::Product(None))],
                        |list| if let [NonTerminal(ParseResult::Sum(a)), _, NonTerminal(ParseResult::Product(b))] = list {
                            ParseResult::Sum(a.and_then(|a| b.map(|b| a + b)))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Sum(None),
                        &[NonTerminal(ParseResult::Sum(None)), Terminal(Token::Sub), NonTerminal(ParseResult::Product(None))],
                        |list| if let [NonTerminal(ParseResult::Sum(a)), _, NonTerminal(ParseResult::Product(b))] = list {
                            ParseResult::Sum(a.and_then(|a| b.map(|b| a - b)))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Sum(None),
                        &[NonTerminal(ParseResult::Product(None))],
                        |list| if let [NonTerminal(ParseResult::Product(a))] = list {
                            ParseResult::Sum(*a)
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Product(None),
                        &[NonTerminal(ParseResult::Product(None)), Terminal(Token::Mul), NonTerminal(ParseResult::Block(None))],
                        |list| if let [NonTerminal(ParseResult::Product(a)), _, NonTerminal(ParseResult::Block(b))] = list {
                            ParseResult::Product(a.and_then(|a| b.map(|b| a * b)))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Product(None),
                        &[NonTerminal(ParseResult::Product(None)), Terminal(Token::Div), NonTerminal(ParseResult::Block(None))],
                        |list| if let [NonTerminal(ParseResult::Product(a)), _, NonTerminal(ParseResult::Block(b))] = list {
                            ParseResult::Product(a.and_then(|a| b.map(|b| a / b)))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Product(None),
                        &[NonTerminal(ParseResult::Block(None))],
                        |list| if let [NonTerminal(ParseResult::Block(a))] = list {
                            ParseResult::Product(*a)
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Block(None),
                        &[Terminal(Token::Number(0.0))],
                        |list| if let [Terminal(Token::Number(n))] = list {
                            ParseResult::Block(Some(*n))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Block(None),
                        &[Terminal(Token::Add), Terminal(Token::Number(0.0))],
                        |list| if let [_, Terminal(Token::Number(n))] = list {
                            ParseResult::Block(Some(*n))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Block(None),
                        &[Terminal(Token::Sub), Terminal(Token::Number(0.0))],
                        |list| if let [_, Terminal(Token::Number(n))] = list {
                            ParseResult::Block(Some(-*n))
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Block(None),
                        &[Terminal(Token::Bracket), NonTerminal(ParseResult::Sum(None)), Terminal(Token::CloseBracket)],
                        |list| if let [_, NonTerminal(ParseResult::Sum(n)), _] = list {
                            ParseResult::Block(*n)
                        } else { unreachable!() }))
        .rule(Rule::new(ParseResult::Block(None),
                        &[Terminal(Token::Sqrt), NonTerminal(ParseResult::Block(None))],
                        |list| if let [_, NonTerminal(ParseResult::Block(n))] = list {
                            ParseResult::Block(n.map(f64::sqrt))
                        } else { unreachable!() }))
        .build(ParseResult::Sum(None)));
    loop {
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).expect("failed to read input");
        let result = input.chars().tokenize(&tokenizer).flatten().parse(&parser);
        match result {
            Ok(ParseResult::Sum(Some(n))) => {
                println!("= {}", n);
            }
            Err(e) => {
                println!("{:?}", e);
            }
            _ => unreachable!()
        }
    }
}
