#[derive(Debug, PartialEq)]
pub enum Token {
    A(String),
    B(String),
    C(String),
}

use Token::*;
use tokenizer::Tokenize;
tokenizer_generator::tokenizer! {
    character char;
    token Token;
    "[a-zA-Z_][a-zA-Z0-9_]*": (|s, _| Token::A(s.to_string()));
    "0([xX][0-9a-fA-F]+|[dD][0-9]+|[oO][0-7]+|[bB][01]+)|[1-9][0-9]*|0": (|s, _| Token::B(s.to_string()));
    ".|\n": (|s, _| Token::C(s.to_string()));
}

#[test]
fn tokenizer() {
    let tokenizer = get_tokenizer();
    let tokens = "let mut test = 0xFF;".chars().tokenize(&tokenizer).collect::<Vec<_>>();
    assert_eq!(tokens, vec![A("let".to_string()), C(" ".to_string()), A("mut".to_string()), C(" ".to_string()), A("test".to_string()), C(" ".to_string()), C("=".to_string()), C(" ".to_string()), B("0xFF".to_string()), C(";".to_string())]);

    let tokens = "1+0b10+0o7+0d9+0xf".chars().tokenize(&tokenizer).collect::<Vec<_>>();
    assert_eq!(tokens, vec![B("1".to_string()), C("+".to_string()), B("0b10".to_string()), C("+".to_string()), B("0o7".to_string()), C("+".to_string()), B("0d9".to_string()), C("+".to_string()), B("0xf".to_string())]);

    let tokens = "01+0b2+0o8+0da+0xg".chars().tokenize(&tokenizer).collect::<Vec<_>>();
    assert_eq!(
        tokens,
        vec![
            B("0".to_string()),
            B("1".to_string()),
            C("+".to_string()),
            B("0".to_string()),
            A("b2".to_string()),
            C("+".to_string()),
            B("0".to_string()),
            A("o8".to_string()),
            C("+".to_string()),
            B("0".to_string()),
            A("da".to_string()),
            C("+".to_string()),
            B("0".to_string()),
            A("xg".to_string()),
        ]
    );
}
