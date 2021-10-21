#[derive(Debug, PartialEq)]
pub enum Token {
    A(String, usize, usize),
    B(String, usize, usize),
    C(String, usize, usize),
}

use Token::*;
use tokenizer::Tokenize;
tokenizer_generator::tokenizer! {
    fn create_tokenizer() -> DFATokenizer {
        character (char, usize);
        token Token;
        "[a-zA-Z_][a-zA-Z0-9_]*": |s, a: Vec<(char, _)>| Token::A(s.to_string(), a[0].1, a.len());
        "0([xX][0-9a-fA-F]+|[dD][0-9]+|[oO][0-7]+|[bB][01]+)|[1-9][0-9]*|0": |s, a| Token::B(s.to_string(), a[0].1, a.len());
        ".|\n": |s, a| Token::C(s.to_string(), a[0].1, a.len());
    }
}

#[test]
fn tokenize_with() {
    let tokenizer = create_tokenizer();
    let tokens = "let mut test = 0xFF;"
        .chars()
        .scan(0, |state, item| {
            let i = *state;
            *state += 1;
            Some((item, i))
        })
        .tokenize_with(&tokenizer, |(c, _)| *c)
        .collect::<Vec<_>>();
    assert_eq!(
        tokens,
        vec![
            A("let".to_string(), 0, 3),
            C(" ".to_string(), 3, 1),
            A("mut".to_string(), 4, 3),
            C(" ".to_string(), 7, 1),
            A("test".to_string(), 8, 4),
            C(" ".to_string(), 12, 1),
            C("=".to_string(), 13, 1),
            C(" ".to_string(), 14, 1),
            B("0xFF".to_string(), 15, 4),
            C(";".to_string(), 19, 1),
        ]
    );

    let tokens = "1+0b10+0o7+0d9+0xf"
        .chars()
        .scan(0, |state, item| {
            let i = *state;
            *state += 1;
            Some((item, i))
        })
        .tokenize_with(&tokenizer, |(c, _)| *c)
        .collect::<Vec<_>>();
    assert_eq!(
        tokens,
        vec![
            B("1".to_string(), 0, 1),
            C("+".to_string(), 1, 1),
            B("0b10".to_string(), 2, 4),
            C("+".to_string(), 6, 1),
            B("0o7".to_string(), 7, 3),
            C("+".to_string(), 10, 1),
            B("0d9".to_string(), 11, 3),
            C("+".to_string(), 14, 1),
            B("0xf".to_string(), 15, 3),
        ]
    );

    let tokens = "01+0b2+0o8+0da+0xg"
        .chars()
        .scan(0, |state, item| {
            let i = *state;
            *state += 1;
            Some((item, i))
        })
        .tokenize_with(&tokenizer, |(c, _)| *c)
        .collect::<Vec<_>>();
    assert_eq!(
        tokens,
        vec![
            B("0".to_string(), 0, 1),
            B("1".to_string(), 1, 1),
            C("+".to_string(), 2, 1),
            B("0".to_string(), 3, 1),
            A("b2".to_string(), 4, 2),
            C("+".to_string(), 6, 1),
            B("0".to_string(), 7, 1),
            A("o8".to_string(), 8, 2),
            C("+".to_string(), 10, 1),
            B("0".to_string(), 11, 1),
            A("da".to_string(), 12, 2),
            C("+".to_string(), 14, 1),
            B("0".to_string(), 15, 1),
            A("xg".to_string(), 16, 2),
        ]
    );
}
