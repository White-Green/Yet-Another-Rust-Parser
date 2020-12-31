use crate::tokenizer::Tokenizer;
use std::collections::VecDeque;
use std::iter::FusedIterator;
use std::ops::Deref;

pub struct TokenizeIterator<'a, I: Iterator<Item=char> + FusedIterator, E> {
    iter: I,
    queue: VecDeque<char>,
    tokenizer: Tokenizer<'a, E>,
}

pub trait Tokenize<E>: Sized + Iterator<Item=char> + FusedIterator {
    fn tokenize(self, tokenizer: Tokenizer<E>) -> TokenizeIterator<Self, E>;
}

impl<I: Iterator<Item=char> + FusedIterator, E> Tokenize<E> for I {
    fn tokenize(self, tokenizer: Tokenizer<E>) -> TokenizeIterator<Self, E> {
        TokenizeIterator {
            iter: self,
            queue: VecDeque::new(),
            tokenizer,
        }
    }
}

impl<'a, I: Iterator<Item=char> + FusedIterator, E> Iterator for TokenizeIterator<'a, I, E> {
    type Item = E;

    fn next(&mut self) -> Option<Self::Item> {
        let TokenizeIterator { iter, queue, tokenizer } = self;
        let mut current_node = tokenizer.dfa.begin();
        let mut last_matched_index = tokenizer.dfa.end(&current_node);
        let mut last_matched_length = 0;
        let mut i = 0;
        let mut chars = Vec::new();
        while let Some(c) = queue.pop_front().or_else(|| iter.next()) {
            i += 1;
            chars.push(c);
            if let Some(node) = current_node.next(c) {
                if let Some(index) = tokenizer.dfa.end(&node) {
                    last_matched_index = Some(index);
                    last_matched_length = i;
                }
                current_node = node;
            } else {
                break;
            }
        }
        if let Some(matched_index) = last_matched_index {
            while chars.len() > last_matched_length {
                queue.push_front(chars.pop().unwrap());
            }
            let s = chars.into_iter().collect::<String>();
            Some(tokenizer.enum_maker[matched_index](s.deref()))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tokenizer::iter::Tokenize;
    use crate::tokenizer::Tokenizer;
    use crate::dfa::{print_tokenizer_dfa_index, tokenizer_dfa_to_index};

    #[test]
    fn tokenize_iterator() {
        #[derive(Debug, PartialEq)]
        enum Token {
            A(String),
            B(String),
            C(String),
        }
        use Token::*;
        let tokenizer = || Tokenizer::builder()
            .add_pattern("[a-zA-Z_][a-zA-Z0-9_]*", |s| Token::A(s.to_string()))
            .add_pattern("0([xX][0-9a-fA-F]+|[dD][0-9]+|[oO][0-7]+|[bB][01]+)|[1-9][0-9]*|0", |s| Token::B(s.to_string()))
            .add_pattern(".|\n", |s| Token::C(s.to_string()))
            .build().unwrap().0;
        let tokens = "let mut test = 0xFF;".chars().tokenize(tokenizer()).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                A("let".to_string()),
                C(" ".to_string()),
                A("mut".to_string()),
                C(" ".to_string()),
                A("test".to_string()),
                C(" ".to_string()),
                C("=".to_string()),
                C(" ".to_string()),
                B("0xFF".to_string()),
                C(";".to_string()),
            ]
        );

        let tokens = "1+0b10+0o7+0d9+0xf".chars().tokenize(tokenizer()).collect::<Vec<_>>();
        assert_eq!(
            tokens,
            vec![
                B("1".to_string()),
                C("+".to_string()),
                B("0b10".to_string()),
                C("+".to_string()),
                B("0o7".to_string()),
                C("+".to_string()),
                B("0d9".to_string()),
                C("+".to_string()),
                B("0xf".to_string()),
            ]
        );

        let tokens = "01+0b2+0o8+0da+0xg".chars().tokenize(tokenizer()).collect::<Vec<_>>();
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
}
