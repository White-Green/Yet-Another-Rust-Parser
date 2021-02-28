use std::collections::VecDeque;
use std::ops::Deref;

use crate::tokenizer::Tokenizer;

pub struct TokenizeIterator<'a, I: Iterator, E, F>
    where F: FnMut(&I::Item) -> char {
    iter: I,
    queue: VecDeque<I::Item>,
    map: F,
    tokenizer: Tokenizer<'a, E, I::Item>,
}

pub trait Tokenize<E>: Sized + Iterator {
    fn tokenize(self, tokenizer: Tokenizer<E, Self::Item>) -> TokenizeIterator<Self, E, fn(&char) -> char> where Self: Iterator<Item=char>;
    fn tokenize_with<F: FnMut(&Self::Item) -> char>(self, tokenizer: Tokenizer<E, Self::Item>, map: F) -> TokenizeIterator<Self, E, F>;
}

impl<I: Iterator, E> Tokenize<E> for I {
    fn tokenize(self, tokenizer: Tokenizer<E, I::Item>) -> TokenizeIterator<Self, E, fn(&char) -> char> where Self: Iterator<Item=char> {
        TokenizeIterator {
            iter: self,
            queue: VecDeque::new(),
            map: char::clone,
            tokenizer,
        }
    }

    fn tokenize_with<F: FnMut(&Self::Item) -> char>(self, tokenizer: Tokenizer<E, Self::Item>, map: F) -> TokenizeIterator<Self, E, F> {
        TokenizeIterator {
            iter: self,
            queue: VecDeque::new(),
            map,
            tokenizer,
        }
    }
}

impl<'a, I: Iterator, E, F: FnMut(&I::Item) -> char> Iterator for TokenizeIterator<'a, I, E, F> {
    type Item = E;

    fn next(&mut self) -> Option<Self::Item> {
        let TokenizeIterator { iter, queue, map, tokenizer } = self;
        let mut current_node = tokenizer.dfa.begin();
        let mut last_matched_index = tokenizer.dfa.accept_index(&current_node);
        let mut last_matched_length = 0;
        let mut i = 0;
        let mut items = Vec::new();
        let mut chars = Vec::new();
        while let Some(item) = queue.pop_front().or_else(|| iter.next()) {
            let c = map(&item);
            i += 1;
            items.push(item);
            chars.push(c);
            if let Some(node) = current_node.next(c) {
                if let Some(index) = tokenizer.dfa.accept_index(&node) {
                    last_matched_index = Some(index);
                    last_matched_length = i;
                }
                current_node = node;
            } else {
                break;
            }
        }
        if let Some(matched_index) = last_matched_index {
            while items.len() > last_matched_length {
                queue.push_front(items.pop().unwrap());
            }
            let s = chars.into_iter().take(last_matched_length).collect::<String>();
            Some(tokenizer.enum_maker[matched_index](s.deref(), std::mem::take(&mut items)))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tokenizer::iter::Tokenize;
    use crate::tokenizer::Tokenizer;

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
            .add_pattern("[a-zA-Z_][a-zA-Z0-9_]*", |s, _| Token::A(s.to_string()))
            .add_pattern("0([xX][0-9a-fA-F]+|[dD][0-9]+|[oO][0-7]+|[bB][01]+)|[1-9][0-9]*|0", |s, _| Token::B(s.to_string()))
            .add_pattern(".|\n", |s, _| Token::C(s.to_string()))
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

    #[test]
    fn tokenize_with() {
        #[derive(Debug, PartialEq)]
        enum Token {
            A(String, usize, usize),
            B(String, usize, usize),
            C(String, usize, usize),
        }
        use Token::*;
        let tokenizer = || Tokenizer::builder()
            .add_pattern("[a-zA-Z_][a-zA-Z0-9_]*", |s, a: Vec<(char, _)>| Token::A(s.to_string(), a[0].1, a.len()))
            .add_pattern("0([xX][0-9a-fA-F]+|[dD][0-9]+|[oO][0-7]+|[bB][01]+)|[1-9][0-9]*|0", |s, a| Token::B(s.to_string(), a[0].1, a.len()))
            .add_pattern(".|\n", |s, a| Token::C(s.to_string(), a[0].1, a.len()))
            .build().unwrap().0;

        let tokens = "let mut test = 0xFF;".chars()
            .scan(0, |state, item| {
                let i = *state;
                *state += 1;
                Some((item, i))
            })
            .tokenize_with(tokenizer(), |(c, _)| *c)
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

        let tokens = "1+0b10+0o7+0d9+0xf".chars()
            .scan(0, |state, item| {
                let i = *state;
                *state += 1;
                Some((item, i))
            })
            .tokenize_with(tokenizer(), |(c, _)| *c)
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

        let tokens = "01+0b2+0o8+0da+0xg".chars()
            .scan(0, |state, item| {
                let i = *state;
                *state += 1;
                Some((item, i))
            })
            .tokenize_with(tokenizer(), |(c, _)| *c)
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
}
