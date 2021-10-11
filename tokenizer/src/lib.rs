use std::borrow::Borrow;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::Debug;
use std::ops::Range;

pub use crate::tokenizer::iter::{Tokenize, TokenizeIterator};
pub use crate::tokenizer::DFATokenizer;

mod dfa;
mod nfa;
mod tokenizer;

#[derive(Eq, Hash, Clone)]
pub struct CharRange {
    pub range: Range<u32>,
}

impl Debug for CharRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CharRange")
            .field(
                "range",
                &if self.range.end - self.range.start == 1 {
                    char::try_from(self.range.start).unwrap_or('~').to_string()
                } else {
                    format!("{}..={}", char::try_from(self.range.start).unwrap_or('~'), char::try_from(self.range.end - 1).unwrap_or('~'))
                },
            )
            .finish()
    }
}

impl Borrow<u32> for CharRange {
    fn borrow(&self) -> &u32 {
        &self.range.start
    }
}

impl PartialEq for CharRange {
    fn eq(&self, other: &Self) -> bool {
        self.range.start == other.range.start
    }
}

impl PartialOrd for CharRange {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.range.start.partial_cmp(&other.range.start)
    }
}

impl Ord for CharRange {
    fn cmp(&self, other: &Self) -> Ordering {
        self.range.start.cmp(&other.range.start)
    }
}

#[cfg(test)]
mod tests {
    use crate::CharRange;

    #[test]
    fn char_range() {
        assert_eq!((CharRange { range: 0..2 }), (CharRange { range: 0..2 }));
        assert_eq!((CharRange { range: 0..2 }), (CharRange { range: 0..2 }));
        assert_eq!((CharRange { range: 0..2 }), (CharRange { range: 0..3 }));
        assert_eq!((CharRange { range: 0..3 }), (CharRange { range: 0..2 }));
        assert_ne!((CharRange { range: 0..2 }), (CharRange { range: 1..2 }));
        assert_ne!((CharRange { range: 1..2 }), (CharRange { range: 0..2 }));
        assert_ne!((CharRange { range: 0..2 }), (CharRange { range: 1..2 }));
        assert_ne!((CharRange { range: 1..2 }), (CharRange { range: 0..2 }));

        assert!((CharRange { range: 0..2 }) < (CharRange { range: 1..2 }));
        assert!((CharRange { range: 1..2 }) > (CharRange { range: 0..2 }));
        assert!((CharRange { range: 0..1 }) < (CharRange { range: 1..2 }));
        assert!((CharRange { range: 1..2 }) > (CharRange { range: 0..1 }));
    }
}
