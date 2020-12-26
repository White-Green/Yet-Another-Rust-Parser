use std::borrow::Borrow;
use std::cmp::Ordering;
use std::ops::Range;

mod nfa;
mod dfa;

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

#[derive(Eq, Hash, Clone, Debug)]
struct CharRange {
    range: Range<u32>,
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
