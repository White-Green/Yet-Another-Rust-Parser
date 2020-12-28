use core::clone::Clone;
use core::cmp::{Eq, PartialEq};
use core::convert::TryFrom;
use core::default::Default;
use core::hash::{Hash, Hasher};
use core::mem::drop;
use core::option::Option::Some;
use core::result::Result;
use core::result::Result::{Err, Ok};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::RwLock;
use std::sync::Weak;

use regex_syntax::hir::{Class, Hir, HirKind, Literal, RepetitionKind, RepetitionRange};

use crate::CharRange;


#[derive(Debug, Clone)]
pub(crate) struct TokenizerNFANodeRef<'a>(*const TokenizerNFANode<'a>, PhantomData<&'a ()>);

impl<'a> TokenizerNFANodeRef<'a> {
    fn new(ptr: *const TokenizerNFANode<'a>) -> Self {
        Self(ptr, Default::default())
    }
}

impl<'a> Deref for TokenizerNFANodeRef<'a> {
    type Target = TokenizerNFANode<'a>;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0 }
    }
}

impl<'a> PartialEq for TokenizerNFANodeRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<'a> Eq for TokenizerNFANodeRef<'a> {}

impl<'a> Hash for TokenizerNFANodeRef<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<'a> PartialOrd for TokenizerNFANodeRef<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<'a> Ord for TokenizerNFANodeRef<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[derive(Default, Debug)]
pub(crate) struct TokenizerNFANode<'a> {
    epsilon: HashSet<TokenizerNFANodeRef<'a>>,
    next: BTreeMap<CharRange, HashSet<TokenizerNFANodeRef<'a>>>,
}

impl<'a> TokenizerNFANode<'a> {
    fn reference(&self) -> TokenizerNFANodeRef<'a> {
        TokenizerNFANodeRef::new(self as *const Self)
    }

    pub(crate) fn next(&self) -> &BTreeMap<CharRange, HashSet<TokenizerNFANodeRef<'a>>> {
        &self.next
    }

    pub(crate) fn epsilon_recursive(&self) -> BTreeSet<TokenizerNFANodeRef<'a>> {
        let mut set = BTreeSet::new();
        let mut q = VecDeque::new();
        q.push_back(self.reference());
        while let Some(node) = q.pop_front() {
            if set.contains(&node) { continue; }
            for node in &node.epsilon {
                q.push_back(node.reference());
            }
            set.insert(node);
        }
        set
    }
}

#[derive(Debug)]
pub(crate) struct TokenizerNFA<'a> {
    node: Vec<Pin<Box<TokenizerNFANode<'a>>>>,
    begin: TokenizerNFANodeRef<'a>,
    end: Vec<TokenizerNFANodeRef<'a>>,
}

impl<'a> TokenizerNFA<'a> {
    pub(crate) fn begin(&self) -> &TokenizerNFANodeRef<'a> {
        &self.begin
    }

    pub(crate) fn end(&self) -> &Vec<TokenizerNFANodeRef<'a>> {
        &self.end
    }

    pub(crate) fn node(&self) -> Vec<TokenizerNFANodeRef<'a>> {
        self.node.iter().map(|n| n.reference()).collect()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum NFARegexConstructError {
    RegexError(regex_syntax::Error),
    ConstructError(NFAConstructError),
}

impl<'a> TryFrom<Vec<&str>> for TokenizerNFA<'a> {
    type Error = NFARegexConstructError;

    fn try_from(value: Vec<&str>) -> Result<Self, Self::Error> {
        let mut hir = Vec::new();
        for pattern in value {
            let mut parser = regex_syntax::Parser::new();
            hir.push(parser.parse(pattern).map_err(|e| NFARegexConstructError::RegexError(e))?);
        }
        Self::try_from(hir).map_err(|e| NFARegexConstructError::ConstructError(e))
    }
}

impl<'a> TryFrom<Vec<Hir>> for TokenizerNFA<'a> {
    type Error = NFAConstructError;

    fn try_from(value: Vec<Hir>) -> Result<Self, Self::Error> {
        let mut node = Vec::new();
        let mut begin = Box::pin(TokenizerNFANode::default());
        let mut end = Vec::new();
        let mut map = HashMap::new();
        for hir in value {
            let nfa = NFA::try_from(hir)?;
            map.clear();
            let base = node.len();
            for (arc, i) in nfa.node.iter().zip(base..) {
                map.insert(Arc::as_ptr(arc), i);
            }
            node.extend((0..nfa.node.len()).map(|_| Box::pin(TokenizerNFANode::default())));
            end.push(node[map[&Arc::as_ptr(&nfa.end)]].reference());
            begin.epsilon.insert(node[map[&Arc::as_ptr(&nfa.begin)]].reference());

            for (nfa_node, i) in nfa.node.iter().zip(base..) {
                let nfa_node = nfa_node.read().unwrap();
                for edge in &nfa_node.epsilon {
                    let reference = node[map[&edge.0.as_ptr()]].reference();
                    node[i].epsilon.insert(reference);
                }
                for (key, value) in &nfa_node.next {
                    let mut set = HashSet::new();
                    for edge in value {
                        let reference = node[map[&edge.0.as_ptr()]].reference();
                        set.insert(reference);
                    }
                    node[i].next.insert(key.clone(), set);
                }
            }
        }
        let begin_ref = begin.reference();
        node.push(begin);
        Ok(Self {
            node,
            begin: begin_ref,
            end,
        })
    }
}

#[derive(Debug)]
struct Edge(Weak<RwLock<NFANode>>);

impl Clone for Edge {
    fn clone(&self) -> Self {
        Edge(Weak::clone(&self.0))
    }
}

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0.as_ptr(), other.0.as_ptr())
    }
}

impl Eq for Edge {}

impl Hash for Edge {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state)
    }
}

#[derive(Default, Debug)]
struct NFANode {
    epsilon: HashSet<Edge>,
    next: BTreeMap<CharRange, HashSet<Edge>>,
}

struct NFA {
    node: Vec<Arc<RwLock<NFANode>>>,
    begin: Arc<RwLock<NFANode>>,
    end: Arc<RwLock<NFANode>>,
}

impl Clone for NFA {
    fn clone(&self) -> Self {
        let map: HashMap<_, _> = self.node.iter()
            .zip(0..)
            .map(|(arc, index)| (Arc::as_ptr(arc), index))
            .collect();
        let node: Vec<_> = self.node.iter()
            .map(|_| Arc::new(RwLock::new(NFANode { epsilon: HashSet::new(), next: BTreeMap::new() })))
            .collect();
        node.iter()
            .zip(self.node.iter())
            .for_each(|(new, old)| {
                let mut new = new.write().unwrap();
                let old = old.read().unwrap();
                new.epsilon = old.epsilon.iter()
                    .map(|weak| Edge(Arc::downgrade(&node[map[&weak.0.as_ptr()]])))
                    .collect();
                new.next = old.next.iter()
                    .map(|(k, v)|
                        (
                            k.clone(),
                            v.iter()
                                .map(|weak| Edge(Arc::downgrade(&node[map[&weak.0.as_ptr()]])))
                                .collect()
                        )
                    )
                    .collect();
            });
        let begin = Arc::clone(&node[map[&Arc::as_ptr(&self.begin)]]);
        let end = Arc::clone(&node[map[&Arc::as_ptr(&self.end)]]);
        NFA {
            node,
            begin,
            end,
        }
    }
}

impl TryFrom<Hir> for NFA {
    type Error = <NFA as TryFrom<HirKind>>::Error;

    fn try_from(value: Hir) -> Result<Self, Self::Error> {
        Self::try_from(value.into_kind())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum NFAConstructError {
    ByteLiteralIsNotSupported,
    BytesClassIsNotSupported,
    AnchorIsNotSupported,
    WordBoundaryIsNotSupported,
}

impl TryFrom<HirKind> for NFA {
    type Error = NFAConstructError;

    fn try_from(kind: HirKind) -> Result<Self, Self::Error> {
        match kind {
            HirKind::Empty => {
                let node: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                let weak = Edge(Arc::downgrade(&node));
                let mut guard = node.write().unwrap();
                guard.epsilon.insert(weak.clone());
                guard.next.insert(CharRange { range: '\u{0}' as u32..'\u{10ffff}' as u32 + 1 }, HashSet::from_iter(vec![weak]));
                drop(guard);
                Ok(NFA {
                    node: vec![Arc::clone(&node)],
                    begin: Arc::clone(&node),
                    end: node,
                })
            }
            HirKind::Literal(literal) => {
                if let Literal::Unicode(u) = literal {
                    let begin: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                    let end: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                    begin.write().unwrap().next.insert(CharRange { range: u as u32..u as u32 + 1 }, HashSet::from_iter(vec![Edge(Arc::downgrade(&end))]));
                    Ok(NFA {
                        node: vec![Arc::clone(&begin), Arc::clone(&end)],
                        begin,
                        end,
                    })
                } else {
                    Err(NFAConstructError::ByteLiteralIsNotSupported)
                }
            }
            HirKind::Class(class) => {
                if let Class::Unicode(class) = class {
                    let begin: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                    let end: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                    let mut guard = begin.write().unwrap();
                    for range in class.iter() {
                        guard.next.insert(CharRange { range: range.start() as u32..range.end() as u32 + 1 }, HashSet::from_iter(vec![Edge(Arc::downgrade(&end))]));
                    }
                    drop(guard);
                    Ok(NFA {
                        node: vec![Arc::clone(&begin), Arc::clone(&end)],
                        begin,
                        end,
                    })
                } else {
                    Err(NFAConstructError::BytesClassIsNotSupported)
                }
            }
            HirKind::Anchor(_) => { Err(NFAConstructError::AnchorIsNotSupported) }
            HirKind::WordBoundary(_) => { Err(NFAConstructError::WordBoundaryIsNotSupported) }
            HirKind::Repetition(repetition) => {
                let mut inner = NFA::try_from(repetition.hir.into_kind())?;
                match repetition.kind {
                    RepetitionKind::ZeroOrOne => {
                        inner.begin.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                        Ok(inner)
                    }
                    RepetitionKind::ZeroOrMore => {
                        inner.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                        inner.end = Arc::clone(&inner.begin);
                        Ok(inner)
                    }
                    RepetitionKind::OneOrMore => {
                        inner.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                        Ok(inner)
                    }
                    RepetitionKind::Range(range) => {
                        match range {
                            RepetitionRange::Exactly(n) => {
                                match n {
                                    0 => {
                                        let node = Arc::new(Default::default());
                                        Ok(NFA {
                                            node: vec![Arc::clone(&node)],
                                            begin: Arc::clone(&node),
                                            end: node,
                                        })
                                    }
                                    1 => {
                                        Ok(inner)
                                    }
                                    n => {
                                        let NFA { mut node, begin, mut end } = inner.clone();
                                        for _ in 0..n - 2 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            end = nfa.end;
                                        }
                                        node.append(&mut inner.node);
                                        end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        end = inner.end;
                                        Ok(NFA { node, begin, end })
                                    }
                                }
                            }
                            RepetitionRange::AtLeast(n) => {
                                match n {
                                    0 => {
                                        inner.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        inner.end = Arc::clone(&inner.begin);
                                        Ok(inner)
                                    }
                                    n => {
                                        let NFA { mut node, begin, mut end } = inner.clone();
                                        for _ in 0..n - 1 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            end = nfa.end;
                                        }
                                        end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        inner.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        inner.end = Arc::clone(&inner.begin);
                                        node.append(&mut inner.node);
                                        end = inner.end;
                                        Ok(NFA { node, begin, end })
                                    }
                                }
                            }
                            RepetitionRange::Bounded(n, m) => {
                                match (n, m) {
                                    (0, 0) => {
                                        let node = Arc::new(Default::default());
                                        Ok(NFA {
                                            node: vec![Arc::clone(&node)],
                                            begin: Arc::clone(&node),
                                            end: node,
                                        })
                                    }
                                    (0, 1) => {
                                        inner.begin.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                                        Ok(inner)
                                    }
                                    (0, n) => {
                                        let NFA { mut node, begin, mut end } = inner.clone();
                                        for _ in 0..n - 2 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            let mut guard = end.write().unwrap();
                                            guard.epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            guard.epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                                            drop(guard);
                                            end = nfa.end;
                                        }
                                        node.append(&mut inner.node);
                                        let mut guard = end.write().unwrap();
                                        guard.epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        guard.epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                                        drop(guard);
                                        end = inner.end;
                                        begin.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&end)));
                                        Ok(NFA { node, begin, end })
                                    }
                                    (1, 1) => {
                                        Ok(inner)
                                    }
                                    (n, m) if n == m => {
                                        let NFA { mut node, begin, mut end } = inner.clone();
                                        for _ in 0..n - 2 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            end = nfa.end;
                                        }
                                        node.append(&mut inner.node);
                                        end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        end = inner.end;
                                        Ok(NFA { node, begin, end })
                                    }
                                    (n, m) if n < m => {
                                        let NFA { mut node, begin, mut end } = inner.clone();
                                        for _ in 0..n - 1 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            end = nfa.end;
                                        }
                                        for _ in 0..m - n - 1 {
                                            let mut nfa = inner.clone();
                                            node.append(&mut nfa.node);
                                            let mut guard = end.write().unwrap();
                                            guard.epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                                            guard.epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                                            drop(guard);
                                            end = nfa.end;
                                        }
                                        node.append(&mut inner.node);
                                        let mut guard = end.write().unwrap();
                                        guard.epsilon.insert(Edge(Arc::downgrade(&inner.begin)));
                                        guard.epsilon.insert(Edge(Arc::downgrade(&inner.end)));
                                        drop(guard);
                                        end = inner.end;
                                        Ok(NFA { node, begin, end })
                                    }
                                    _ => unreachable!()
                                }
                            }
                        }
                    }
                }
            }
            HirKind::Group(group) => {
                Self::try_from(group.hir.into_kind())
            }
            HirKind::Concat(mut vec) => {
                let NFA { mut node, mut begin, end } = Self::try_from(vec.pop().unwrap())?;
                while let Some(hir) = vec.pop() {
                    let mut nfa = Self::try_from(hir)?;
                    node.append(&mut nfa.node);
                    nfa.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&begin)));
                    begin = nfa.begin;
                }
                Ok(NFA { node, begin, end })
            }
            HirKind::Alternation(vec) => {
                let mut node = Vec::new();
                let begin: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                let end: Arc<RwLock<NFANode>> = Arc::new(Default::default());
                node.push(Arc::clone(&begin));
                node.push(Arc::clone(&end));
                let mut guard = begin.write().unwrap();
                for hir in vec {
                    let mut nfa = Self::try_from(hir)?;
                    node.append(&mut nfa.node);
                    guard.epsilon.insert(Edge(Arc::downgrade(&nfa.begin)));
                    nfa.end.write().unwrap().epsilon.insert(Edge(Arc::downgrade(&end)));
                }
                drop(guard);
                Ok(NFA { node, begin, end })
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn tokenizer_nfa_to_index(nfa: &TokenizerNFA) -> (Vec<(BTreeSet<usize>, BTreeSet<(CharRange, BTreeSet<usize>)>)>, usize, Vec<usize>) {
    let mut map = HashMap::new();
    nfa.node.iter().zip(0usize..).for_each(|(edge, i)| { map.insert(edge.reference(), i); });
    (
        nfa.node.iter()
            .map(|node| {
                (
                    node.epsilon.iter()
                        .map(|edge| map[&edge])
                        .collect(),
                    node.next.iter()
                        .map(|(k, v)| {
                            (
                                k.clone(),
                                v.iter()
                                    .map(|edge| map[&edge])
                                    .collect()
                            )
                        })
                        .collect()
                )
            })
            .collect(),
        map[&nfa.begin],
        nfa.end.iter().map(|node_ref| map[node_ref]).collect()
    )
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap};
    use std::convert::TryFrom;
    use std::sync::Arc;

    use regex_syntax::hir::{Class, ClassUnicode, ClassUnicodeRange, Hir, Literal, Repetition, RepetitionKind, RepetitionRange};

    use crate::CharRange;
    use crate::nfa::{NFA, tokenizer_nfa_to_index, TokenizerNFA};

    macro_rules! seq {
        ($($a:expr),*)=>{std::iter::FromIterator::from_iter(vec![$($a),*].into_iter())}
    }

    #[test]
    fn construct_tokenizer_nfa() {
        assert_eq!(tokenizer_nfa_to_index(&TokenizerNFA::try_from(vec![Hir::literal(Literal::Unicode('a')), Hir::literal(Literal::Unicode('c')), Hir::literal(Literal::Unicode('e'))]).unwrap()),
                   (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'c' as u32..'c' as u32 + 1},seq![3])]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'e' as u32..'e' as u32 + 1},seq![5])]), (seq![], seq![]), (seq![0,2,4], seq![])], 6, vec![1, 3, 5]));
    }

    #[test]
    fn construct_nfa() {
        fn to_index(nfa: &NFA) -> (Vec<(BTreeSet<usize>, BTreeSet<(CharRange, BTreeSet<usize>)>)>, usize, usize) {
            let mut map = HashMap::new();
            nfa.node.iter().zip(0usize..).for_each(|(edge, i)| { map.insert(Arc::as_ptr(edge), i); });
            (
                nfa.node.iter()
                    .map(|node| {
                        let guard = node.read().unwrap();
                        (
                            guard.epsilon.iter()
                                .map(|edge| map[&edge.0.as_ptr()])
                                .collect(),
                            guard.next.iter()
                                .map(|(k, v)| {
                                    (
                                        k.clone(),
                                        v.iter()
                                            .map(|edge| map[&edge.0.as_ptr()])
                                            .collect()
                                    )
                                })
                                .collect()
                        )
                    })
                    .collect(),
                map[&Arc::as_ptr(&nfa.begin)],
                map[&Arc::as_ptr(&nfa.end)]
            )
        }
        assert_eq!(to_index(&NFA::try_from(Hir::empty()).unwrap()), (vec![(seq![0], seq![(CharRange{range:'\u{0}' as u32..'\u{10ffff}' as u32 + 1},seq![0])])], 0, 0));
        assert_eq!(to_index(&NFA::try_from(Hir::literal(Literal::Unicode('a'))).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::class(Class::Unicode(ClassUnicode::new(vec![ClassUnicodeRange::new('a', 'c'), ClassUnicodeRange::new('0', '3')])))).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'c' as u32 + 1},seq![1]), (CharRange{range: '0' as u32..'3' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::concat(vec![Hir::literal(Literal::Unicode('a')), Hir::literal(Literal::Unicode('b'))])).unwrap()), (vec![(seq![], seq![(CharRange{range: 'b' as u32..'b' as u32 + 1},seq![1])]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![0], seq![])], 2, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::concat(vec![Hir::literal(Literal::Unicode('a')), Hir::literal(Literal::Unicode('b')), Hir::literal(Literal::Unicode('c'))])).unwrap()),
                   (vec![(seq![], seq![(CharRange{range: 'c' as u32..'c' as u32 + 1},seq![1])]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'b' as u32..'b' as u32 + 1},seq![3])]), (seq![0], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![5])]), (seq![2], seq![])], 4, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::alternation(vec![Hir::literal(Literal::Unicode('a')), Hir::literal(Literal::Unicode('b'))])).unwrap()), (vec![(seq![2,4], seq![]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![1], seq![]), (seq![], seq![(CharRange{range: 'b' as u32..'b' as u32 + 1},seq![5])]), (seq![1], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::alternation(vec![Hir::literal(Literal::Unicode('a')), Hir::literal(Literal::Unicode('b')), Hir::literal(Literal::Unicode('c'))])).unwrap()),
                   (vec![(seq![2, 4, 6], seq![]), (seq![], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![1], seq![]), (seq![], seq![(CharRange{range: 'b' as u32..'b' as u32 + 1},seq![5])]), (seq![1], seq![]), (seq![], seq![(CharRange{range: 'c' as u32..'c' as u32 + 1},seq![7])]), (seq![1], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::ZeroOrOne,
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![1], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::ZeroOrMore,
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![0], seq![])], 0, 0));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::OneOrMore,
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![0], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Exactly(0)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![])], 0, 0));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Exactly(1)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Exactly(3)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![2], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![4], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![5])]), (seq![], seq![])], 0, 5));

        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::AtLeast(0)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![0], seq![])], 0, 0));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::AtLeast(1)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![2], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![2], seq![])], 0, 2));

        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(0, 0)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![])], 0, 0));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(0, 1)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![1], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(0, 2)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![3], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![2,3], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![], seq![])], 0, 3));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(1, 1)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![], seq![])], 0, 1));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(2, 2)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![2], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![], seq![])], 0, 3));
        assert_eq!(to_index(&NFA::try_from(Hir::repetition(Repetition {
            kind: RepetitionKind::Range(RepetitionRange::Bounded(1, 2)),
            greedy: false,
            hir: Box::new(Hir::literal(Literal::Unicode('a'))),
        })).unwrap()), (vec![(seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![1])]), (seq![2,3], seq![]), (seq![], seq![(CharRange{range: 'a' as u32..'a' as u32 + 1},seq![3])]), (seq![], seq![])], 0, 3));
    }
}
