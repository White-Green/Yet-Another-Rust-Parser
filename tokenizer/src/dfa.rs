use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::swap;
use std::ops::Deref;
use std::pin::Pin;

use crate::nfa::{TokenizerNFA, TokenizerNFANodeRef};
use crate::CharRange;

#[derive(Debug, Clone)]
pub(crate) struct TokenizerDFANodeRef<'a>(*const TokenizerDFANode<'a>, PhantomData<&'a ()>);

impl<'a> TokenizerDFANodeRef<'a> {
    fn new(ptr: *const TokenizerDFANode<'a>) -> Self {
        Self(ptr, Default::default())
    }
}

impl<'a> Deref for TokenizerDFANodeRef<'a> {
    type Target = TokenizerDFANode<'a>;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0 }
    }
}

impl<'a> PartialEq for TokenizerDFANodeRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<'a> Eq for TokenizerDFANodeRef<'a> {}

impl<'a> Hash for TokenizerDFANodeRef<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

#[derive(Default, Debug)]
pub(crate) struct TokenizerDFANode<'a> {
    next: BTreeMap<CharRange, TokenizerDFANodeRef<'a>>,
}

impl<'a> TokenizerDFANode<'a> {
    fn new() -> Self {
        Default::default()
    }

    pub(crate) fn reference(&self) -> TokenizerDFANodeRef<'a> {
        TokenizerDFANodeRef::new(self as *const Self)
    }

    pub(crate) fn next_map(&self) -> &BTreeMap<CharRange, TokenizerDFANodeRef<'a>> {
        &self.next
    }
}

pub(crate) struct TokenizerDFA<'a> {
    pub(crate) node: Vec<Pin<Box<TokenizerDFANode<'a>>>>,
    pub(crate) begin: TokenizerDFANodeRef<'a>,
    pub(crate) end: HashMap<TokenizerDFANodeRef<'a>, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DFAConstructWarning {
    EndConflict(usize, usize),
}

impl<'a, 'b> From<TokenizerNFA<'a>> for (TokenizerDFA<'b>, Vec<DFAConstructWarning>) {
    fn from(nfa: TokenizerNFA<'a>) -> Self {
        let mut warnings = Vec::new();

        let mut node = Vec::new();
        let mut node_ref = HashMap::new();
        let mut q = VecDeque::new();
        let begin = {
            let begin = Box::pin(TokenizerDFANode::new());
            let begin_node_ref = begin.reference();
            node.push(begin);
            let begin_nfa_node = nfa.begin().epsilon_recursive();
            q.push_back(begin_nfa_node.clone());
            node_ref.insert(begin_nfa_node, 0);
            begin_node_ref
        };
        let mut end = HashMap::new();
        let mut processed = HashSet::new();

        while let Some(current_node) = q.pop_front() {
            if !processed.insert(node_ref[&current_node]) {
                continue;
            }
            let mut next = BTreeMap::new();
            for node in &current_node {
                for (char_range, next_node) in node.next() {
                    next.entry(char_range.range.start).or_insert_with(BTreeMap::new).entry(char_range.range.end).or_insert_with(BTreeSet::new).append(&mut next_node.iter().map(|node| node.epsilon_recursive()).flatten().collect::<BTreeSet<_>>());
                }
            }

            let mut next_begin_map = next.into_iter().collect::<Vec<_>>();
            TokenizerDFA::align_by_begin(&mut next_begin_map);
            let next_map = TokenizerDFA::split_by_end(next_begin_map);
            for (range, next) in next_map {
                let next_ref = if node_ref.contains_key(&next) {
                    node[node_ref[&next]].reference()
                } else {
                    node_ref.insert(next.clone(), node.len());
                    let new_node = Box::pin(TokenizerDFANode::new());
                    let next_ref = new_node.reference();
                    node.push(new_node);
                    next_ref
                };
                q.push_back(next);
                node[node_ref[&current_node]].next.insert(range, next_ref);
            }
        }
        for (set, index) in node_ref {
            for (nfa_node, i) in nfa.end().iter().zip(0..nfa.end().len()).rev() {
                if set.contains(nfa_node) {
                    if let Some(old) = end.insert(node[index].reference(), i) {
                        warnings.push(DFAConstructWarning::EndConflict(old, i));
                    }
                }
            }
        }
        (TokenizerDFA { node, begin, end }, warnings)
    }
}

impl<'a> TokenizerDFA<'a> {
    pub(crate) fn minify<'b>(self) -> TokenizerDFA<'b> {
        let mut group_map = self
            .node
            .iter()
            .map(|node| {
                let node_ref = node.reference();
                let group = self.end.get(&node_ref).map_or(0, |i| *i + 1);
                (node_ref, group)
            })
            .collect::<HashMap<_, _>>();
        let mut new_group_map = group_map.clone();
        loop {
            let group_set = Self::create_group_set(&group_map);
            let mut max_index = 0;
            let mut updated = false;
            for set in &group_set {
                let mut split_group = HashMap::new();
                for node in set {
                    let node_next = &(*node).next;
                    let compressed_next = Self::compress_next(&group_map, node_next);
                    split_group.entry(compressed_next).or_insert_with(HashSet::new).insert(node.reference());
                }
                updated |= split_group.len() > 1;
                for (_, set) in split_group.into_iter() {
                    for node in set {
                        new_group_map.insert(node, max_index);
                    }
                    max_index += 1;
                }
            }
            if !updated {
                break;
            }
            swap(&mut group_map, &mut new_group_map);
        }
        let group_set = Self::create_group_set(&new_group_map);
        let mut node = Vec::with_capacity(group_set.len());
        for _ in 0..group_set.len() {
            node.push(Box::pin(TokenizerDFANode::new()));
        }
        for (set, i) in group_set.iter().zip(0..) {
            let map = Self::compress_next(&new_group_map, &(*set.iter().next().unwrap()).next);
            node[i].next = map.into_iter().map(|(k, v)| (k, node[v].reference())).collect();
        }
        let begin = node[new_group_map[&self.begin]].reference();
        let end = self.end.iter().map(|(k, v)| (node[new_group_map[k]].reference(), *v)).collect();
        TokenizerDFA { node, begin, end }
    }

    fn create_group_set<'b>(group_map: &HashMap<TokenizerDFANodeRef<'b>, usize>) -> Vec<HashSet<TokenizerDFANodeRef<'b>>> {
        let mut group_set = Vec::new();
        for (node_ref, &group) in group_map.iter() {
            if group >= group_set.len() {
                group_set.resize_with(group + 1, HashSet::new);
            }
            group_set[group].insert(node_ref.reference());
        }
        group_set
    }

    fn compress_next<'b>(group_map: &HashMap<TokenizerDFANodeRef<'b>, usize>, node_next: &BTreeMap<CharRange, TokenizerDFANodeRef<'b>>) -> BTreeMap<CharRange, usize> {
        let mut compressed_next = BTreeMap::new();
        let mut prev_begin = None;
        let mut prev_end = None;
        let mut prev_group = None;
        for (range, next) in node_next {
            let current_group = group_map[next];
            if let Some(prev_group) = prev_group {
                if prev_group != current_group || prev_end != Some(range.range.start) {
                    compressed_next.insert(CharRange { range: prev_begin.unwrap()..prev_end.unwrap() }, prev_group);
                    prev_begin = None;
                }
            }
            prev_begin = prev_begin.or(Some(range.range.start));
            prev_end = Some(range.range.end);
            prev_group = Some(current_group);
        }
        if let Some(prev_group) = prev_group {
            compressed_next.insert(CharRange { range: prev_begin.unwrap()..prev_end.unwrap() }, prev_group);
        }
        compressed_next
    }
}

impl<'a> TokenizerDFA<'a> {
    fn align_by_begin(next_begin_map: &mut Vec<(u32, BTreeMap<u32, BTreeSet<TokenizerNFANodeRef>>)>) {
        if next_begin_map.is_empty() {
            return;
        }
        for i in 0..next_begin_map.len() - 1 {
            let upper = next_begin_map[i + 1].0;
            let greater_keys = next_begin_map[i].1.range(upper + 1..).map(|(k, _)| *k).collect::<Vec<_>>();
            if !greater_keys.is_empty() {
                let mut greater_end_map = BTreeMap::new();
                let mut limit_next = BTreeSet::new();
                for key in greater_keys {
                    let mut greater_next = next_begin_map[i].1.remove(&key).unwrap();
                    greater_end_map.insert(key, greater_next.clone());
                    limit_next.append(&mut greater_next);
                }
                next_begin_map[i].1.entry(upper).or_insert_with(BTreeSet::new).append(&mut limit_next);
                for (end, mut greater_next) in greater_end_map {
                    next_begin_map[i + 1].1.entry(end).or_insert_with(BTreeSet::new).append(&mut greater_next);
                }
            }
        }
    }

    fn split_by_end(next_begin_map: Vec<(u32, BTreeMap<u32, BTreeSet<TokenizerNFANodeRef>>)>) -> Vec<(CharRange, BTreeSet<TokenizerNFANodeRef>)> {
        let mut result = Vec::new();
        for (begin, mut end_map) in next_begin_map {
            let mut vec = Vec::new();
            let mut begin = begin;
            for end in end_map.keys() {
                vec.push((CharRange { range: begin..*end }, BTreeSet::new()));
                begin = *end;
            }
            let mut next_sum = BTreeSet::new();
            for ((_, ref mut set), (_, ref mut next)) in vec.iter_mut().zip(end_map.iter_mut()).rev() {
                next_sum.append(next);
                set.append(&mut next_sum.clone());
            }
            result.append(&mut vec);
        }
        result
    }
}

#[cfg(test)]
pub(crate) fn tokenizer_dfa_to_index(dfa: &TokenizerDFA) -> (Vec<BTreeMap<CharRange, usize>>, usize, BTreeMap<usize, usize>) {
    let mut map = HashMap::new();
    for (edge, i) in dfa.node.iter().zip(0usize..) {
        map.insert(edge.reference(), i);
    }
    (dfa.node.iter().map(|node| node.next.iter().map(|(k, v)| (k.clone(), map[&v])).collect()).collect(), map[&dfa.begin], dfa.end.iter().map(|(node_ref, i)| (map[node_ref], *i)).collect())
}

#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn print_tokenizer_dfa_index(index: &(Vec<BTreeMap<CharRange, usize>>, usize, BTreeMap<usize, usize>)) {
    println!("digraph Automaton{{");
    for i in 0..index.0.len() {
        let option = if i == index.1 { "color=red, " } else { "" };
        let option = if index.2.contains_key(&i) { format!("{}shape = doublecircle, ", option) } else { format!("{}shape = circle, ", option) };
        println!("\tnode{}[{}label=\"{0}\"];", i, option);
    }
    for (x, i) in index.0.iter().zip(0..) {
        for (range, next) in x {
            println!("\tnode{}->node{}[label=\"{}{}\"]", i, next, char::try_from(range.range.start).unwrap_or('~'), if range.range.end - range.range.start == 1 { format!("") } else { format!("-{}", char::try_from(range.range.end - 1).unwrap_or('~')) });
        }
    }
    println!("}}");
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashSet, VecDeque};
    use std::convert::TryFrom;
    use std::iter::FromIterator;

    use rand::rngs::ThreadRng;
    use rand::Rng;
    use regex_syntax::hir::{Class, ClassUnicode, ClassUnicodeRange, Hir, Literal, Repetition, RepetitionKind, RepetitionRange};

    use crate::dfa::{tokenizer_dfa_to_index, DFAConstructWarning, TokenizerDFA};
    use crate::nfa::TokenizerNFA;
    use crate::CharRange;

    fn tokenizer_dfa_index_isomorphisms(a: &(Vec<BTreeMap<CharRange, usize>>, usize, BTreeMap<usize, usize>), b: &(Vec<BTreeMap<CharRange, usize>>, usize, BTreeMap<usize, usize>)) -> bool {
        if a.0.len() != b.0.len() {
            return false;
        }
        let mut map = vec![None; a.0.len()];
        map[a.1] = Some(b.1);
        let mut q = VecDeque::new();
        q.push_back(a.1);
        while let Some(i) = q.pop_front() {
            if a.0[i].len() != b.0[map[i].unwrap()].len() {
                return false;
            }
            for ((k1, v1), (k2, v2)) in a.0[i].iter().zip(b.0[map[i].unwrap()].iter()) {
                if k1 != k2 {
                    return false;
                }
                if map[*v1].is_none() {
                    map[*v1] = Some(*v2);
                    q.push_back(*v1);
                } else if map[*v1] != Some(*v2) {
                    return false;
                }
            }
        }

        for i in 0..a.0.len() {
            if a.0[i].len() != b.0[map[i].unwrap()].len() {
                return false;
            }
            for ((k1, v1), (k2, v2)) in a.0[i].iter().zip(b.0[map[i].unwrap()].iter()) {
                if k1 != k2 {
                    return false;
                }
                if map[*v1] != Some(*v2) {
                    return false;
                }
            }
        }

        if a.2.len() != b.2.len() {
            return false;
        }
        for (k, v) in a.2.iter() {
            if b.2.get(&map[*k].unwrap()) != Some(v) {
                return false;
            }
        }
        true
    }

    macro_rules! seq {
        ($($a:expr),*)=>{std::iter::FromIterator::from_iter(vec![$($a),*].into_iter())}
    }

    macro_rules! range {
        ($begin:expr) => {
            CharRange { range: $begin as u32..$begin as u32 + 1 }
        };
        ($begin:expr, $end:expr) => {
            CharRange { range: $begin as u32..$end as u32 + 1 }
        };
    }

    #[test]
    fn isomorphisms() {
        assert!(tokenizer_dfa_index_isomorphisms(
            &(
                vec![
                    seq![(CharRange { range: 0..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
            &(
                vec![
                    seq![(CharRange { range: 0..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
        ));
        assert!(tokenizer_dfa_index_isomorphisms(
            &(vec![seq![(CharRange { range: 0..10 }, 1)], seq![(CharRange { range: 1..11 }, 2)], seq![(CharRange { range: 2..12 }, 3)], seq![(CharRange { range: 3..13 }, 4)], seq![(CharRange { range: 4..14 }, 0)]], 0, seq![(2, 1), (3, 0), (4, 0)]),
            &(vec![seq![(CharRange { range: 4..14 }, 1)], seq![(CharRange { range: 0..10 }, 2)], seq![(CharRange { range: 1..11 }, 3)], seq![(CharRange { range: 2..12 }, 4)], seq![(CharRange { range: 3..13 }, 0)]], 1, seq![(3, 1), (4, 0), (0, 0)]),
        ));
        assert!(tokenizer_dfa_index_isomorphisms(
            &(
                vec![
                    seq![(CharRange { range: 0..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
            &(
                vec![
                    seq![(CharRange { range: 4..14 }, 1), (CharRange { range: 14..24 }, 2), (CharRange { range: 24..34 }, 3), (CharRange { range: 34..44 }, 4), (CharRange { range: 44..54 }, 0)],
                    seq![(CharRange { range: 0..10 }, 1), (CharRange { range: 10..20 }, 2), (CharRange { range: 20..30 }, 3), (CharRange { range: 30..40 }, 4), (CharRange { range: 40..50 }, 0)],
                    seq![(CharRange { range: 1..11 }, 1), (CharRange { range: 11..21 }, 2), (CharRange { range: 21..31 }, 3), (CharRange { range: 31..41 }, 4), (CharRange { range: 41..51 }, 0)],
                    seq![(CharRange { range: 2..12 }, 1), (CharRange { range: 12..22 }, 2), (CharRange { range: 22..32 }, 3), (CharRange { range: 32..42 }, 4), (CharRange { range: 42..52 }, 0)],
                    seq![(CharRange { range: 3..13 }, 1), (CharRange { range: 13..23 }, 2), (CharRange { range: 23..33 }, 3), (CharRange { range: 33..43 }, 4), (CharRange { range: 43..53 }, 0)]
                ],
                1,
                seq![(3, 1), (4, 0), (0, 0)]
            ),
        ));

        assert!(!tokenizer_dfa_index_isomorphisms(
            &(
                vec![
                    seq![(CharRange { range: 1..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
            &(
                vec![
                    seq![(CharRange { range: 4..14 }, 1), (CharRange { range: 14..24 }, 2), (CharRange { range: 24..34 }, 3), (CharRange { range: 34..44 }, 4), (CharRange { range: 44..54 }, 0)],
                    seq![(CharRange { range: 0..10 }, 1), (CharRange { range: 10..20 }, 2), (CharRange { range: 20..30 }, 3), (CharRange { range: 30..40 }, 4), (CharRange { range: 40..50 }, 0)],
                    seq![(CharRange { range: 1..11 }, 1), (CharRange { range: 11..21 }, 2), (CharRange { range: 21..31 }, 3), (CharRange { range: 31..41 }, 4), (CharRange { range: 41..51 }, 0)],
                    seq![(CharRange { range: 2..12 }, 1), (CharRange { range: 12..22 }, 2), (CharRange { range: 22..32 }, 3), (CharRange { range: 32..42 }, 4), (CharRange { range: 42..52 }, 0)],
                    seq![(CharRange { range: 3..13 }, 1), (CharRange { range: 13..23 }, 2), (CharRange { range: 23..33 }, 3), (CharRange { range: 33..43 }, 4), (CharRange { range: 43..53 }, 0)]
                ],
                1,
                seq![(3, 1), (4, 0), (0, 0)]
            ),
        ));
        assert!(!tokenizer_dfa_index_isomorphisms(
            &(
                vec![
                    seq![(CharRange { range: 0..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
            &(
                vec![
                    seq![(CharRange { range: 4..14 }, 1), (CharRange { range: 14..24 }, 2), (CharRange { range: 24..34 }, 3), (CharRange { range: 34..44 }, 4), (CharRange { range: 44..54 }, 0)],
                    seq![(CharRange { range: 0..10 }, 1), (CharRange { range: 10..20 }, 2), (CharRange { range: 20..30 }, 3), (CharRange { range: 30..40 }, 4), (CharRange { range: 40..50 }, 0)],
                    seq![(CharRange { range: 1..11 }, 1), (CharRange { range: 11..21 }, 2), (CharRange { range: 21..31 }, 3), (CharRange { range: 31..41 }, 4), (CharRange { range: 41..51 }, 0)],
                    seq![(CharRange { range: 2..12 }, 1), (CharRange { range: 12..22 }, 2), (CharRange { range: 22..32 }, 3), (CharRange { range: 32..42 }, 4), (CharRange { range: 42..52 }, 0)],
                    seq![(CharRange { range: 3..13 }, 1), (CharRange { range: 13..23 }, 2), (CharRange { range: 23..33 }, 3), (CharRange { range: 33..43 }, 4), (CharRange { range: 43..53 }, 0)]
                ],
                1,
                seq![(3, 1), (4, 0), (1, 0)]
            ),
        ));
        assert!(!tokenizer_dfa_index_isomorphisms(
            &(
                vec![
                    seq![(CharRange { range: 0..10 }, 0), (CharRange { range: 10..20 }, 1), (CharRange { range: 20..30 }, 2), (CharRange { range: 30..40 }, 3), (CharRange { range: 40..50 }, 4)],
                    seq![(CharRange { range: 1..11 }, 0), (CharRange { range: 11..21 }, 1), (CharRange { range: 21..31 }, 2), (CharRange { range: 31..41 }, 3), (CharRange { range: 41..51 }, 4)],
                    seq![(CharRange { range: 2..12 }, 0), (CharRange { range: 12..22 }, 1), (CharRange { range: 22..32 }, 2), (CharRange { range: 32..42 }, 3), (CharRange { range: 42..52 }, 4)],
                    seq![(CharRange { range: 3..13 }, 0), (CharRange { range: 13..23 }, 1), (CharRange { range: 23..33 }, 2), (CharRange { range: 33..43 }, 3), (CharRange { range: 43..53 }, 4)],
                    seq![(CharRange { range: 4..14 }, 0), (CharRange { range: 14..24 }, 1), (CharRange { range: 24..34 }, 2), (CharRange { range: 34..44 }, 3), (CharRange { range: 44..54 }, 4)]
                ],
                0,
                seq![(2, 1), (3, 0), (4, 0)]
            ),
            &(
                vec![
                    seq![(CharRange { range: 4..14 }, 1), (CharRange { range: 14..24 }, 2), (CharRange { range: 24..34 }, 3), (CharRange { range: 34..44 }, 4), (CharRange { range: 44..54 }, 0)],
                    seq![(CharRange { range: 0..10 }, 1), (CharRange { range: 10..20 }, 2), (CharRange { range: 20..30 }, 3), (CharRange { range: 30..40 }, 4), (CharRange { range: 40..50 }, 0)],
                    seq![(CharRange { range: 1..11 }, 1), (CharRange { range: 11..21 }, 2), (CharRange { range: 21..31 }, 3), (CharRange { range: 31..41 }, 4), (CharRange { range: 41..51 }, 0)],
                    seq![(CharRange { range: 2..12 }, 1), (CharRange { range: 12..22 }, 2), (CharRange { range: 22..32 }, 3), (CharRange { range: 32..42 }, 4), (CharRange { range: 42..52 }, 0)],
                    seq![(CharRange { range: 3..13 }, 1), (CharRange { range: 13..23 }, 2), (CharRange { range: 23..33 }, 3), (CharRange { range: 33..43 }, 4), (CharRange { range: 43..53 }, 0)]
                ],
                1,
                seq![(3, 1), (4, 0), (0, 1)]
            ),
        ));
    }

    #[test]
    fn construct_tokenizer_dfa() {
        let nfa = TokenizerNFA::try_from(vec![
            Hir::class(Class::Unicode(ClassUnicode::new(vec![ClassUnicodeRange::new('a', 'a')]))),
            Hir::class(Class::Unicode(ClassUnicode::new(vec![ClassUnicodeRange::new('a', 'c')]))),
            Hir::class(Class::Unicode(ClassUnicode::new(vec![ClassUnicodeRange::new('c', 'f')]))),
        ])
        .unwrap();
        let (dfa, warnings): (TokenizerDFA, Vec<_>) = nfa.into();
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa),
            &(
                vec![
                    seq![(CharRange { range: 'a' as u32..'a' as u32 + 1 }, 1), (CharRange { range: 'b' as u32..'b' as u32 + 1 }, 2), (CharRange { range: 'c' as u32..'c' as u32 + 1 }, 3), (CharRange { range: 'd' as u32..'f' as u32 + 1 }, 4)],
                    seq![],
                    seq![],
                    seq![],
                    seq![]
                ],
                0,
                seq![(1, 0), (2, 1), (3, 1), (4, 2)]
            )
        ));
        assert_eq!(HashSet::<DFAConstructWarning>::from_iter(warnings.into_iter()), seq![DFAConstructWarning::EndConflict(1, 0), DFAConstructWarning::EndConflict(2, 1)]);
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa.minify()),
            &(vec![seq![(CharRange { range: 'a' as u32..'a' as u32 + 1 }, 1), (CharRange { range: 'b' as u32..'c' as u32 + 1 }, 2), (CharRange { range: 'd' as u32..'f' as u32 + 1 }, 3)], seq![], seq![], seq![]], 0, seq![(1, 0), (2, 1), (3, 2)])
        ));

        let nfa = TokenizerNFA::try_from(vec!["([a-zA-Z]{2})*"]).unwrap();
        let (dfa, _) = nfa.into();
        let dfa: TokenizerDFA = dfa.minify();
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa),
            &(
                vec![seq![(CharRange { range: 'a' as u32..'z' as u32 + 1 }, 1), (CharRange { range: 'A' as u32..'Z' as u32 + 1 }, 1)], seq![(CharRange { range: 'a' as u32..'z' as u32 + 1 }, 0), (CharRange { range: 'A' as u32..'Z' as u32 + 1 }, 0)]],
                0,
                seq![(0, 0)]
            )
        ));

        let nfa = TokenizerNFA::try_from(vec!["(.|\\n){2,5}"]).unwrap();
        let (dfa, _) = nfa.into();
        let dfa: TokenizerDFA = dfa.minify();
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa),
            &(
                vec![
                    seq![(CharRange { range: 0..'\u{10ffff}' as u32 + 1 }, 1)],
                    seq![(CharRange { range: 0..'\u{10ffff}' as u32 + 1 }, 2)],
                    seq![(CharRange { range: 0..'\u{10ffff}' as u32 + 1 }, 3)],
                    seq![(CharRange { range: 0..'\u{10ffff}' as u32 + 1 }, 4)],
                    seq![(CharRange { range: 0..'\u{10ffff}' as u32 + 1 }, 5)],
                    seq![]
                ],
                0,
                seq![(2, 0), (3, 0), (4, 0), (5, 0)]
            )
        ));

        let nfa = TokenizerNFA::try_from(vec!["みみ[た-ゎ]", "てめた*", "ぺ[ぼ-るゎ-わ]*ぅ"]).unwrap();
        let (dfa, _) = nfa.into();
        let dfa: TokenizerDFA = dfa.minify();
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa),
            &(
                vec![
                    seq![(range!('み'), 1), (range!('て'), 4), (range!('ぺ'), 6)],
                    seq![(range!('み'), 2)],
                    seq![(range!('た', 'ゎ'), 3)],
                    seq![],
                    seq![(range!('め'), 5)],
                    seq![(range!('た'), 5)],
                    seq![(range!('ぼ', 'る'), 6), (range!('ゎ', 'わ'), 6), (range!('ぅ'), 7)],
                    seq![]
                ],
                0,
                seq![(3, 0), (5, 1), (7, 2)]
            )
        ));

        let nfa = TokenizerNFA::try_from(vec!["int|long", "[a-zA-Z][a-zA-Z0-9]*"]).unwrap();
        let (dfa, _) = nfa.into();
        let dfa: TokenizerDFA = dfa.minify();
        assert!(tokenizer_dfa_index_isomorphisms(
            &tokenizer_dfa_to_index(&dfa),
            &(
                vec![
                    seq![(range!('a', 'h'), 1), (range!('j', 'k'), 1), (range!('m', 'z'), 1), (range!('A', 'Z'), 1), (range!('i'), 2), (range!('l'), 5)],
                    seq![(range!('a', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1)],
                    seq![(range!('a', 'm'), 1), (range!('o', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1), (range!('n'), 3)],
                    seq![(range!('a', 's'), 1), (range!('u', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1), (range!('t'), 4)],
                    seq![(range!('a', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1)],
                    seq![(range!('a', 'n'), 1), (range!('p', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1), (range!('o'), 6)],
                    seq![(range!('a', 'm'), 1), (range!('o', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1), (range!('n'), 7)],
                    seq![(range!('a', 'f'), 1), (range!('h', 'z'), 1), (range!('A', 'Z'), 1), (range!('0', '9'), 1), (range!('g'), 4)]
                ],
                0,
                seq![(1, 1), (2, 1), (3, 1), (4, 0), (5, 1), (6, 1), (7, 1)]
            )
        ));

        // for i in 0..100 {
        //     let mut rng = rand::thread_rng();
        //
        //     let mut vec = vec![
        //         random_hir(&mut rng),
        //         random_hir(&mut rng),
        //         random_hir(&mut rng),
        //     ];
        //     println!("{}:{}", i, Hir::concat(vec));
        // }
    }

    #[allow(dead_code)]
    fn random_hir(rng: &mut ThreadRng) -> Hir {
        const CHAR_BEGIN: char = '0';
        const CHAR_END: char = '9';
        match rng.gen_range(0..5) {
            0 => Hir::literal(Literal::Unicode(rng.gen_range(CHAR_BEGIN..=CHAR_END))),
            1 => {
                let mut ranges = Vec::new();
                let mut min = CHAR_BEGIN as u32;
                loop {
                    let begin = rng.gen_range(min..=CHAR_END as u32 + if ranges.len() > 0 { 1 } else { 0 });
                    let end = rng.gen_range(begin..=CHAR_END as u32 + if ranges.len() > 0 { 1 } else { 0 });
                    if end - 1 == CHAR_END as u32 {
                        break;
                    }
                    ranges.push(ClassUnicodeRange::new(char::try_from(begin).unwrap(), char::try_from(end).unwrap()));
                    min = end + 1;
                }
                Hir::class(Class::Unicode(ClassUnicode::new(ranges)))
            }
            2 => {
                let kind = match rng.gen_range(0..4) {
                    0 => RepetitionKind::ZeroOrOne,
                    1 => RepetitionKind::ZeroOrMore,
                    2 => RepetitionKind::OneOrMore,
                    3 => {
                        let range = match rng.gen_range(0..3) {
                            0 => RepetitionRange::Exactly(rng.gen_range(2..10)),
                            1 => RepetitionRange::AtLeast(rng.gen_range(0..10)),
                            2 => {
                                let m = rng.gen_range(0..10);
                                RepetitionRange::Bounded(m, rng.gen_range(m..=10))
                            }
                            _ => unreachable!(),
                        };
                        RepetitionKind::Range(range)
                    }
                    _ => unreachable!(),
                };
                Hir::repetition(Repetition { kind, greedy: false, hir: Box::new(random_hir(rng)) })
            }
            3 => {
                let mut vec = Vec::new();
                for _ in 0..rng.gen_range(1..=3) {
                    vec.push(random_hir(rng));
                }
                Hir::concat(vec)
            }
            4 => {
                let mut vec = Vec::new();
                for _ in 0..rng.gen_range(1..=3) {
                    vec.push(random_hir(rng));
                }
                Hir::alternation(vec)
            }
            _ => unreachable!(),
        }
    }
}
