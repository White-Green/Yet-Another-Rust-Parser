use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use enum_index::EnumIndex;

use crate::{Rule, Syntax};
use crate::syntax::TerminalSymbol;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum SymbolInternal<N, T> {
    NonTerminal(N),
    Terminal(T),
}

#[derive(Debug)]
struct LR1Item<N, T> {
    rule: Rc<Rule<N, T>>,
    position: usize,
    lookahead_symbol: TerminalSymbolInterop,
}

impl<N, T> Clone for LR1Item<N, T> {
    fn clone(&self) -> Self {
        LR1Item {
            rule: self.rule.clone(),
            position: self.position,
            lookahead_symbol: self.lookahead_symbol.clone(),
        }
    }
}

impl<N, T> PartialEq for LR1Item<N, T> {
    fn eq(&self, other: &Self) -> bool {
        self.rule == other.rule &&
            self.position == other.position &&
            self.lookahead_symbol == other.lookahead_symbol
    }
}

impl<N, T> Eq for LR1Item<N, T> {}

impl<N, T> PartialOrd for LR1Item<N, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.rule.partial_cmp(&other.rule) {
            Some(Ordering::Equal) => {}
            other => return other
        }
        match self.position.partial_cmp(&other.position) {
            Some(Ordering::Equal) => {}
            other => return other
        }
        self.lookahead_symbol.partial_cmp(&other.lookahead_symbol)
    }
}

impl<N, T> Ord for LR1Item<N, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.rule.cmp(&other.rule) {
            Ordering::Equal => {}
            other => return other
        }
        match self.position.cmp(&other.position) {
            Ordering::Equal => {}
            other => return other
        }
        self.lookahead_symbol.cmp(&other.lookahead_symbol)
    }
}

impl<N, T> Hash for LR1Item<N, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rule.hash(state);
        self.position.hash(state);
        self.lookahead_symbol.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Action<State, Rule> {
    Shift(State),
    Reduce(Rule),
    Accept,
}

type NonTerminalSymbolInterop = usize;
type TerminalSymbolInterop = TerminalSymbol<usize>;
type StateInterop<N, T> = BTreeSet<LR1Item<N, T>>;
type SymbolInterop = SymbolInternal<NonTerminalSymbolInterop, TerminalSymbolInterop>;
type ActionInterop<N, T> = Action<StateInterop<N, T>, Rc<Rule<N, T>>>;
type GotoListInterop<N, T> = HashMap<SymbolInterop, StateInterop<N, T>>;
type NullSetInterop = BTreeSet<SymbolInterop>;
type FirstSetInterop = HashMap<SymbolInterop, BTreeSet<TerminalSymbolInterop>>;
type ActionTableInterop<N, T> = HashMap<StateInterop<N, T>, HashMap<TerminalSymbolInterop, ActionInterop<N, T>>>;
type GotoTableInterop<N, T> = HashMap<StateInterop<N, T>, HashMap<NonTerminalSymbolInterop, StateInterop<N, T>>>;

fn calc_goto<N, T>(set: &StateInterop<N, T>, syntax: &Syntax<N, T>, null: &NullSetInterop, first: &FirstSetInterop) -> GotoListInterop<N, T> {
    let mut goto = HashMap::new();
    for item in set {
        if let Some(symbol) = item.rule.symbols.get(item.position) {
            goto.entry(symbol.clone())
                .or_insert_with(|| BTreeSet::new())
                .insert(LR1Item {
                    rule: item.rule.clone(),
                    position: item.position + 1,
                    lookahead_symbol: item.lookahead_symbol.clone(),
                });
        }
    }
    for (_, set) in &mut goto {
        calc_closure(set, syntax, null, first);
    }
    goto
}

fn calc_closure<N, T>(set: &mut StateInterop<N, T>, syntax: &Syntax<N, T>, null: &NullSetInterop, first: &FirstSetInterop) {
    let mut rules = HashMap::new();
    for rule in &syntax.rules {
        rules.entry(rule.non_terminal)
            .or_insert_with(|| BTreeSet::new())
            .insert(rule);
    }
    loop {
        let mut update = BTreeSet::new();
        for item in set.iter() {
            let non_terminal = if let Some(SymbolInternal::NonTerminal(non_terminal)) = item.rule.symbols.get(item.position) {
                *non_terminal
            } else {
                continue;
            };
            let lookahead_symbol = SymbolInternal::Terminal(item.lookahead_symbol.clone());
            let follow = item.rule.symbols.get(item.position + 1..).unwrap_or(&[]).iter().chain(Some(&lookahead_symbol));
            for lookahead_symbol in get_first(follow, null, first) {
                for rule in &rules[&non_terminal] {
                    update.insert(LR1Item {
                        rule: Rc::clone(rule),
                        position: 0,
                        lookahead_symbol: lookahead_symbol.clone(),
                    });
                }
            }
        }
        let mut updated = false;
        for item in update {
            updated |= set.insert(item);
        }
        if !updated { break; }
    }
}

fn get_first<'a>(string: impl Iterator<Item=&'a SymbolInterop>, null: &NullSetInterop, first: &FirstSetInterop) -> BTreeSet<TerminalSymbolInterop> {
    let mut result = BTreeSet::new();
    for symbol in string {
        if let SymbolInternal::Terminal(symbol) = symbol {
            result.insert(symbol.clone());
        } else {
            for symbol in first.get(symbol).map(|set| set.iter()).into_iter().flatten().cloned() {
                result.insert(symbol);
            }
        }
        if !null.contains(symbol) { break; }
    }
    result
}

fn calc_null<N, T>(syntax: &Syntax<N, T>) -> NullSetInterop {
    let mut null = BTreeSet::new();
    loop {
        let mut updated = false;
        for rule in &syntax.rules {
            if null.contains(&SymbolInternal::NonTerminal(rule.non_terminal)) { continue; }
            if rule.symbols.iter().all(|symbol| null.contains(symbol))
            {
                null.insert(SymbolInternal::NonTerminal(rule.non_terminal));
                updated = true;
            }
        }
        if !updated { break; }
    }
    null
}

fn calc_first<N, T>(syntax: &Syntax<N, T>, null: &NullSetInterop) -> FirstSetInterop {
    let mut first = HashMap::new();
    for rule in &syntax.rules {
        for symbol in &rule.symbols {
            if let SymbolInternal::Terminal(t) = symbol {
                first.entry(symbol.clone())
                    .or_insert_with(|| BTreeSet::new())
                    .insert(t.clone());
            }
        }
    }

    loop {
        let mut updated = false;
        for rule in &syntax.rules {
            let mut update = BTreeSet::new();
            for symbol in &rule.symbols {
                if let Some(first) = first.get(&symbol) {
                    first.iter().cloned().for_each(|item| { update.insert(item); });
                }
                if !null.contains(&symbol) { break; }
            }
            let set = first.entry(SymbolInternal::NonTerminal(rule.non_terminal))
                .or_insert_with(|| BTreeSet::new());
            for item in update {
                updated |= set.insert(item);
            }
        }
        if !updated { break; }
    }

    first
}

#[derive(Debug, Clone, PartialEq)]
pub enum CalcTableWarning<State, N, T> {
    ShiftReduce { state: State, shift: State, reduce: Rc<Rule<N, T>> },
    ReduceReduce { state: State, actions: [Rc<Rule<N, T>>; 2] },
}

fn calc_table<N, T>(state_list: HashMap<StateInterop<N, T>, GotoListInterop<N, T>>, start_rule: &Rc<Rule<N, T>>) -> (ActionTableInterop<N, T>, GotoTableInterop<N, T>, Vec<CalcTableWarning<StateInterop<N, T>, N, T>>) {
    let mut action_table = HashMap::new();
    let mut goto_table = HashMap::new();
    let mut warnings = Vec::new();
    for (state, goto_list) in state_list {
        let mut action = HashMap::new();
        let mut goto = HashMap::new();
        for (symbol, goto_state) in goto_list {
            match symbol {
                SymbolInternal::NonTerminal(symbol) => { goto.insert(symbol, goto_state); }
                SymbolInternal::Terminal(symbol) => { action.insert(symbol, Action::Shift(goto_state)); }
            }
        }
        let current_state = state.clone();
        for item in state {
            if item.position == item.rule.symbols.len() {
                if &item.rule == start_rule {
                    action.insert(TerminalSymbol::EOI, Action::Accept);
                } else {
                    match action.get(&item.lookahead_symbol) {
                        None => { action.insert(item.lookahead_symbol, Action::Reduce(item.rule)); }
                        Some(Action::Shift(shift)) => { warnings.push(CalcTableWarning::ShiftReduce { state: current_state.clone(), shift: shift.clone(), reduce: item.rule }); }
                        Some(Action::Reduce(reduce)) => { warnings.push(CalcTableWarning::ReduceReduce { state: current_state.clone(), actions: [reduce.clone(), item.rule] }); }
                        Some(Action::Accept) => unreachable!(),
                    }
                }
            }
        }
        if !goto.is_empty() {
            goto_table.insert(current_state.clone(), goto);
        }
        action_table.insert(current_state, action);
    }
    (action_table, goto_table, warnings)
}

fn calc_all_goto<N, T>(syntax: &Syntax<N, T>, start_state: StateInterop<N, T>, null: &NullSetInterop, first: &FirstSetInterop) -> HashMap<StateInterop<N, T>, GotoListInterop<N, T>> {
    let mut q = VecDeque::new();
    q.push_back(start_state);
    let mut state_list = HashMap::new();
    while let Some(state) = q.pop_front() {
        if state_list.contains_key(&state) { continue; }
        let goto = calc_goto(&state, &syntax, &null, &first);
        for (_, new_state) in &goto {
            q.push_back(new_state.clone());
        }
        state_list.insert(state, goto);
    }
    state_list
}

fn calc_error_rules<N, T>(state_index: &HashMap<StateInterop<N, T>, usize>) -> HashMap<usize, HashSet<Rc<Rule<N, T>>>> {
    let mut error_rules = HashMap::new();
    for (item_list, index) in state_index {
        let mut set = HashSet::new();
        for item in item_list {
            if item.rule.symbols.get(item.position) == Some(&SymbolInternal::Terminal(TerminalSymbol::Error)) {
                set.insert(Rc::clone(&item.rule));
            }
        }
        if !set.is_empty() { error_rules.insert(*index, set); }
    }
    error_rules.shrink_to_fit();
    error_rules
}

#[derive(Debug, Clone, PartialEq)]
pub struct LR1Parser<N, T> {
    pub(crate) action_table: HashMap<usize, HashMap<TerminalSymbol<usize>, Action<usize, Rc<Rule<N, T>>>>>,
    pub(crate) goto_table: HashMap<usize, HashMap<usize, usize>>,
    pub(crate) error_rules: HashMap<usize, HashSet<Rc<Rule<N, T>>>>,
    pub(crate) start: usize,
}

impl<N: EnumIndex, T: EnumIndex> LR1Parser<N, T> {
    pub fn new(mut syntax: Syntax<N, T>) -> (Self, Vec<CalcTableWarning<usize, N, T>>) {
        let start_symbol = {
            let mut non_terminal_symbols = BTreeSet::new();
            for rule in &syntax.rules {
                non_terminal_symbols.insert(rule.non_terminal);
                for symbol in &rule.symbols {
                    if let SymbolInternal::NonTerminal(non_terminal) = symbol {
                        non_terminal_symbols.insert(*non_terminal);
                    }
                }
            }
            (0..).into_iter().find(|i| !non_terminal_symbols.contains(i)).unwrap()
        };
        let start_rule = Rule::builder_raw(start_symbol).non_terminal_raw(syntax.start).build(|_| unimplemented!());
        let start_rule = Rc::new(start_rule);
        syntax.rules.push(start_rule.clone());
        let null = calc_null(&syntax);
        let first = calc_first(&syntax, &null);
        let mut start_state = vec![LR1Item { rule: start_rule.clone(), position: 0, lookahead_symbol: TerminalSymbol::EOI }].into_iter().collect();
        calc_closure(&mut start_state, &syntax, &null, &first);
        let state_list = calc_all_goto(&syntax, start_state.clone(), &null, &first);

        let mut state_index = HashMap::new();
        let mut i = 0usize;
        for (state, _) in &state_list {
            state_index.insert(state.clone(), i);
            i += 1;
        }
        let (action_table, goto_table, warnings) = calc_table(state_list, &start_rule);
        let mut action_table: HashMap<_, _> = action_table.into_iter()
            .map(|(state, action)| (
                *state_index.get(&state).unwrap(),
                action.into_iter()
                    .map(|(symbol, action)| (
                        symbol,
                        match action {
                            Action::Shift(state) => Action::Shift(*state_index.get(&state).unwrap()),
                            Action::Reduce(rule) => Action::Reduce(rule),
                            Action::Accept => Action::Accept
                        }
                    ))
                    .collect()
            ))
            .collect();
        let mut goto_table: HashMap<_, _> = goto_table.into_iter()
            .map(|(state, goto)| (
                *state_index.get(&state).unwrap(),
                goto.into_iter()
                    .map(|(non_terminal, state)| (
                        non_terminal,
                        *state_index.get(&state).unwrap()
                    ))
                    .collect()
            ))
            .collect();
        let warnings = warnings.into_iter()
            .map(|warning| match warning {
                CalcTableWarning::ShiftReduce { state, shift, reduce } => CalcTableWarning::ShiftReduce { state: *state_index.get(&state).unwrap(), shift: *state_index.get(&shift).unwrap(), reduce },
                CalcTableWarning::ReduceReduce { state, actions } => CalcTableWarning::ReduceReduce { state: *state_index.get(&state).unwrap(), actions }
            })
            .collect();
        action_table.shrink_to_fit();
        goto_table.shrink_to_fit();
        (LR1Parser { action_table, goto_table, error_rules: calc_error_rules(&state_index), start: *state_index.get(&start_state).unwrap() }, warnings)
    }
}

impl<N: EnumIndex, T: EnumIndex> From<Syntax<N, T>> for LR1Parser<N, T> {
    fn from(syntax: Syntax<N, T>) -> Self {
        Self::new(syntax).0
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::fmt::Debug;
    use std::rc::Rc;

    use enum_index::EnumIndex;
    use enum_index_derive::*;

    use crate::{Rule, Syntax};
    use crate::parser::{Action, calc_closure, calc_first, calc_goto, calc_null, LR1Item, LR1Parser, SymbolInternal};
    use crate::syntax::TerminalSymbol;

    #[test]
    fn null() {
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N { A, B, C }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T { A, B }
        let syntax = Syntax::builder()
            .rule(Rule::builder(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A).build(|_| N::A))
            .rule(Rule::builder(N::A).non_terminal(N::C).terminal(T::B).build(|_| N::A))
            .rule(Rule::builder(N::B).non_terminal(N::C).build(|_| N::B))
            .rule(Rule::builder(N::B).non_terminal(N::A).build(|_| N::B))
            .rule(Rule::builder(N::C).build(|_| N::C))
            .build(N::A);
        assert_eq!(calc_null(&syntax), vec![SymbolInternal::NonTerminal(N::C.enum_index()), SymbolInternal::NonTerminal(N::B.enum_index())].into_iter().collect())
    }

    #[test]
    fn first() {
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N { A, B, C }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T { A, B }
        let syntax = Syntax::builder()
            .rule(Rule::builder(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A).build(|_| N::A))
            .rule(Rule::builder(N::A).non_terminal(N::C).terminal(T::B).build(|_| N::A))
            .rule(Rule::builder(N::B).non_terminal(N::C).build(|_| N::B))
            .rule(Rule::builder(N::B).non_terminal(N::A).build(|_| N::B))
            .rule(Rule::builder(N::C).build(|_| N::C))
            .build(N::A);
        let first = calc_first(&syntax, &calc_null(&syntax));
        assert_eq!(first[&SymbolInternal::NonTerminal(N::A.enum_index())], vec![(TerminalSymbol::Symbol(T::A.enum_index())), (TerminalSymbol::Symbol(T::B.enum_index()))].into_iter().collect());
        assert_eq!(first[&SymbolInternal::NonTerminal(N::B.enum_index())], vec![(TerminalSymbol::Symbol(T::A.enum_index())), (TerminalSymbol::Symbol(T::B.enum_index()))].into_iter().collect());
        assert_eq!(first[&SymbolInternal::NonTerminal(N::C.enum_index())], vec![].into_iter().collect());
        assert_eq!(first[&SymbolInternal::Terminal(TerminalSymbol::Symbol(T::A.enum_index()))], vec![(TerminalSymbol::Symbol(T::A.enum_index()))].into_iter().collect());
        assert_eq!(first[&SymbolInternal::Terminal(TerminalSymbol::Symbol(T::B.enum_index()))], vec![(TerminalSymbol::Symbol(T::B.enum_index()))].into_iter().collect());
    }

    #[test]
    fn closure() {
        #[derive(EnumIndex, Debug)]
        enum NonTerminal { E, T, F }
        #[derive(EnumIndex, Debug)]
        enum Terminal { Plus, Star, Bracket, CloseBracket, I }
        use NonTerminal::*;
        use Terminal::*;
        let mut syntax = Syntax::builder()
            .rule(Rule::builder(E).non_terminal(E).terminal(Plus).non_terminal(T).build(|_| E))
            .rule(Rule::builder(E).non_terminal(T).build(|_| E))
            .rule(Rule::builder(T).non_terminal(T).terminal(Star).non_terminal(F).build(|_| T))
            .rule(Rule::builder(T).non_terminal(F).build(|_| T))
            .rule(Rule::builder(F).terminal(Bracket).non_terminal(E).terminal(CloseBracket).build(|_| F))
            .rule(Rule::builder(F).terminal(I).build(|_| F))
            .build(E);
        let start_rule = Rc::new(Rule::builder_raw(3).non_terminal(E).build(|_| unreachable!()));
        syntax.rules.push(Rc::clone(&start_rule));
        let mut start_state = vec![LR1Item {
            rule: start_rule.clone(),
            position: 0,
            lookahead_symbol: TerminalSymbol::EOI,
        }].into_iter().collect();
        let null = calc_null(&syntax);
        let first = calc_first(&syntax, &null);
        calc_closure(&mut start_state, &syntax, &null, &first);
        assert_eq!(start_state, vec![
            LR1Item {
                rule: start_rule.clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Star.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Star.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Star.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Plus.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(Star.enum_index()),
            },
        ].into_iter().collect());
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N { A, B, C }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T { A, B, C }
        let syntax = Syntax::builder()
            .rule(Rule::builder(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A).build(|_| N::A))
            .rule(Rule::builder(N::A).non_terminal(N::C).terminal(T::B).build(|_| N::A))
            .rule(Rule::builder(N::B).non_terminal(N::C).build(|_| N::B))
            .rule(Rule::builder(N::B).non_terminal(N::A).build(|_| N::B))
            .rule(Rule::builder(N::C).terminal(T::C).build(|_| N::C))
            .rule(Rule::builder(N::C).build(|_| N::C))
            .build(N::A);
        let null = calc_null(&syntax);
        let first = calc_first(&syntax, &null);
        let mut closure = vec![LR1Item {
            rule: syntax.rules[0].clone(),
            position: 0,
            lookahead_symbol: TerminalSymbol::EOI,
        }].into_iter().collect();
        calc_closure(&mut closure, &syntax, &null, &first);
        assert_eq!(closure, vec![
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[1].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[2].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[3].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::B.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[4].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::B.enum_index()),
            },
            LR1Item {
                rule: syntax.rules[5].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
            },
        ].into_iter().collect());
    }

    #[test]
    fn goto() {
        #[derive(Debug, PartialEq, EnumIndex)]
        enum N { A, B, C }
        #[derive(Debug, PartialEq, EnumIndex)]
        enum T { A, B, C }
        let syntax = Syntax::builder()
            .rule(Rule::builder(N::A).non_terminal(N::B).non_terminal(N::C).terminal(T::A).build(|_| N::A))
            .rule(Rule::builder(N::A).non_terminal(N::C).terminal(T::B).build(|_| N::A))
            .rule(Rule::builder(N::B).non_terminal(N::C).build(|_| N::B))
            .rule(Rule::builder(N::B).non_terminal(N::A).build(|_| N::B))
            .rule(Rule::builder(N::C).terminal(T::C).build(|_| N::C))
            .rule(Rule::builder(N::C).build(|_| N::C))
            .build(N::A);
        let null = calc_null(&syntax);
        let first = calc_first(&syntax, &null);
        let closure = {
            let mut closure = vec![LR1Item {
                rule: syntax.rules[0].clone(),
                position: 0,
                lookahead_symbol: TerminalSymbol::EOI,
            }].into_iter().collect();
            calc_closure(&mut closure, &syntax, &null, &first);
            closure
        };
        let goto = calc_goto(&closure, &syntax, &null, &first);
        assert_eq!(goto, vec![
            (SymbolInternal::Terminal(TerminalSymbol::Symbol(T::C.enum_index())),
             vec![
                 LR1Item {
                     rule: syntax.rules[4].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[4].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::B.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[4].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
                 },
             ].into_iter().collect()
            ),
            (SymbolInternal::NonTerminal(N::A.enum_index()),
             vec![
                 LR1Item {
                     rule: syntax.rules[3].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[3].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
                 },
             ].into_iter().collect()),
            (SymbolInternal::NonTerminal(N::B.enum_index()),
             vec![
                 LR1Item {
                     rule: syntax.rules[0].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::EOI,
                 },
                 LR1Item {
                     rule: syntax.rules[0].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[0].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[4].clone(),
                     position: 0,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[5].clone(),
                     position: 0,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
             ].into_iter().collect()),
            (SymbolInternal::NonTerminal(N::C.enum_index()),
             vec![
                 LR1Item {
                     rule: syntax.rules[1].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[1].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[2].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::A.enum_index()),
                 },
                 LR1Item {
                     rule: syntax.rules[2].clone(),
                     position: 1,
                     lookahead_symbol: TerminalSymbol::Symbol(T::C.enum_index()),
                 },
             ].into_iter().collect())
        ].into_iter().collect());
    }

    fn parser_isomorphisms<N, T>(parser_a: &LR1Parser<N, T>, parser_b: &LR1Parser<N, T>) -> bool {
        let mut map = HashMap::new();
        map.insert(parser_a.start, parser_b.start);
        let mut q = VecDeque::new();
        q.push_back(parser_a.start);
        while let Some(state) = q.pop_front() {
            let a = parser_a.action_table.get(&state).unwrap();
            let b = if let Some(b) = parser_b.action_table.get(map.get(&state).unwrap()) { b } else { return false; };
            for (symbol, action_a) in a {
                let action_b = if let Some(action) = b.get(symbol) { action } else { return false; };
                match (action_a, action_b) {
                    (Action::Shift(shift_a), Action::Shift(shift_b)) if !map.contains_key(shift_a) => {
                        map.insert(*shift_a, *shift_b);
                        q.push_back(*shift_a);
                    }
                    (Action::Shift(shift_a), Action::Shift(shift_b)) if map.get(shift_a).unwrap() == shift_b => {}
                    (Action::Reduce(rule_a), Action::Reduce(rule_b)) if rule_a == rule_b => {}
                    (Action::Accept, Action::Accept) => {}
                    _ => return false,
                }
            }
            let (a, b) = match (parser_a.goto_table.get(&state), parser_b.goto_table.get(map.get(&state).unwrap())) {
                (Some(a), Some(b)) => (a, b),
                (None, None) => continue,
                _ => return false,
            };
            for (symbol, goto_a) in a {
                let goto_b = if let Some(goto) = b.get(symbol) { goto } else { return false; };
                if !map.contains_key(goto_a) {
                    map.insert(*goto_a, *goto_b);
                    q.push_back(*goto_a);
                }
                if map.get(goto_a) != Some(goto_b) { return false; }
            }
        }
        q.push_back(parser_a.start);
        let mut set = HashSet::new();
        while let Some(state) = q.pop_front() {
            if set.contains(&state) { continue; }
            set.insert(state);
            let a = parser_a.action_table.get(&state).unwrap();
            let b = parser_b.action_table.get(map.get(&state).unwrap()).unwrap();
            for (symbol, action_a) in a {
                let action_b = if let Some(action) = b.get(symbol) { action } else { return false; };
                match (action_a, action_b) {
                    (Action::Shift(shift_a), Action::Shift(shift_b)) if map.get(shift_a) == Some(shift_b) => {
                        q.push_back(*shift_a);
                    }
                    (Action::Reduce(rule_a), Action::Reduce(rule_b)) if rule_a == rule_b => {}
                    (Action::Accept, Action::Accept) => {}
                    _ => return false,
                }
            }
            let (a, b) = match (parser_a.goto_table.get(&state), parser_b.goto_table.get(map.get(&state).unwrap())) {
                (Some(a), Some(b)) => (a, b),
                (None, None) => continue,
                _ => return false,
            };
            for (symbol, goto_a) in a {
                if b.get(symbol) != Some(map.get(goto_a).unwrap()) { return false; }
                q.push_back(*goto_a);
            }
        }
        true
    }

    #[test]
    fn construct_parser() {
        #[derive(EnumIndex, Debug)]
        enum NonTerminal { E, T, F }
        #[derive(EnumIndex, Debug)]
        enum Terminal { Plus, Star, Bracket, CloseBracket, I }
        use NonTerminal::*;
        use Terminal::*;
        let syntax = Syntax::builder()
            .rule(/* 0:E->E+T */Rule::builder(E).non_terminal(E).terminal(Plus).non_terminal(T).build(|_| E))
            .rule(/* 1:E->T   */Rule::builder(E).non_terminal(T).build(|_| E))
            .rule(/* 2:T->T*F */Rule::builder(T).non_terminal(T).terminal(Star).non_terminal(F).build(|_| T))
            .rule(/* 3:T->F   */Rule::builder(T).non_terminal(F).build(|_| T))
            .rule(/* 4:F->(E) */Rule::builder(F).terminal(Bracket).non_terminal(E).terminal(CloseBracket).build(|_| F))
            .rule(/* 5:F->i   */Rule::builder(F).terminal(I).build(|_| F))
            /*       6:E'->E  */
            .build(E);
        let expect = LR1Parser {
            action_table: vec![
                // 0:closure([E'->.E,$])=[E'->.E,$],[E->.E+T,$+],[E->.T,$+],[T->.T*F,$+*],[T->.F,$+*],[F->.(E),$+*],[F->.i,$+*]
                //      Action: (=>s4,i=>s5
                //      Goto:   E=>1,T=>2,F=>3
                (
                    0,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(4)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(5)),
                    ].into_iter().collect()
                ),
                // 1:closure([E'->E.,$],[E->E.+T,$+])=[E'->E.,$],[E->E.+T,$+]
                //      Action: +=>s6,$=>r6
                (
                    1,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(6)),
                        (TerminalSymbol::EOI, Action::Accept),
                    ].into_iter().collect()
                ),
                // 2:closure([E->T.,$+],[T->T.*F,$+*])=[E->T.,$+],[T->T.*F,$+*]
                //      Action: *=>s7,$+=>r1
                (
                    2,
                    vec![
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Shift(7)),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[1].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                    ].into_iter().collect()
                ),
                // 3:closure([T->F.,$+*])=[T->F.,$+*]
                //      Action: $+*=>r3
                (
                    3,
                    vec![
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                    ].into_iter().collect()
                ),
                // 4:closure([F->(.E),$+*])=[F->(.E),$+*],[E->.E+T,)+],[E->.T,)+],[T->.T*F,)+*],[T->.F,)+*],[F->.(E),)+*],[F->.i,)+*]
                //      Action: (=>s12,i=>s13
                //      Goto:   E=>8,T=>9,F=>10
                (
                    4,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(12)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(13)),
                    ].into_iter().collect()
                ),
                // 5:closure([F->i.,$+*])=[F->i.,$+*]
                //      Action: $+*=>r5
                (
                    5,
                    vec![
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[5].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[5].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[5].clone())),
                    ].into_iter().collect()
                ),
                // 6:closure([E->E+.T,$+])=[E->E+.T,$+],[T->.T*F,$+*],[T->.F,$+*],[F->.(E),$+*],[F->.i,$+*]
                //      Action: (=>s4,i=>s5
                //      Goto:   T=>14,F=>3
                (
                    6,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(4)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(5)),
                    ].into_iter().collect()
                ),
                // 7:closure([T->T*.F,$+*])=[T->T*.F,$+*],[F->.(E),$+*],[F->.i,$+*]
                //      Action: (=>s4,i=>s5
                //      Goto:   F=>15
                (
                    7,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(4)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(5)),
                    ].into_iter().collect()
                ),
                // 8:closure([F->(E.),$+*],[E->E.+T,)+])=[F->(E.),$+*],[E->E.+T,)+]
                //      Action: )=>s16,+=>s11
                (
                    8,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(16)),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(11)),
                    ].into_iter().collect()
                ),
                // 9:closure([E->T.,)+],[T->T.*F,)+*])=[E->T.,)+],[T->T.*F,)+*]
                //      Action: *=>s17,)+=>r1
                (
                    9,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Shift(17)),
                    ].into_iter().collect()
                ),
                //10:closure([T->F.,)+*])=[T->F.,)+*]
                //      Action: )+*=>r3
                (
                    10,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                    ].into_iter().collect()
                ),
                //11:closure([E->E+.T,)+])=[E->E+.T,)+],[T->.T*F,)+*],[T->.F,)+*],[F->.(E),)+*],[F->.i,)+*]
                //      Action: (=>s12,i=>s13
                //      Goto:   T=>18,F=>10
                (
                    11,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(12)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(13)),
                    ].into_iter().collect()
                ),
                //12:closure([F->(.E),)+*])=[F->(.E),)+*],[E->.E+T,)+],[E->.T,)+],[T->.T*F,)+*],[T->.F,)+*],[F->.(E),)+*],[F->.i,)+*]
                //      Action: (=>s12,i=>s13
                //      Goto:   E=>19,T=>9,F=>10
                (
                    12,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(12)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(13)),
                    ].into_iter().collect()
                ),
                //13:closure([F->i.,)+*])=[F->i.,)+*]
                //      Action: )+*=>r5
                (
                    13,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[5].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[5].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[5].clone())),
                    ].into_iter().collect()
                ),
                //14:closure([E->E+T.,$+],[T->T.*F,$+*])=[E->E+T.,$+],[T->T.*F,$+*]
                //      Action: *=>s7,$+=>r0
                (
                    14,
                    vec![
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Shift(7)),
                    ].into_iter().collect()
                ),
                //15:closure([T->T*F.,$+*])=[T->T*F.,$+*]
                //      Action: $+*=>r2
                (
                    15,
                    vec![
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                    ].into_iter().collect()
                ),
                //16:closure([F->(E).,$+*])=[F->(E).,$+*]
                //      Action: $+*=>r4
                (
                    16,
                    vec![
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                    ].into_iter().collect()
                ),
                //17:closure([T->T*.F,)+*])=[T->T*.F,)+*],[F->.(E),)+*],[F->.i,)+*]
                //      Action: (=>s12,i=>s13
                //      Goto:   F=>20
                (
                    17,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(12)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(13)),
                    ].into_iter().collect()
                ),
                //18:closure([E->E+T.,)+],[T->T.*F,)+*])=[E->E+T.,)+],[T->T.*F,)+*]
                //      Action: *=>s17,)+=>r0
                (
                    18,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Shift(17)),
                    ].into_iter().collect()
                ),
                //19:closure([F->(E.),)+*],[E->E.+T,)+])=[F->(E.),)+*],[E->E.+T,)+]
                //      Action: )=>s21,+=>s11
                (
                    19,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(21)),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(11)),
                    ].into_iter().collect()
                ),
                //20:closure([T->T*F.,)+*])=[T->T*F.,)+*]
                //      Action: )+*=>r2
                (
                    20,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                    ].into_iter().collect()
                ),
                //21:closure([F->(E).,)+*])=[F->(E).,)+*]
                //      Action: )+*=>r4
                (
                    21,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::Symbol(Star.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                    ].into_iter().collect()
                ),
            ].into_iter().collect(),
            goto_table: vec![
                (
                    0,
                    vec![
                        (E.enum_index(), 1),
                        (T.enum_index(), 2),
                        (F.enum_index(), 3),
                    ].into_iter().collect()
                ),
                (
                    4,
                    vec![
                        (E.enum_index(), 8),
                        (T.enum_index(), 9),
                        (F.enum_index(), 10),
                    ].into_iter().collect()
                ),
                (
                    6,
                    vec![
                        (T.enum_index(), 14),
                        (F.enum_index(), 3),
                    ].into_iter().collect()
                ),
                (
                    7,
                    vec![
                        (F.enum_index(), 15),
                    ].into_iter().collect()
                ),
                (
                    11,
                    vec![
                        (T.enum_index(), 18),
                        (F.enum_index(), 10),
                    ].into_iter().collect()
                ),
                (
                    12,
                    vec![
                        (E.enum_index(), 19),
                        (T.enum_index(), 9),
                        (F.enum_index(), 10),
                    ].into_iter().collect()
                ),
                (
                    17,
                    vec![
                        (F.enum_index(), 20),
                    ].into_iter().collect()
                ),
            ].into_iter().collect(),
            error_rules: HashMap::new(),
            start: 0,
        };
        let (parser, _warning) = LR1Parser::new(syntax);
        assert!(parser_isomorphisms(&parser, &expect));

        let syntax = Syntax::builder()
            .rule(/* 0:E->E+T     */Rule::builder(E).non_terminal(E).terminal(Plus).non_terminal(T).build(|_| E))
            .rule(/* 1:E->T       */Rule::builder(E).non_terminal(T).build(|_| E))
            .rule(/* 2:T->i       */Rule::builder(T).terminal(I).build(|_| T))
            .rule(/* 3:T->(E)     */Rule::builder(T).terminal(Bracket).non_terminal(E).terminal(CloseBracket).build(|_| T))
            .rule(/* 4:T->(error) */Rule::builder(T).terminal(Bracket).error().terminal(CloseBracket).build(|_| T))
            /*       5:E'->E      */
            .build(E);
        let expect = LR1Parser {
            action_table: vec![
                // 0:closure([E'->.E,$])=[E'->.E,$],[E->.E+T,$+],[E->.T,$+],[T->.i,$+],[T->.(E),$+],[T->.(error),$+]
                //      Action: (=>s1,i=>s2
                //      Goto:   E=>3,T=>4
                (
                    0,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(1)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(2)),
                    ].into_iter().collect()
                ),
                // 1:closure([T->(.E),$+],[T->(.error),$+])=[T->(.E),$+],[T->(.error),$+],[E->.E+T,)+],[E->.T,)+],[T->.i,)+],[T->.(E),)+],[T->.(error),)+]
                //      Action: (=>s5,i=>s6,error=>s7
                //      Goto:   E=>8,T=>9
                (
                    1,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(5)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(6)),
                        (TerminalSymbol::Error, Action::Shift(7)),
                    ].into_iter().collect()
                ),
                // 2:closure([T->i.,$+])=[T->i.,$+]
                //      Action: $+=>r2
                (
                    2,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[2].clone())),
                    ].into_iter().collect()
                ),
                // 3:closure([E'->E.,$],[E->E.+T,$+])=[E'->E.,$],[E->E.+T,$+]
                //      Action: $=>accept,+=>s10
                (
                    3,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(10)),
                        (TerminalSymbol::EOI, Action::Accept),
                    ].into_iter().collect()
                ),
                // 4:closure([E->T.,$+])=[E->T.,$+]
                //      Action: $+=>r1
                (
                    4,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[1].clone())),
                    ].into_iter().collect()
                ),
                // 5:closure([T->(.E),)+],[T->(.error),)+])=[T->(.E),)+],[T->(.error),)+],[E->.E+T,)+],[E->.T,)+],[T->.i,)+],[T->.(E),)+],[T->.(error),)+]
                //      Action: (=>s5,i=>s6,error=>s11
                //      Goto:   E=>12,T=>9
                (
                    5,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(5)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(6)),
                        (TerminalSymbol::Error, Action::Shift(11)),
                    ].into_iter().collect()
                ),
                // 6:closure([T->i.,)+])=[T->i.,)+]
                //      Action: )+=>r2
                (
                    6,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[2].clone())),
                    ].into_iter().collect()
                ),
                // 7:closure([T->(error.),$+])=[T->(error.),$+]
                //      Action: )=>s13
                (
                    7,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(13)),
                    ].into_iter().collect()
                ),
                // 8:closure([T->(E.),$+],[E->E.+T,)+])=[T->(E.),$+],[E->E.+T,)+]
                //      Action: )=>s14,+=>s15
                (
                    8,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(14)),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(15)),
                    ].into_iter().collect()
                ),
                // 9:closure([E->T.,)+])=[E->T.,)+]
                //      Action: )+=>r1
                (
                    9,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[1].clone())),
                    ].into_iter().collect()
                ),
                //10:closure([E->E+.T,$+])=[E->E+.T,$+],[T->.i,$+],[T->.(E),$+],[T->.(error),$+]
                //      Action: (=>s1,i=>s2
                //      Goto:   T=>16
                (
                    10,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(1)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(2)),
                    ].into_iter().collect()
                ),
                //11:closure([T->(error.),)+])=[T->(error.),)+]
                //      Action: )=>s17
                (
                    11,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(17)),
                    ].into_iter().collect()
                ),
                //12:closure([T->(E.),)+],[E->E.+T,)+])=[T->(E.),)+],[E->E.+T,)+]
                //      Action: )=>s18,+=>s15
                (
                    12,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Shift(18)),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Shift(15)),
                    ].into_iter().collect()
                ),
                //13:closure([T->(error).,$+])=[T->(error).,$+]
                //      Action: $+=>r4
                (
                    13,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[4].clone())),
                    ].into_iter().collect()
                ),
                //14:closure([T->(E).,$+])=[T->(E).,$+]
                //      Action: $+=>r3
                (
                    14,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[3].clone())),
                    ].into_iter().collect()
                ),
                //15:closure([E->E+.T,)+])=[E->E+.T,)+],[T->.i,)+],[T->.(E),)+],[T->.(error),)+]
                //      Action: (=>s5,i=>s6
                //      Goto:   T=>19
                (
                    15,
                    vec![
                        (TerminalSymbol::Symbol(Bracket.enum_index()), Action::Shift(5)),
                        (TerminalSymbol::Symbol(I.enum_index()), Action::Shift(6)),
                    ].into_iter().collect()
                ),
                //16:closure([E->E+T.,$+])=[E->E+T.,$+]
                //      Action: $+=>r0
                (
                    16,
                    vec![
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::EOI, Action::Reduce(syntax.rules[0].clone())),
                    ].into_iter().collect()
                ),
                //17:closure([T->(error).,)+])=[T->(error).,)+]
                //      Action: )+=>r4
                (
                    17,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[4].clone())),
                    ].into_iter().collect()
                ),
                //18:closure([T->(E).,)+])=[T->(E).,)+]
                //      Action: )+=>r3
                (
                    18,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[3].clone())),
                    ].into_iter().collect()
                ),
                //19:closure([E->E+T.,)+])=[E->E+T.,)+]
                //      Action: )+=>r0
                (
                    19,
                    vec![
                        (TerminalSymbol::Symbol(CloseBracket.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                        (TerminalSymbol::Symbol(Plus.enum_index()), Action::Reduce(syntax.rules[0].clone())),
                    ].into_iter().collect()
                ),
            ].into_iter().collect(),
            goto_table: vec![
                (
                    0,
                    vec![
                        (E.enum_index(), 3),
                        (T.enum_index(), 4),
                    ].into_iter().collect()
                ),
                (
                    1,
                    vec![
                        (E.enum_index(), 8),
                        (T.enum_index(), 9),
                    ].into_iter().collect()
                ),
                (
                    5,
                    vec![
                        (E.enum_index(), 12),
                        (T.enum_index(), 9),
                    ].into_iter().collect()
                ),
                (
                    10,
                    vec![
                        (T.enum_index(), 16),
                    ].into_iter().collect()
                ),
                (
                    15,
                    vec![
                        (T.enum_index(), 19),
                    ].into_iter().collect()
                ),
            ].into_iter().collect(),
            error_rules: vec![
                (
                    1,
                    vec![
                        syntax.rules[4].clone()
                    ].into_iter().collect()
                ),
                (
                    5,
                    vec![
                        syntax.rules[4].clone()
                    ].into_iter().collect()
                )
            ].into_iter().collect(),
            start: 0,
        };
        let (parser, _warning) = LR1Parser::new(syntax);
        assert!(parser_isomorphisms(&parser, &expect));
    }
}
