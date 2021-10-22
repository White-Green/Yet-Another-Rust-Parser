use proc_macro::TokenStream;
use std::collections::HashMap;
use std::time::Instant;

use proc_macro2::{Delimiter, Group};
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{braced, bracketed, parenthesized, parse_macro_input, token, Expr, ExprTuple, FieldValue, Ident, LitStr, Pat, Path, Token, Type, Visibility};

use parser::enum_index::EnumIndex;
use parser::{Action, LR1Parser, Rule, Symbol, Syntax, TerminalSymbol};

mod kw {
    syn::custom_keyword!(token);
    syn::custom_keyword!(symbol);
    syn::custom_keyword!(errortype);
    syn::custom_keyword!(start);
    syn::custom_keyword!(ERROR);
    syn::custom_keyword!(LR1Parser);
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum TokenKey {
    Named(String),
    Raw(String),
}

impl Parse for TokenKey {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(LitStr) {
            let s: LitStr = input.parse()?;
            Ok(TokenKey::Raw(s.value()))
        } else {
            let s: Ident = input.parse()?;
            Ok(TokenKey::Named(s.to_string()))
        }
    }
}

struct TokenItem {
    key: TokenKey,
    _eq: Token![=],
    value: Expr,
}

impl Parse for TokenItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(TokenItem { key: input.parse()?, _eq: input.parse()?, value: input.parse()? })
    }
}

struct TokenList {
    _token: kw::token,
    name: Path,
    _brace: token::Brace,
    items: Punctuated<TokenItem, Token![,]>,
}

impl Parse for TokenList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let items;
        Ok(TokenList {
            _token: input.parse()?,
            name: input.parse()?,
            _brace: braced!(items in input),
            items: items.parse_terminated(TokenItem::parse)?,
        })
    }
}

struct SymbolItem {
    key: String,
    _eq: Token![=],
    value: Expr,
}

impl Parse for SymbolItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let key: Ident = input.parse()?;
        Ok(SymbolItem { key: key.to_string(), _eq: input.parse()?, value: input.parse()? })
    }
}

struct SymbolList {
    _symbol: kw::symbol,
    name: Path,
    _brace: token::Brace,
    items: Punctuated<SymbolItem, Token![,]>,
}

impl Parse for SymbolList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let items;
        Ok(SymbolList {
            _symbol: input.parse()?,
            name: input.parse()?,
            _brace: braced!(items in input),
            items: items.parse_terminated(SymbolItem::parse)?,
        })
    }
}

enum EnumValue {
    Named { _brace: token::Brace, values: Punctuated<FieldValue, Token![,]> },
    Unnamed(ExprTuple),
    None,
}

impl Parse for EnumValue {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(token::Brace) {
            let content;
            Ok(EnumValue::Named {
                _brace: braced!(content in input),
                values: content.parse_terminated(FieldValue::parse)?,
            })
        } else if input.peek(token::Paren) {
            Ok(EnumValue::Unnamed(input.parse()?))
        } else {
            Ok(EnumValue::None)
        }
    }
}

impl ToTokens for EnumValue {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            EnumValue::Named { _brace, values } => Group::new(Delimiter::Brace, values.to_token_stream()).to_tokens(tokens),
            EnumValue::Unnamed(tuple) => tuple.to_tokens(tokens),
            EnumValue::None => {}
        }
    }
}

struct EnumItem {
    name: Ident,
    value: EnumValue,
}

impl Parse for EnumItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(EnumItem { name: input.parse()?, value: input.parse()? })
    }
}

impl ToTokens for EnumItem {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.name.to_tokens(tokens);
        self.value.to_tokens(tokens);
    }
}

enum BNFTerminalSymbol {
    Named { _bracket: token::Bracket, name: Ident },
    Raw(LitStr),
}

impl Parse for BNFTerminalSymbol {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(token::Bracket) {
            let name;
            Ok(BNFTerminalSymbol::Named { _bracket: bracketed!(name in input), name: name.parse()? })
        } else {
            Ok(BNFTerminalSymbol::Raw(input.parse()?))
        }
    }
}

enum BNFSymbol {
    Terminal(BNFTerminalSymbol),
    NonTerminal { _open: Token![<], name: Ident, _close: Token![>] },
    Error(kw::ERROR),
}

impl Parse for BNFSymbol {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(Token![<]) {
            Ok(BNFSymbol::NonTerminal { _open: input.parse()?, name: input.parse()?, _close: input.parse()? })
        } else if input.peek(kw::ERROR) {
            Ok(BNFSymbol::Error(input.parse()?))
        } else {
            Ok(BNFSymbol::Terminal(input.parse()?))
        }
    }
}

struct NoneToken;

impl Parse for NoneToken {
    fn parse(_: ParseStream) -> syn::Result<Self> {
        Ok(NoneToken)
    }
}

enum BNFRuleKey {
    Named { _open: Token![<], name: Ident, _close: Token![>], _eq1: Token![::], _eq2: Token![=] },
    Follow(Token![|]),
}

impl Parse for BNFRuleKey {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(Token![<]) {
            Ok(BNFRuleKey::Named {
                _open: input.parse()?,
                name: input.parse()?,
                _close: input.parse()?,
                _eq1: input.parse()?,
                _eq2: input.parse()?,
            })
        } else {
            Ok(BNFRuleKey::Follow(input.parse()?))
        }
    }
}

struct BNFRule {
    key: BNFRuleKey,
    rule: Vec<BNFSymbol>,
    _sep: Token![:],
    pattern: Pat,
    _arrow: Token![=>],
    generator: Expr,
    _end: Token![;],
}

impl Parse for BNFRule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(BNFRule {
            key: input.parse()?,
            rule: {
                let mut vec = Vec::new();
                while !input.peek(Token![:]) {
                    vec.push(input.parse()?);
                }
                vec
            },
            _sep: input.parse()?,
            pattern: input.parse()?,
            _arrow: input.parse()?,
            generator: input.parse()?,
            _end: input.parse()?,
        })
    }
}

struct ParserGeneratorInput {
    visibility: Visibility,
    _fn: Token![fn],
    function_name: Ident,
    _paren: token::Paren,
    _arrow: Token![->],
    _marker: kw::LR1Parser,
    _brace: token::Brace,
    tokens: TokenList,
    symbols: SymbolList,
    _error: kw::errortype,
    error: Type,
    _end1: Token![;],
    _start: kw::start,
    start: Ident,
    _end2: Token![;],
    rules: Vec<BNFRule>,
}

impl Parse for ParserGeneratorInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut rules = Vec::new();
        let items;
        let ignore;
        Ok(ParserGeneratorInput {
            visibility: input.parse()?,
            _fn: input.parse()?,
            function_name: input.parse()?,
            _paren: {
                let p = parenthesized!(ignore in input);
                assert!(ignore.is_empty(), "argument count of parser function should be zero");
                p
            },
            _arrow: input.parse()?,
            _marker: input.parse()?,
            _brace: braced!(items in input),
            tokens: items.parse()?,
            symbols: items.parse()?,
            _error: items.parse()?,
            error: items.parse()?,
            _end1: items.parse()?,
            _start: items.parse()?,
            start: items.parse()?,
            _end2: items.parse()?,
            rules: loop {
                if items.is_empty() {
                    break rules;
                }
                rules.push(items.parse()?);
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
struct AnonymousSymbol(usize);

impl EnumIndex for AnonymousSymbol {
    fn enum_index(&self) -> usize {
        self.0
    }
}

#[proc_macro]
pub fn parser(input: TokenStream) -> TokenStream {
    let ParserGeneratorInput { visibility, function_name, tokens, symbols, error, start, rules, .. } = parse_macro_input!(input as ParserGeneratorInput);
    let token_type_name = tokens.name;
    let token_name_map = tokens.items.iter().enumerate().map(|(i, TokenItem { key, .. })| (key.clone(), i)).collect::<HashMap<_, _>>();
    let symbol_type_name = symbols.name;
    let symbol_name_map = symbols.items.iter().enumerate().map(|(i, SymbolItem { key, .. })| (key.clone(), i)).collect::<HashMap<_, _>>();
    let mut syntax = Syntax::<AnonymousSymbol, AnonymousSymbol>::builder();
    let mut above_rule_key = None;
    let mut keys = Vec::with_capacity(rules.len());
    for BNFRule { key, rule, .. } in &rules {
        let start = match key {
            BNFRuleKey::Named { name, .. } => {
                if let Some(start) = symbol_name_map.get(&name.to_string()) {
                    *start
                } else {
                    panic!("unknown symbol key {}", name.to_string());
                }
            }
            BNFRuleKey::Follow(_) => above_rule_key.expect("above rule is not found"),
        };
        above_rule_key = Some(start);
        keys.push(start);
        let items = rule
            .iter()
            .map(|symbol| match symbol {
                BNFSymbol::Terminal(BNFTerminalSymbol::Named { name, .. }) => Symbol::Terminal(*token_name_map.get(&TokenKey::Named(name.to_string())).unwrap_or_else(|| panic!("token named {:?} is not found", name.to_string()))),
                BNFSymbol::Terminal(BNFTerminalSymbol::Raw(name)) => Symbol::Terminal(*token_name_map.get(&TokenKey::Raw(name.value())).unwrap_or_else(|| panic!("token named {:?} is not found", name.value()))),
                BNFSymbol::NonTerminal { name, .. } => Symbol::NonTerminal(*symbol_name_map.get(&name.to_string()).unwrap_or_else(|| panic!("symbol named {:?} is not found", name.to_string()))),
                BNFSymbol::Error(_) => Symbol::Error(()),
            })
            .collect::<Vec<_>>();
        syntax = syntax.rule(Rule::new_raw(start, &items, |_| unreachable!()));
    }
    let syntax = syntax.build(AnonymousSymbol(*symbol_name_map.get(&start.to_string()).expect("symbol name is not found")));
    eprintln!("start construct parser.");
    let stopwatch = Instant::now();
    let (LR1Parser { action_table, goto_table, error_rules, start, .. }, warnings) = LR1Parser::new(syntax);
    eprintln!("construct parser finished in {}ms.", stopwatch.elapsed().as_millis());
    if !warnings.is_empty() {
        eprintln!("warnings in construct parser {:?}", warnings);
    }
    let goto_table_constructor = {
        let goto_table_constructor = goto_table.into_iter().map(|(key, value)| {
            let value_constructor = value.into_iter().map(|(key, value)| quote! { (symbols[#key], #value) });
            quote! {
                (#key, std::collections::HashMap::<usize, usize>::from([#(#value_constructor),*]))
            }
        });
        quote! {
            std::collections::HashMap::<usize, std::collections::HashMap<usize, usize>>::from([#(#goto_table_constructor),*])
        }
    };
    let action_table_constructor = {
        let action_table_constructor = action_table.into_iter().map(|(key, value)| {
            let key_value_list = value.into_iter().map(|(key, value)| {
                let key = match key {
                    TerminalSymbol::Symbol(s) => {
                        quote! { parser::TerminalSymbol::Symbol(tokens[#s]) }
                    }
                    TerminalSymbol::Error(_) => quote! { parser::TerminalSymbol::Error(()) },
                    TerminalSymbol::EOI => quote! { parser::TerminalSymbol::EOI },
                };
                let value = match value {
                    Action::Shift(s) => quote! { parser::Action::Shift(#s) },
                    Action::Reduce(r) => quote! { parser::Action::Reduce(#r) },
                    Action::Accept => quote! { parser::Action::Accept },
                };
                quote! { (#key, #value) }
            });

            quote! {
                (#key, std::collections::HashMap::<parser::TerminalSymbol<usize, ()>, parser::Action<usize, usize>>::from([#(#key_value_list),*]))
            }
        });
        quote! {
            std::collections::HashMap::<usize, std::collections::HashMap<parser::TerminalSymbol<usize, ()>, parser::Action<usize, usize>>>::from([#(#action_table_constructor),*])
        }
    };
    let error_rules_constructor = {
        let error_rules_constructor = error_rules.into_iter().map(|(key, value)| {
            let value_constructor = value.into_iter();
            quote! {
                (#key, std::collections::HashSet::<usize>::from([#(#value_constructor),*]))
            }
        });
        quote! {
            std::collections::HashMap::<usize, std::collections::HashSet<usize>>::from([#(#error_rules_constructor),*])
        }
    };
    let rules_constructor = rules.into_iter().enumerate().map(|(i, rule)| {
        let generator = {
            let pattern = rule.pattern;
            let generator = rule.generator;
            quote! {
                |list| match list {
                    #pattern => #generator,
                    _ => panic!("entered unreachable code in rule {}. please check definition of parser", #i),
                }
            }
        };

        let start = keys[i];
        let items = rule.rule.iter().map(|item| match item {
            BNFSymbol::Terminal(BNFTerminalSymbol::Named { name, .. }) => {
                let token = *token_name_map.get(&TokenKey::Named(name.to_string())).expect("");
                quote! { parser::Symbol::<usize, usize, ()>::Terminal(tokens[#token]) }
            }
            BNFSymbol::Terminal(BNFTerminalSymbol::Raw(name)) => {
                let token = *token_name_map.get(&TokenKey::Raw(name.value())).expect("");
                quote! { parser::Symbol::<usize, usize, ()>::Terminal(tokens[#token]) }
            }
            BNFSymbol::NonTerminal { name, .. } => {
                let symbol = *symbol_name_map.get(&name.to_string()).expect("");
                quote! { parser::Symbol::<usize, usize, ()>::NonTerminal(symbols[#symbol]) }
            }
            BNFSymbol::Error(_) => quote! { parser::Symbol::<usize, usize, ()>::Error(()) },
        });
        quote! { parser::Rule::<#symbol_type_name, #token_type_name, #error>::new_raw(symbols[#start], &[#(#items),*], #generator) }
    });
    let tokens = tokens.items.iter().map(|TokenItem { value, .. }| value); //.map(|token| dbg!(quote! { #token_type_name::#token }));
    let symbols = symbols.items.iter().map(|SymbolItem { value, .. }| value); //.map(|symbol|quote!{ #symbol_type_name::#symbol });
    let result = quote! {
        #visibility fn #function_name() -> parser::LR1Parser<#symbol_type_name, #token_type_name, #error>{
            let tokens = [#(parser::enum_index::EnumIndex::enum_index(&(#token_type_name::#tokens))),*];
            let symbols = [#(parser::enum_index::EnumIndex::enum_index(&(#symbol_type_name::#symbols))),*];
            let action_table: std::collections::HashMap<usize, std::collections::HashMap<parser::TerminalSymbol<usize, ()>, parser::Action<usize, usize>>> = #action_table_constructor;
            let goto_table: std::collections::HashMap<usize, std::collections::HashMap<usize, usize>> = #goto_table_constructor;
            let error_rules: std::collections::HashMap<usize, std::collections::HashSet<usize>> = #error_rules_constructor;
            let rules = parser::Syntax::<#symbol_type_name, #token_type_name, #error>::builder()
                #(.rule(#rules_constructor))*
                .build_raw(#start)
                .into_rules();
            parser::LR1Parser{
                rules,
                action_table,
                goto_table,
                error_rules,
                start: #start,
            }
        }
    };
    result.into()
}
