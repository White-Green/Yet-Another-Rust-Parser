use proc_macro::TokenStream;
use std::collections::HashMap;
use std::str::FromStr;

use proc_macro2::{Delimiter, Group};
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{
    braced, bracketed, parenthesized, parse_macro_input, token, ExprClosure, ExprTuple, FieldValue,
    Ident, Token,
};

use parser::enum_index::EnumIndex;
use parser::{Action, LR1Parser, Rule, Symbol, Syntax, TerminalSymbol};

enum EnumValue {
    Named {
        _brace: token::Brace,
        values: Punctuated<FieldValue, Token![,]>,
    },
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
            EnumValue::Named { _brace, values } => {
                Group::new(Delimiter::Brace, values.to_token_stream()).to_tokens(tokens)
            }
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
        Ok(EnumItem {
            name: input.parse()?,
            value: input.parse()?,
        })
    }
}

impl ToTokens for EnumItem {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.name.to_tokens(tokens);
        self.value.to_tokens(tokens);
    }
}

struct ItemsList {
    prefix: Ident,
    token_enum_name: Ident,
    _brace: token::Brace,
    items: Punctuated<EnumItem, Token![,]>,
}

impl Parse for ItemsList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        Ok(ItemsList {
            prefix: input.parse()?,
            token_enum_name: input.parse()?,
            _brace: braced!(content in input),
            items: content.parse_terminated(EnumItem::parse)?,
        })
    }
}

enum BNFSymbol {
    Terminal {
        _bracket: token::Bracket,
        name: Ident,
    },
    NonTerminal {
        _open: Token![<],
        name: Ident,
        _close: Token![>],
    },
}

impl Parse for BNFSymbol {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(Token![<]) {
            Ok(BNFSymbol::NonTerminal {
                _open: input.parse()?,
                name: input.parse()?,
                _close: input.parse()?,
            })
        } else {
            let content;
            Ok(BNFSymbol::Terminal {
                _bracket: bracketed!(content in input),
                name: content.parse()?,
            })
        }
    }
}

struct NoneToken;

impl Parse for NoneToken {
    fn parse(_: ParseStream) -> syn::Result<Self> {
        Ok(NoneToken)
    }
}

struct BNFRule {
    _open: Token![<],
    non_terminal: Ident,
    _close: Token![>],
    _eq1: Token![::],
    _eq2: Token![=],
    _bracket: token::Paren,
    rule: Punctuated<BNFSymbol, NoneToken>,
    _bracket2: token::Paren,
    generator: ExprClosure,
}

impl Parse for BNFRule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        let content2;
        Ok(BNFRule {
            _open: input.parse()?,
            non_terminal: input.parse()?,
            _close: input.parse()?,
            _eq1: input.parse()?,
            _eq2: input.parse()?,
            _bracket: parenthesized!(content in input),
            rule: content.parse_terminated(BNFSymbol::parse)?,
            _bracket2: parenthesized!(content2 in input),
            generator: content2.parse()?,
        })
    }
}

struct ParserGeneratorInput {
    tokens: ItemsList,
    symbols: ItemsList,
    start: Ident,
    rules: Vec<BNFRule>,
}

impl Parse for ParserGeneratorInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut rules = Vec::new();
        Ok(ParserGeneratorInput {
            tokens: input.parse()?,
            symbols: input.parse()?,
            start: input.parse()?,
            rules: loop {
                if input.is_empty() {
                    break rules;
                }
                rules.push(input.parse()?);
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
    let ParserGeneratorInput {
        tokens,
        symbols,
        start,
        rules,
    } = parse_macro_input!(input as ParserGeneratorInput);
    if tokens.prefix.to_string() != "token" {
        return TokenStream::from_str("compile_error!()").unwrap();
    }
    if symbols.prefix.to_string() != "symbol" {
        return TokenStream::from_str("compile_error!()").unwrap();
    }
    let token_type_name = tokens.token_enum_name;
    let token_name_map = tokens
        .items
        .iter()
        .enumerate()
        .map(|(i, EnumItem { name, .. })| (name.to_string(), i))
        .collect::<HashMap<_, _>>();
    let symbol_type_name = symbols.token_enum_name;
    let symbol_name_map = symbols
        .items
        .iter()
        .enumerate()
        .map(|(i, EnumItem { name, .. })| (name.to_string(), i))
        .collect::<HashMap<_, _>>();
    let mut syntax = Syntax::<AnonymousSymbol, AnonymousSymbol>::builder();
    for BNFRule {
        non_terminal, rule, ..
    } in &rules
    {
        let start = if let Some(start) = symbol_name_map.get(&non_terminal.to_string()) {
            *start
        } else {
            return TokenStream::from_str("compile_error!()").unwrap();
        };
        let items = rule
            .iter()
            .map(|symbol| match symbol {
                BNFSymbol::Terminal { name, .. } => Symbol::Terminal(
                    *token_name_map
                        .get(&name.to_string())
                        .expect("token name is not found"),
                ),
                BNFSymbol::NonTerminal { name, .. } => Symbol::NonTerminal(
                    *symbol_name_map
                        .get(&name.to_string())
                        .expect("symbol name is not found"),
                ),
            })
            .collect::<Vec<_>>();
        syntax = syntax.rule(Rule::new_raw(start, &items, |_| unreachable!()));
    }
    let syntax = syntax.build(AnonymousSymbol(
        *symbol_name_map
            .get(&start.to_string())
            .expect("symbol name is not found"),
    ));
    let (
        LR1Parser {
            action_table,
            goto_table,
            error_rules,
            start,
            ..
        },
        warnings,
    ) = LR1Parser::new(syntax);
    if !warnings.is_empty() {
        eprintln!("warnings in construct parser {:?}", warnings);
    }
    let action_table_constructor = {
        let action_table_size = action_table.len();
        let action_table_constructor = action_table.into_iter().map(|(key, value)| {
            let value_size = value.len();
            let value_constructor = value.into_iter().map(|(key, value)| {
                let key = match key {
                    TerminalSymbol::Symbol(s) => {
                        quote! { parser::TerminalSymbol::Symbol(tokens[#s]) }
                    }
                    TerminalSymbol::Error => quote! { parser::TerminalSymbol::Error },
                    TerminalSymbol::EOI => quote! { parser::TerminalSymbol::EOI },
                };
                let value = match value {
                    Action::Shift(s) => quote! { parser::Action::Shift(#s) },
                    Action::Reduce(r) => quote! { parser::Action::Reduce(#r) },
                    Action::Accept => quote! { parser::Action::Accept },
                };
                quote! { value.insert(#key, #value); }
            });

            quote! {
                let value = {
                    let mut value = std::collections::HashMap::with_capacity(#value_size);
                    #(#value_constructor)*
                    value
                };
                action_table.insert(#key, value);
            }
        });
        quote! {
            {
                let mut action_table = std::collections::HashMap::with_capacity(#action_table_size);
                #(#action_table_constructor)*
                action_table
            }
        }
    };
    let goto_table_constructor = {
        let goto_table_size = goto_table.len();
        let goto_table_constructor = goto_table.into_iter().map(|(key, value)| {
            let value_size = value.len();
            let value_constructor = value
                .into_iter()
                .map(|(key, value)| quote! {value.insert(symbols[#key], #value);});
            quote! {
                let value = {
                    let mut value = std::collections::HashMap::with_capacity(#value_size);
                    #(#value_constructor)*
                    value
                };
                goto_table.insert(#key, value);
            }
        });
        quote! {
            {
                let mut goto_table = std::collections::HashMap::with_capacity(#goto_table_size);
                #(#goto_table_constructor)*
                goto_table
            }
        }
    };
    let error_rules_constructor = {
        let error_rules_size = error_rules.len();
        let error_rules_constructor = error_rules.into_iter().map(|(key, value)| {
            let value_size = value.len();
            let value_constructor = value.into_iter().map(|v| quote! { value.insert(#v); });
            quote! {
                let value = {
                    let value = std::collections::HashSet::with_capacity(#value_size);
                    #(#value_constructor)*
                    value
                };
                error_rules.insert(#key, value);
            }
        });
        quote! {
            {
                let mut error_rules = std::collections::HashMap::with_capacity(#error_rules_size);
                #(#error_rules_constructor)*
                error_rules
            }
        }
    };
    let rules_constructor = rules.into_iter().map(|rule| {
        let generator = rule.generator;
        let start = *symbol_name_map.get(&rule.non_terminal.to_string()).expect("");
        let items = rule.rule.iter().map(|item| match item {
            BNFSymbol::Terminal { name, .. } => {
                let token = *token_name_map.get(&name.to_string()).expect("");
                quote! { parser::Symbol::Terminal(tokens[#token]) }
            }
            BNFSymbol::NonTerminal { name, .. } => {
                let symbol = *symbol_name_map.get(&name.to_string()).expect("");
                quote! { parser::Symbol::NonTerminal(symbols[#symbol]) }
            }
        });
        quote! { parser::Rule::<#symbol_type_name, #token_type_name>::new_raw(symbols[#start], &[#(#items),*], #generator) }
    });
    let tokens = tokens.items.iter(); //.map(|token| dbg!(quote! { #token_type_name::#token }));
    let symbols = symbols.items.iter(); //.map(|symbol|quote!{ #symbol_type_name::#symbol });
    let result = quote! {
        pub fn get_parser() -> parser::LR1Parser<#symbol_type_name, #token_type_name>{
            let tokens = [#(parser::enum_index::EnumIndex::enum_index(&(#token_type_name::#tokens))),*];
            let symbols = [#(parser::enum_index::EnumIndex::enum_index(&(#symbol_type_name::#symbols))),*];
            let action_table = #action_table_constructor;
            let goto_table = #goto_table_constructor;
            let error_rules = #error_rules_constructor;
            let rules = parser::Syntax::builder()
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
