use proc_macro::TokenStream;
use std::ops::Range;
use syn::{Token, braced, Ident, token, Type, LitStr, parenthesized, parse_macro_input, Visibility, Expr};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use tokenizer::{CharRange, DFATokenizer};
use quote::quote;

mod kw {
    syn::custom_keyword!(character);
    syn::custom_keyword!(token);
    syn::custom_keyword!(DFATokenizer);
}

struct TokenizerRule {
    rule: LitStr,
    _sep: Token![:],
    generator: Expr,
}

impl Parse for TokenizerRule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(TokenizerRule {
            rule: input.parse()?,
            _sep: input.parse()?,
            generator: input.parse()?,
        })
    }
}

struct TokenizerGeneratorInput {
    visibility: Visibility,
    _fn: Token![fn],
    function_name: Ident,
    _paren: token::Paren,
    _arrow: Token![->],
    _marker: kw::DFATokenizer,
    _brace: token::Brace,
    _character: kw::character,
    character_type: Type,
    _sep0: Token![;],
    _token: kw::token,
    token_type: Type,
    _sep1: Token![;],
    rules: Punctuated<TokenizerRule, Token![;]>,
}

impl Parse for TokenizerGeneratorInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ignore;
        let items;
        Ok(TokenizerGeneratorInput {
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
            _character: items.parse()?,
            character_type: items.parse()?,
            _sep0: items.parse()?,
            _token: items.parse()?,
            token_type: items.parse()?,
            _sep1: items.parse()?,
            rules: items.parse_terminated(TokenizerRule::parse)?,
        })
    }
}

#[proc_macro]
pub fn tokenizer(input: TokenStream) -> TokenStream {
    let TokenizerGeneratorInput { visibility, function_name, character_type, token_type, rules, .. } = parse_macro_input!(input as TokenizerGeneratorInput);
    let (rules, enum_maker): (Vec<LitStr>, Vec<Expr>) = rules.into_iter().map(|TokenizerRule { rule, generator, .. }| (rule, generator)).unzip();
    let mut builder = DFATokenizer::<(), char>::builder();
    for rule in &rules {
        builder = builder.pattern(&rule.value(), |_, _| unreachable!());
    }
    let (DFATokenizer { goto, begin, end, .. }, warnings) = builder.build().expect("failed to build tokenizer");
    if !warnings.is_empty() {
        eprintln!("warnings in construct tokenizer {:?}", warnings);
    }
    let goto_constructor = {
        let inner = goto.into_iter().map(|map| {
            let (key, value): (Vec<_>, Vec<_>) = map.into_iter().unzip();
            let (start, end): (Vec<_>, Vec<_>) = key.into_iter().map(|CharRange { range: Range { start, end } }| (start, end)).unzip();

            quote! {
                std::collections::BTreeMap::<tokenizer::CharRange, usize>::from([#((tokenizer::CharRange { range: #start..#end }, #value)),*])
            }
        });
        quote! {
            vec![
                #(#inner),*
            ]
        }
    };
    let end_constructor = {
        let (key, value): (Vec<_>, Vec<_>) = end.into_iter().unzip();
        quote! {
            std::collections::HashMap::<usize, usize>::from([#((#key, #value)),*])
        }
    };
    let enum_maker_constructor = quote! {
        {
            fn into_box(closure: impl Fn(&str, Vec<#character_type>) -> #token_type + 'static) -> Box<dyn Fn(&str, Vec<#character_type>) -> #token_type> {
                Box::new(closure) as Box<dyn Fn(&str, Vec<#character_type>) -> #token_type>
            }
            vec![
                #( into_box(#enum_maker) ),*
            ]
        }
    };

    let result = quote! {
        #visibility fn #function_name() -> tokenizer::DFATokenizer<#token_type, #character_type> {
            let goto = #goto_constructor;
            let end = #end_constructor;
            let enum_maker = #enum_maker_constructor;
            tokenizer::DFATokenizer {
                goto,
                begin: #begin,
                end,
                enum_maker
            }
        }
    };
    result.into()
}
