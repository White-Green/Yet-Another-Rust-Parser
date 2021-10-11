use proc_macro::TokenStream;
use std::ops::Range;
use syn::{Token, token, Type, LitStr, parenthesized, parse_macro_input, ExprClosure};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use tokenizer::{CharRange, DFATokenizer};
use quote::quote;

mod kw {
    syn::custom_keyword!(character);
    syn::custom_keyword!(token);
}

struct TokenizerRule {
    rule: LitStr,
    _sep: Token![:],
    paren: token::Paren,
    generator: syn::ExprClosure,
}

impl Parse for TokenizerRule {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let closure;
        Ok(TokenizerRule {
            rule: input.parse()?,
            _sep: input.parse()?,
            paren: parenthesized!(closure in input),
            generator: closure.parse()?,
        })
    }
}

struct TokenizerGeneratorInput {
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
        Ok(TokenizerGeneratorInput {
            _character: input.parse()?,
            character_type: input.parse()?,
            _sep0: input.parse()?,
            _token: input.parse()?,
            token_type: input.parse()?,
            _sep1: input.parse()?,
            rules: input.parse_terminated(TokenizerRule::parse)?,
        })
    }
}

#[proc_macro]
pub fn tokenizer(input: TokenStream) -> TokenStream {
    let TokenizerGeneratorInput { character_type, token_type, rules, .. } = parse_macro_input!(input as TokenizerGeneratorInput);
    let (rules, enum_maker): (Vec<LitStr>, Vec<ExprClosure>) = rules.into_iter().map(|TokenizerRule { rule, generator, .. }| (rule, generator)).unzip();
    let mut builder = DFATokenizer::<(), char>::builder();
    for rule in &rules {
        builder = builder.pattern(&rule.value(), |_, _| unreachable!());
    }
    let (DFATokenizer { goto, begin, end, .. }, warnings) = builder.build().expect("failed to build tokenizer");
    if !warnings.is_empty() {
        eprintln!("warnings in construct tokenizer {:?}", warnings);
    }
    let goto_constructor = {
        let goto_length = goto.len();
        let inner = goto.into_iter().map(|map| {
            let (key, value): (Vec<_>, Vec<_>) = map.into_iter().unzip();
            let (start, end): (Vec<_>, Vec<_>) = key.into_iter().map(|CharRange { range: Range { start, end } }| (start, end)).unzip();

            quote! {
                {
                    let mut map = std::collections::BTreeMap::<tokenizer::CharRange, usize>::new();
                    #(map.insert(tokenizer::CharRange { range: #start..#end }, #value);)*
                    map
                }
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
            {
                let mut map = std::collections::HashMap::<usize, usize>::new();
                #(map.insert(#key, #value);)*
                map
            }
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
        pub fn get_tokenizer() -> tokenizer::DFATokenizer<#token_type, #character_type> {
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
