use chasa::prelude::*;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::scan::trivia::scan_trivia;
use crate::scan::{
    scan_dot_field, scan_ident_or_keyword, scan_number, scan_punct_pat, scan_sigil_ident,
    scan_symbol, scan_unknown,
};
use crate::sink::EventSink;
use crate::string::scan::scan_string_start;

#[derive(Debug, Clone)]
pub enum PatNudTag {
    Atom,
    PolyVariantStart,
    StringStart,
    Rule,
    OpenParen,
    OpenBracket,
    OpenBrace,
    Stop,
}

#[derive(Debug, Clone)]
pub enum PatLedTag {
    DotField,
    PathSep,
    KwAs,
    Colon,
    Pipe,
    CallStart,
    MlNud(PatNudTag),
    Stop,
    Invalid,
}

pub fn scan_pat_nud<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<PatNudTag>> {
    if let Some(lex) = i.maybe_fn(|i| scan_string_start(leading_info, i))? {
        return Some(lex.tag(PatNudTag::StringStart));
    }

    let stop = i.env.stop.clone();
    let (tag, (kind, text)) = i.choice((
        (value(PatNudTag::Atom), scan_number),
        (value(PatNudTag::Atom), scan_sigil_ident),
        scan_ident_or_keyword.map(|(kind, text)| {
            let tag = match kind {
                SyntaxKind::Rule => PatNudTag::Rule,
                kind if !stop.contains(&kind) && matches!(kind, SyntaxKind::Ident) => {
                    PatNudTag::Atom
                }
                _ => PatNudTag::Stop,
            };
            (tag, (kind, text))
        }),
        from_fn(|i| scan_symbol(leading_info, true, i))
            .map(|(kind, text)| (PatNudTag::Atom, (kind, text))),
        scan_punct_pat.map(|(kind, text)| {
            let tag = read_pat_nud_punct(kind, &stop);
            (tag, (kind, text))
        }),
        (value(PatNudTag::Stop), scan_unknown),
    ))?;

    let trailing_trivia = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
}

pub fn scan_pat_led<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<PatLedTag>> {
    let stop = i.env.stop.clone();
    let stop_for_ident = stop.clone();
    let stop_for_punct = stop.clone();
    let (tag, (kind, text)) = i.choice((
        (value(PatLedTag::DotField), scan_dot_field),
        scan_ident_or_keyword.map(move |(kind, text)| match kind {
            SyntaxKind::As => (PatLedTag::KwAs, (kind, text)),
            kind if stop_for_ident.contains(&kind) => (PatLedTag::Stop, (kind, text)),
            kind if matches!(kind, SyntaxKind::Ident) => {
                (PatLedTag::MlNud(PatNudTag::Atom), (kind, text))
            }
            _ => (PatLedTag::Stop, (kind, text)),
        }),
        from_fn(|i| scan_symbol(leading_info, false, i))
            .map(|(kind, text)| (PatLedTag::MlNud(PatNudTag::Atom), (kind, text))),
        scan_sigil_ident.map(|(kind, text)| (PatLedTag::MlNud(PatNudTag::Atom), (kind, text))),
        scan_number.map(|(kind, text)| (PatLedTag::MlNud(PatNudTag::Atom), (kind, text))),
        scan_punct_pat.map(move |(kind, text)| {
            let tag = read_pat_led_punct(kind, leading_info, &stop_for_punct);
            (tag, (kind, text))
        }),
        (value(PatLedTag::Stop), scan_unknown),
    ))?;

    let trailing_trivia = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
}

fn read_pat_nud_punct(kind: SyntaxKind, stop: &im::HashSet<SyntaxKind>) -> PatNudTag {
    match kind {
        kind if stop.contains(&kind) => PatNudTag::Stop,
        SyntaxKind::Colon => PatNudTag::PolyVariantStart,
        SyntaxKind::ParenL => PatNudTag::OpenParen,
        SyntaxKind::BracketL => PatNudTag::OpenBracket,
        SyntaxKind::BraceL => PatNudTag::OpenBrace,
        SyntaxKind::StringStart => PatNudTag::StringStart,
        _ => PatNudTag::Stop,
    }
}

fn read_pat_led_punct(
    kind: SyntaxKind,
    leading_info: TriviaInfo,
    stop: &im::HashSet<SyntaxKind>,
) -> PatLedTag {
    match kind {
        kind if stop.contains(&kind) => PatLedTag::Stop,
        SyntaxKind::ColonColon => PatLedTag::PathSep,
        SyntaxKind::Colon => PatLedTag::Colon,
        SyntaxKind::Pipe => PatLedTag::Pipe,
        SyntaxKind::ParenL if matches!(leading_info, TriviaInfo::None) => PatLedTag::CallStart,
        other => match read_pat_nud_punct(other, stop) {
            PatNudTag::Stop => PatLedTag::Invalid,
            tag => PatLedTag::MlNud(tag),
        },
    }
}
