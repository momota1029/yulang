use chasa::prelude::*;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::scan::trivia::scan_trivia;
use crate::scan::{
    scan_ident_or_keyword, scan_number, scan_punct_typ, scan_sigil_ident, scan_unknown,
};
use crate::sink::EventSink;

#[derive(Debug, Clone)]
pub enum TypNudTag {
    Atom,
    Forall,
    OpenParen,
    OpenBracket,
    OpenBrace,
    PolyVariantStart,
    EffectRowStart,
    Stop,
}

#[derive(Debug, Clone)]
pub enum TypLedTag {
    Arrow,
    PathSep,
    CallStart,
    BracketStart,
    MlNud(TypNudTag),
    Stop,
}

pub fn scan_typ_nud<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<TypNudTag>> {
    let stop = i.env.stop.clone();
    let stop_for_ident = stop.clone();
    let stop_for_punct = stop.clone();
    let (tag, (kind, text)) = i.choice((
        (value(TypNudTag::Atom), scan_sigil_ident),
        (value(TypNudTag::Atom), scan_number),
        scan_ident_or_keyword.map(move |(kind, text)| {
            let tag = if kind == SyntaxKind::For {
                TypNudTag::Forall
            } else if stop_for_ident.contains(&kind) {
                TypNudTag::Stop
            } else {
                TypNudTag::Atom
            };
            (tag, (kind, text))
        }),
        scan_punct_typ.map(move |(kind, text)| {
            let tag = read_typ_nud_punct(kind, &stop_for_punct);
            (tag, (kind, text))
        }),
        (value(TypNudTag::Stop), scan_unknown),
    ))?;
    let trailing_trivia = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
}

pub fn scan_typ_led<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<TypLedTag>> {
    let stop = i.env.stop.clone();
    let stop_for_ident = stop.clone();
    let stop_for_punct = stop.clone();
    let (tag, (kind, text)) = i.choice((
        (value(TypLedTag::MlNud(TypNudTag::Atom)), scan_sigil_ident),
        (value(TypLedTag::MlNud(TypNudTag::Atom)), scan_number),
        scan_punct_typ.map(move |(kind, text)| {
            let tag = read_typ_led_punct(kind, leading_info, &stop_for_punct);
            (tag, (kind, text))
        }),
        scan_ident_or_keyword.map(move |(kind, text)| {
            let tag = if stop_for_ident.contains(&kind) {
                TypLedTag::Stop
            } else {
                TypLedTag::MlNud(TypNudTag::Atom)
            };
            (tag, (kind, text))
        }),
        (value(TypLedTag::Stop), scan_unknown),
    ))?;
    let trailing_trivia = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
}

fn read_typ_nud_punct(kind: SyntaxKind, stop: &im::HashSet<SyntaxKind>) -> TypNudTag {
    match kind {
        kind if stop.contains(&kind) => TypNudTag::Stop,
        SyntaxKind::Colon => TypNudTag::PolyVariantStart,
        SyntaxKind::ParenL => TypNudTag::OpenParen,
        SyntaxKind::BracketL => TypNudTag::OpenBracket,
        SyntaxKind::BraceL => TypNudTag::OpenBrace,
        SyntaxKind::Apostrophe => TypNudTag::EffectRowStart,
        _ => TypNudTag::Stop,
    }
}

fn read_typ_led_punct(
    kind: SyntaxKind,
    leading_info: TriviaInfo,
    stop: &im::HashSet<SyntaxKind>,
) -> TypLedTag {
    match kind {
        kind if stop.contains(&kind) => TypLedTag::Stop,
        SyntaxKind::Arrow => TypLedTag::Arrow,
        SyntaxKind::ColonColon => TypLedTag::PathSep,
        SyntaxKind::ParenL if matches!(leading_info, TriviaInfo::None) => TypLedTag::CallStart,
        SyntaxKind::BracketL => TypLedTag::BracketStart,
        other => match read_typ_nud_punct(other, stop) {
            TypNudTag::Stop => TypLedTag::Stop,
            tag => TypLedTag::MlNud(tag),
        },
    }
}
