use chasa::prelude::*;
use im::HashSet;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::EventInput;
use crate::context::In;
use crate::lex::SyntaxKind;
use crate::sink::EventSink;

pub mod trivia;

pub fn scan_ident_or_keyword<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = keyword_kind(text.as_ref()).unwrap_or(SyntaxKind::Ident);
    Some((kind, text.as_ref().into()))
}

pub fn scan_name<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    Some((SyntaxKind::Ident, text.as_ref().into()))
}

pub fn scan_stmt_head_word<I: EventInput, S: EventSink>(
    i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    scan_ident_or_keyword(i)
}

pub fn scan_visibility_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = visibility_word_kind(text.as_ref());
    Some((kind, text.as_ref().into()))
}

pub fn scan_expr_nud_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, is_expr_nud_keyword);
    Some((kind, text.as_ref().into()))
}

pub fn scan_expr_led_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, is_expr_led_keyword);
    Some((kind, text.as_ref().into()))
}

pub fn scan_pat_nud_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, is_pat_nud_keyword);
    Some((kind, text.as_ref().into()))
}

pub fn scan_pat_led_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, is_pat_led_keyword);
    Some((kind, text.as_ref().into()))
}

pub fn scan_typ_nud_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, is_typ_nud_keyword);
    Some((kind, text.as_ref().into()))
}

pub fn scan_typ_led_word<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: &HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    let ((), text) = i.run(ident.with_seq())?;
    let kind = contextual_word_kind(text.as_ref(), stop, |_| false);
    Some((kind, text.as_ref().into()))
}

pub fn scan_sigil_ident<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let (_, text) = i.run((one_of("$&_'"), ident).with_seq())?;
    Some((SyntaxKind::SigilIdent, text.as_ref().into()))
}

pub fn scan_number<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<(SyntaxKind, Box<str>)> {
    let parser = choice((number_dot_start, number_with_leading));
    let ((), text) = i.run(parser.with_seq())?;
    Some((SyntaxKind::Number, text.as_ref().into()))
}

pub fn scan_dot_field<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let (_, text) = i.run((item('.'), ident).with_seq())?;
    Some((SyntaxKind::DotField, text.as_ref().into()))
}

pub fn scan_symbol<I: EventInput, S: EventSink>(
    leading_info: crate::lex::TriviaInfo,
    allow_start: bool,
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    if !allow_start && matches!(leading_info, crate::lex::TriviaInfo::None) {
        return None;
    }
    let (_, text) = i.run((item(':'), ident).with_seq())?;
    Some((SyntaxKind::Symbol, text.as_ref().into()))
}

pub fn scan_punct_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let parser = choice((
        tag("...").to(SyntaxKind::YadaYada),
        tag("->").to(SyntaxKind::Arrow),
        tag("::").to(SyntaxKind::ColonColon),
        item('(').to(SyntaxKind::ParenL),
        item(')').to(SyntaxKind::ParenR),
        item('[').to(SyntaxKind::BracketL),
        item(']').to(SyntaxKind::BracketR),
        item('{').to(SyntaxKind::BraceL),
        item('}').to(SyntaxKind::BraceR),
        item('\\').to(SyntaxKind::Backslash),
        item('\'').to(SyntaxKind::Apostrophe),
        item(',').to(SyntaxKind::Comma),
        item(':').to(SyntaxKind::Colon),
        item('=').to(SyntaxKind::Equal),
        item(';').to(SyntaxKind::Semicolon),
        item('|').to(SyntaxKind::Pipe),
    ));
    let (kind, text) = i.run(parser.with_seq())?;
    Some((kind, text.as_ref().into()))
}

pub fn scan_doc_comment_token<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let (_, text) = i.with_seq(choice((tag("---"), tag("--"))))?;
    Some((SyntaxKind::DocComment, text.as_ref().into()))
}

pub fn scan_punct_pat<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let parser = choice((
        tag("->").to(SyntaxKind::Arrow),
        tag("::").to(SyntaxKind::ColonColon),
        tag("..").to(SyntaxKind::DotDot),
        item('(').to(SyntaxKind::ParenL),
        item(')').to(SyntaxKind::ParenR),
        item('[').to(SyntaxKind::BracketL),
        item(']').to(SyntaxKind::BracketR),
        item('{').to(SyntaxKind::BraceL),
        item('}').to(SyntaxKind::BraceR),
        item(',').to(SyntaxKind::Comma),
        item(':').to(SyntaxKind::Colon),
        item('=').to(SyntaxKind::Equal),
        item(';').to(SyntaxKind::Semicolon),
        item('|').to(SyntaxKind::Pipe),
    ));
    let (kind, text) = i.run(parser.with_seq())?;
    Some((kind, text.as_ref().into()))
}

pub fn scan_punct_typ<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let parser = choice((
        tag("->").to(SyntaxKind::Arrow),
        tag("::").to(SyntaxKind::ColonColon),
        item('(').to(SyntaxKind::ParenL),
        item(')').to(SyntaxKind::ParenR),
        item('[').to(SyntaxKind::BracketL),
        item(']').to(SyntaxKind::BracketR),
        item('{').to(SyntaxKind::BraceL),
        item('}').to(SyntaxKind::BraceR),
        item(',').to(SyntaxKind::Comma),
        item(':').to(SyntaxKind::Colon),
        item('=').to(SyntaxKind::Equal),
        item(';').to(SyntaxKind::Semicolon),
        item('|').to(SyntaxKind::Pipe),
        item('\'').to(SyntaxKind::Apostrophe),
    ));
    let (kind, text) = i.run(parser.with_seq())?;
    Some((kind, text.as_ref().into()))
}

pub fn scan_unknown<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    let (_, text) = i.run(one_of(|_: char| true).with_seq())?;
    Some((SyntaxKind::Unknown, text.as_ref().into()))
}

fn number_with_leading<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.run((digits1, frac.or_not(), exp.or_not()).skip())
}

fn number_dot_start<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.run((item('.'), digits1, exp.or_not()).skip())
}

fn digits1<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.many1_skip(ascii_digit)
}

fn frac<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.run((item('.'), digits1).skip())
}

fn exp<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.run((one_of("eE"), one_of("+-").or_not(), digits1).skip())
}

pub fn ident<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.choice((one_of(is_xid_start).skip(), item('_').skip()))?;
    i.many_skip(one_of(is_xid_continue))?;
    i.skip(one_of("?!").or_not())
}

fn keyword_kind(text: &str) -> Option<SyntaxKind> {
    match text {
        "do" => Some(SyntaxKind::Do),
        "if" => Some(SyntaxKind::If),
        "else" => Some(SyntaxKind::Else),
        "elsif" => Some(SyntaxKind::Elsif),
        "case" => Some(SyntaxKind::Case),
        "catch" => Some(SyntaxKind::Catch),
        "my" => Some(SyntaxKind::My),
        "our" => Some(SyntaxKind::Our),
        "pub" => Some(SyntaxKind::Pub),
        "use" => Some(SyntaxKind::Use),
        "type" => Some(SyntaxKind::Type),
        "struct" => Some(SyntaxKind::Struct),
        "enum" => Some(SyntaxKind::Enum),
        "error" => Some(SyntaxKind::Error),
        "role" => Some(SyntaxKind::Role),
        "impl" => Some(SyntaxKind::Impl),
        "cast" => Some(SyntaxKind::Cast),
        "act" => Some(SyntaxKind::Act),
        "mod" => Some(SyntaxKind::Mod),
        "as" => Some(SyntaxKind::As),
        "for" => Some(SyntaxKind::For),
        "in" => Some(SyntaxKind::In),
        "with" => Some(SyntaxKind::With),
        "where" => Some(SyntaxKind::Where),
        "via" => Some(SyntaxKind::Via),
        "rule" => Some(SyntaxKind::Rule),
        "prefix" => Some(SyntaxKind::Prefix),
        "infix" => Some(SyntaxKind::Infix),
        "suffix" => Some(SyntaxKind::Suffix),
        "nullfix" => Some(SyntaxKind::Nullfix),
        "lazy" => Some(SyntaxKind::Lazy),
        _ => None,
    }
}

fn contextual_word_kind(
    text: &str,
    stop: &HashSet<SyntaxKind>,
    is_syntax_keyword: impl Fn(SyntaxKind) -> bool,
) -> SyntaxKind {
    let Some(kind) = keyword_kind(text) else {
        return SyntaxKind::Ident;
    };
    if stop.contains(&kind) || is_syntax_keyword(kind) {
        kind
    } else {
        SyntaxKind::Ident
    }
}

fn visibility_word_kind(text: &str) -> SyntaxKind {
    match text {
        "use" => SyntaxKind::Use,
        "mod" => SyntaxKind::Mod,
        "type" => SyntaxKind::Type,
        "struct" => SyntaxKind::Struct,
        "enum" => SyntaxKind::Enum,
        "error" => SyntaxKind::Error,
        "role" => SyntaxKind::Role,
        "impl" => SyntaxKind::Impl,
        "cast" => SyntaxKind::Cast,
        "act" => SyntaxKind::Act,
        "prefix" => SyntaxKind::Prefix,
        "infix" => SyntaxKind::Infix,
        "suffix" => SyntaxKind::Suffix,
        "nullfix" => SyntaxKind::Nullfix,
        "lazy" => SyntaxKind::Lazy,
        _ => SyntaxKind::Ident,
    }
}

fn is_expr_nud_keyword(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Do
            | SyntaxKind::If
            | SyntaxKind::Else
            | SyntaxKind::Elsif
            | SyntaxKind::Case
            | SyntaxKind::Catch
            | SyntaxKind::Rule
    )
}

fn is_expr_led_keyword(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Do | SyntaxKind::Else | SyntaxKind::Elsif | SyntaxKind::As | SyntaxKind::With
    )
}

fn is_pat_nud_keyword(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::Rule)
}

fn is_pat_led_keyword(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::As)
}

fn is_typ_nud_keyword(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::For)
}
