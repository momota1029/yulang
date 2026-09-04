//! Direct canonical `struct` declaration construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    driver::{
        Either, TailExit, delimited_baseline, handoff, implicit_delimited_newline,
        indentation_after_newline, is_active_stop, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        introduced_body_indentation, scan_identifier, scan_statement_item, scan_trivia,
        source_identifier, statement_item_after_trivia, type_nud_item_after_trivia,
    },
    operator::source_after_trivia,
    type_expr::{TypeApplyBoundary, required_type_expr_with_boundary, with_type_outer_close},
};

pub(super) fn struct_declaration_selected(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    if item_word(item) == Some("struct") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    observes(i, |source| prefixed_struct_candidate(source, baseline))
}

pub(super) fn struct_declaration(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    debug_assert!(struct_declaration_selected(i.rb(), &intro, baseline));
    i.state.start_node(SyntaxKind::StructDeclaration.into());
    if item_word(&intro) == Some("struct") {
        emit_intro(&mut i, intro, SyntaxKind::StructKw);
    } else {
        emit_visibility(&mut i, intro);
        let accepted = emit_gstruct(i.rb(), baseline);
        debug_assert!(accepted);
        let keyword = i
            .token(|lex| scan_exact_identifier(lex, "struct"))
            .expect("visibility-led selection proved exact `struct`");
        i.state.token(SyntaxKind::StructKw.into(), &keyword.text);
    }

    let exit = if !emit_gstruct(i.rb(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        handoff(scan_pending_item(i.rb(), baseline, stops))
    } else {
        match required_name(i.rb(), baseline, stops) {
            Ok(true) => {
                if !emit_gstruct(i.rb(), baseline) {
                    emit_missing(&mut i, LeadingTrivia::default());
                    handoff(scan_pending_item(i.rb(), baseline, stops))
                } else {
                    parse_body(i.rb(), baseline, stops)
                }
            }
            Ok(false) => parse_body(i.rb(), baseline, stops),
            Err(item) => handoff(item),
        }
    };
    i.state.finish_node();
    exit
}

/// Returns whether a name was emitted. A body starter remains pending after a
/// missing name, while typed caller boundaries retain their complete Item.
fn required_name(mut i: RewriteIn, baseline: usize, stops: Stops) -> Result<bool, Item> {
    if observes(i.rb(), body_starter) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(false);
    }
    if let Some(boundary) = take_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(boundary);
    }
    if let Some(name) = i.token(scan_identifier) {
        i.state.token(SyntaxKind::Identifier.into(), &name.text);
        return Ok(true);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), baseline, stops);
        emit_token_item(&mut i, item);
        if continuation_has_body_starter(i.rb(), baseline) {
            let trivia = scan_trivia(i.rb());
            emit_leading_trivia(&mut i, &trivia);
            i.state.finish_node();
            return Ok(false);
        }
        if let Some(boundary) = take_boundary(i.rb(), baseline, stops) {
            i.state.finish_node();
            return Err(boundary);
        }
        if continuation_has_raw_name(i.rb(), baseline) {
            let trivia = scan_trivia(i.rb());
            emit_leading_trivia(&mut i, &trivia);
            i.state.finish_node();
            let name = i.token(scan_identifier).expect("raw-name probe was exact");
            i.state.token(SyntaxKind::Identifier.into(), &name.text);
            return Ok(true);
        }
        let trivia = scan_trivia(i.rb());
        emit_leading_trivia(&mut i, &trivia);
    }
}

fn parse_body(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    parse_body_item(i, item, baseline, stops)
}

fn parse_body_item(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> TailExit {
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            scan_after_completed(i, baseline, stops)
        }
        Some(TokenKind::LBrace) => {
            parse_delimited_fields(i, item, baseline, stops, FieldList::NamedBrace)
        }
        Some(TokenKind::LParen) => {
            parse_delimited_fields(i, item, baseline, stops, FieldList::Tuple)
        }
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            parse_indented_fields(i, baseline, stops)
        }
        _ if struct_boundary(i.rb(), &item, baseline, stops) || type_starter(&item) => {
            emit_missing(&mut i, LeadingTrivia::default());
            handoff(item)
        }
        _ => recover_body_introducer(i, item, baseline, stops),
    }
}

fn recover_body_introducer(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if body_starter_item(&item) {
            i.state.finish_node();
            return parse_body_item(i, item, baseline, stops);
        }
        if struct_boundary(i.rb(), &item, baseline, stops) || type_starter(&item) {
            i.state.finish_node();
            return handoff(item);
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum FieldList {
    NamedBrace,
    Tuple,
}

impl FieldList {
    fn close(self) -> TokenKind {
        match self {
            Self::NamedBrace => TokenKind::RBrace,
            Self::Tuple => TokenKind::RParen,
        }
    }

    fn type_boundary(self) -> Option<TypeApplyBoundary> {
        match self {
            Self::NamedBrace => Some(TypeApplyBoundary::StructNamedFields),
            Self::Tuple => None,
        }
    }
}

fn parse_delimited_fields(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    stops: Stops,
    list: FieldList,
) -> TailExit {
    emit_token_item(&mut i, open);
    let opening = scan_trivia(i.rb());
    let list_base = delimited_baseline(baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let item = field_item_after_trivia(
        i.rb(),
        LeadingTrivia::default(),
        list_base,
        stops,
        Some(list),
    );
    field_sequence(i, item, list_base, baseline, stops, Some(list))
}

fn parse_indented_fields(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let Some(block_indent) = introduced_body_indentation(i.rb()) else {
        let item = scan_pending_item(i.rb(), baseline, stops);
        emit_missing_field(&mut i, LeadingTrivia::default(), false);
        return handoff(item);
    };
    if block_indent <= baseline {
        let item = scan_pending_item(i.rb(), baseline, stops);
        emit_missing_field(&mut i, LeadingTrivia::default(), false);
        return handoff(item);
    }
    let opening = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &opening);
    let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), block_indent, stops);
    field_sequence(i, item, block_indent, baseline, stops, None)
}

fn field_sequence(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    owner_baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> TailExit {
    let mut need_field = true;
    let mut after_comma = false;
    loop {
        if let Some(list) = delimited {
            if token_kind(&item) == Some(list.close()) {
                emit_token_item(&mut i, item);
                return scan_after_completed(i, owner_baseline, stops);
            }
            if matches!(item.payload, Payload::Eof) || is_active_stop(i.rb(), &item, stops) {
                if after_comma
                    || (!need_field && implicit_delimited_newline(baseline, &item.leading))
                {
                    emit_missing_field(
                        &mut i,
                        std::mem::take(&mut item.leading),
                        list == FieldList::Tuple,
                    );
                }
                emit_missing(&mut i, LeadingTrivia::default());
                return handoff(item);
            }
        } else if indented_end(i.rb(), &item, baseline, stops) {
            if need_field && !after_comma {
                emit_missing_field(&mut i, LeadingTrivia::default(), false);
            }
            return handoff(item);
        }

        if delimited.is_some_and(|list| mismatched_close(&item, list.close())) {
            i.state.start_node(SyntaxKind::Error.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            let leading = scan_trivia(i.rb());
            item = field_item_after_trivia(i.rb(), leading, baseline, stops, delimited);
            continue;
        }

        if token_kind(&item) == Some(TokenKind::Comma) {
            if need_field {
                emit_missing_field(
                    &mut i,
                    std::mem::take(&mut item.leading),
                    delimited == Some(FieldList::Tuple),
                );
            }
            emit_token_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = field_item_after_trivia(i.rb(), leading, baseline, stops, delimited);
            need_field = true;
            after_comma = true;
            continue;
        }
        if !need_field && implicit_delimited_newline(baseline, &item.leading) {
            emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
            need_field = true;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            item = recover_separator(i.rb(), item, baseline, stops, delimited);
            need_field = true;
            after_comma = false;
            continue;
        }
        if !need_field {
            emit_missing(&mut i, std::mem::take(&mut item.leading));
            need_field = true;
        }
        if need_field && !item.leading.0.is_empty() {
            emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
        }

        let valid_start = match delimited {
            Some(FieldList::Tuple) => true,
            Some(FieldList::NamedBrace) | None => {
                raw_name(&item) || token_kind(&item) == Some(TokenKind::Colon)
            }
        };
        if !valid_start {
            if matches!(delimited, Some(FieldList::NamedBrace) | None) {
                let exit = recover_named_field(i.rb(), item, baseline, stops, delimited);
                item = match exit {
                    Err(Either::Left(item)) => item,
                    _ => return exit,
                };
                need_field = false;
                after_comma = false;
            } else {
                unreachable!("tuple fields admit the ordinary mandatory Type entry")
            }
        }

        if need_field {
            let exit = match delimited {
                Some(FieldList::Tuple) => tuple_field(i.rb(), item, baseline),
                Some(FieldList::NamedBrace) | None => {
                    named_field(i.rb(), item, baseline, stops, delimited)
                }
            };
            item = match exit {
                Err(Either::Left(item)) => item,
                _ => return exit,
            };
            need_field = false;
            after_comma = false;
        }
    }
}

fn named_field(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> TailExit {
    i.state.start_node(SyntaxKind::StructField.into());
    if raw_name(&item) {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, 0);
    } else {
        emit_missing(&mut i, std::mem::take(&mut item.leading));
    }

    if token_kind(&item) == Some(TokenKind::Colon)
        && indentation_after_newline(&item.leading).is_none()
    {
        emit_token_item(&mut i, item);
        return named_field_rhs(i, baseline, delimited);
    }

    if indentation_after_newline(&item.leading).is_some() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return handoff(item);
    }

    if type_starter(&item) {
        emit_missing(&mut i, std::mem::take(&mut item.leading));
        let exit = named_type(i.rb(), item, baseline, delimited);
        i.state.finish_node();
        return exit;
    }

    if field_boundary(i.rb(), &item, baseline, stops, delimited) {
        emit_missing(&mut i, std::mem::take(&mut item.leading));
        i.state.finish_node();
        return handoff(item);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if token_kind(&item) == Some(TokenKind::Colon)
            && indentation_after_newline(&item.leading).is_none()
        {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return named_field_rhs(i, baseline, delimited);
        }
        if type_starter(&item)
            && indentation_after_newline(&item.leading).is_none_or(|indent| indent > baseline)
        {
            i.state.finish_node();
            let exit = named_type(i.rb(), item, baseline, delimited);
            i.state.finish_node();
            return exit;
        }
        if field_boundary(i.rb(), &item, baseline, stops, delimited) {
            i.state.finish_node();
            i.state.finish_node();
            return handoff(item);
        }
    }
}

fn recover_named_field(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> TailExit {
    i.state.start_node(SyntaxKind::StructField.into());
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if token_kind(&item) == Some(TokenKind::Colon)
            && indentation_after_newline(&item.leading).is_none()
        {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return named_field_rhs(i, baseline, delimited);
        }
        if raw_name(&item) || field_boundary(i.rb(), &item, baseline, stops, delimited) {
            i.state.finish_node();
            i.state.finish_node();
            return handoff(item);
        }
    }
}

fn named_field_rhs(mut i: RewriteIn, baseline: usize, delimited: Option<FieldList>) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut primary = type_nud_item_after_trivia(i.rb(), leading);
    if indentation_after_newline(&primary.leading).is_none_or(|indent| indent > baseline) {
        emit_leading_trivia(&mut i, &std::mem::take(&mut primary.leading));
    }
    let exit = named_type(i.rb(), primary, baseline, delimited);
    i.state.finish_node();
    exit
}

fn named_type(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    delimited: Option<FieldList>,
) -> TailExit {
    let close = delimited.map_or(0, |list| with_type_outer_close(0, list.close()));
    required_type_expr_with_boundary(
        i,
        primary,
        baseline,
        Some(TypeApplyBoundary::StructNamedFields),
        close,
    )
}

fn field_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, &item.leading)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
        || delimited.is_some_and(|list| {
            matches!(
                token_kind(item),
                Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
            ) || token_kind(item) == Some(list.close())
        })
}

fn tuple_field(mut i: RewriteIn, item: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::StructField.into());
    let exit = required_type_expr_with_boundary(i.rb(), item, baseline, None, 1);
    i.state.finish_node();
    exit
}

fn recover_separator(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = field_item_after_trivia(i.rb(), leading, baseline, stops, delimited);
        if token_kind(&item) == Some(TokenKind::Comma)
            || delimited.is_some_and(|list| token_kind(&item) == Some(list.close()))
            || token_kind(&item) == Some(TokenKind::Colon)
            || raw_name(&item)
            || delimited == Some(FieldList::Tuple) && type_starter(&item)
            || matches!(item.payload, Payload::Eof)
            || is_active_stop(i.rb(), &item, stops)
            || implicit_delimited_newline(baseline, &item.leading)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn field_item_after_trivia(
    i: RewriteIn,
    leading: LeadingTrivia,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> Item {
    match delimited {
        Some(FieldList::Tuple) => type_nud_item_after_trivia(i, leading),
        Some(FieldList::NamedBrace) | None => {
            statement_item_after_trivia(i, leading, baseline, stops)
        }
    }
}

/// Scope-local pre-TypeApply candidate for named struct fields. The Item has
/// already consumed the candidate name; only the live same-line suffix is
/// inspected, and tuple fields never enable this hook.
pub(super) fn struct_named_fields_next_field_candidate(i: RewriteIn, item: &Item) -> bool {
    if item.leading.0.is_empty()
        || indentation_after_newline(&item.leading).is_some()
        || !raw_name(item)
    {
        return false;
    }
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none() && after.starts_with(':') && !after.starts_with("::")
    })
}

fn indented_end(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || indentation_after_newline(&item.leading).is_some_and(|indent| indent < baseline)
        || is_active_stop(i.rb(), item, stops)
}

fn emit_missing_field(i: &mut RewriteIn, leading: LeadingTrivia, tuple: bool) {
    i.state.start_node(SyntaxKind::StructField.into());
    if tuple {
        i.state.start_node(SyntaxKind::TypeExpression.into());
    }
    emit_missing(i, leading);
    if tuple {
        i.state.finish_node();
    }
    i.state.finish_node();
}

fn scan_after_completed(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let leading = scan_trivia(i.rb());
    handoff(statement_item_after_trivia(i, leading, baseline, stops))
}

fn scan_pending_item(mut i: RewriteIn, baseline: usize, stops: Stops) -> Item {
    let leading = scan_trivia(i.rb());
    statement_item_after_trivia(i, leading, baseline, stops)
}

fn take_boundary(mut i: RewriteIn, baseline: usize, stops: Stops) -> Option<Item> {
    i.token(|mut lex| {
        let item = scan_statement_item(lex.rb(), baseline, stops)?;
        struct_boundary_lex(lex, &item, baseline, stops).then_some(item)
    })
}

fn struct_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || implicit_delimited_newline(baseline, &item.leading)
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn struct_boundary_lex(mut i: LexIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || implicit_delimited_newline(baseline, &item.leading)
        || super::driver::is_active_stop_lex(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn emit_gstruct(mut i: RewriteIn, baseline: usize) -> bool {
    if !gstruct_allowed(i.rb(), baseline) {
        return false;
    }
    let trivia = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &trivia);
    true
}

fn gstruct_allowed(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        source_after_trivia(source)
            .2
            .is_none_or(|indentation| indentation > baseline)
    })
}

fn continuation_has_raw_name(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none_or(|indentation| indentation > baseline)
            && source_identifier(after).is_some()
    })
}

fn continuation_has_body_starter(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none_or(|indentation| indentation > baseline) && body_starter(after)
    })
}

fn prefixed_struct_candidate(source: &str, baseline: usize) -> bool {
    let (source, _, indentation) = source_after_trivia(source);
    indentation.is_none_or(|indentation| indentation > baseline)
        && source_identifier(source).is_some_and(|(word, _)| word == "struct")
}

fn body_starter(source: &str) -> bool {
    source.starts_with(';')
        || source.starts_with('{')
        || source.starts_with('(')
        || source.starts_with(':') && !source.starts_with("::") && !source.starts_with(":{")
}

fn body_starter_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::LParen | TokenKind::Colon)
    )
}

fn type_starter(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::LBracket
                | TokenKind::Forall
                | TokenKind::EffectRowApostrophe
                | TokenKind::PolymorphicVariantColon
        )
    )
}

fn mismatched_close(item: &Item, expected: TokenKind) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(expected)
}

fn raw_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn scan_exact_identifier(mut i: LexIn, expected: &str) -> Option<Token> {
    let token = scan_identifier(i.rb())?;
    (&*token.text == expected).then_some(token)
}

fn item_word(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) => Some(text),
        _ => None,
    }
}

fn emit_intro(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Token(token) = item.payload else {
        unreachable!()
    };
    emit_leading_trivia(i, &item.leading);
    i.state.token(kind.into(), &token.text);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!()
    };
    emit_leading_trivia(i, &item.leading);
    let kind = match &*token.text {
        "my" => SyntaxKind::MyKw,
        "our" => SyntaxKind::OurKw,
        "pub" => SyntaxKind::PubKw,
        _ => unreachable!(),
    };
    i.state.token(kind.into(), &token.text);
}

fn observes<F>(i: RewriteIn, predicate: F) -> bool
where
    F: FnOnce(&str) -> bool,
{
    i.map(|lex: LexIn| Some(predicate(lex.remainder())), |value| value)
        .expect("source observation is total")
}
