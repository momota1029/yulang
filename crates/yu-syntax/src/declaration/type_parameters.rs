//! Shared declaration type-parameter scanning and CST construction.

use crate::{
    cursor::SyntaxIn,
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, TokenKind},
        lexer::{is_declaration_starter_word, scan_declaration_type_parameter},
        observation::token_kind,
        position::{advanced_origin, suffix_marker},
        yumark::FenceBoundary,
    },
    syntax_kind::SyntaxKind,
};

/// Selects whether a declaration admits only sigil type variables or also
/// keeps the legacy bare-identifier parameter vocabulary of type/enum/error.
#[derive(Clone, Copy)]
pub(super) enum ParameterForm {
    SigilOnly,
    SigilOrIdentifier,
}

pub(super) fn parameters_normalized(
    mut i: SyntaxIn,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    form: ParameterForm,
) {
    let Some((parameter, next_origin, next_entry)) =
        parameter_item_normalized(i.rb(), *item_origin, *line_entry, fence, form)
    else {
        return;
    };
    *item_origin = next_origin;
    *line_entry = next_entry;
    i.state
        .start_node(SyntaxKind::DeclarationTypeParameterList.into());
    emit_parameter(&mut i, parameter);
    while let Some((parameter, next_origin, next_entry)) =
        parameter_item_normalized(i.rb(), *item_origin, *line_entry, fence, form)
    {
        *item_origin = next_origin;
        *line_entry = next_entry;
        emit_parameter(&mut i, parameter);
    }
    i.state.finish_node();
}

fn parameter_spelling(parameter: &Item, form: ParameterForm) -> bool {
    if token_kind(parameter) == Some(TokenKind::SigilIdentifier) {
        return true;
    }
    if matches!(form, ParameterForm::SigilOnly) {
        return false;
    }
    debug_assert_eq!(token_kind(parameter), Some(TokenKind::Identifier));
    let spelling = parameter
        .payload_view()
        .spelling()
        .expect("declaration parameter scanner returns identifiers");
    !is_declaration_starter_word(spelling)
        && !matches!(
            spelling,
            "for"
                | "realm"
                | "band"
                | "as"
                | "without"
                | "with"
                | "if"
                | "case"
                | "catch"
                | "where"
                | "elsif"
                | "else"
                | "derives"
        )
}

fn parameter_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    form: ParameterForm,
) -> Option<(Item, usize, LineEntry)> {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i.token(|lex| {
        let current = current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, _, _, _, _| {
                let parameter = lex.token(scan_declaration_type_parameter)?;
                Some(AcceptedPayload {
                    payload: CurrentPayload::Token(parameter),
                    next_line_entry: LineEntry::InLine,
                })
            },
        )?;
        (!current.item.payload_view().is_boundary()
            && !current.item.payload_view().is_eof()
            && !current.item.leading_view().is_grammar_empty()
            && !current.item.leading_view().contains_line_break()
            && parameter_spelling(&current.item, form))
        .then_some(current)
    })?;
    Some((
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    ))
}

fn emit_parameter(i: &mut SyntaxIn, parameter: Item) {
    let kind = match token_kind(&parameter) {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        _ => unreachable!("declaration parameter scanner returns identifiers"),
    };
    parameter.emit_remaining(&mut *i.state, kind);
}
