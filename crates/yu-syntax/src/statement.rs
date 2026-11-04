//! Direct canonical statements and their closed sequence owners.

use crate::ambient_claim::{AmbientClaimContext, AmbientClaimView};
#[cfg(test)]
use crate::handoff::ordinary_exit;
use reborrow_generic::Reborrow as _;

use crate::{
    lexical::operator_scan::OperatorSite, operator_table::BindingPower, syntax_kind::SyntaxKind,
};

use crate::{
    cursor::recovery::emit::{emit_recovery_error_run, emit_recovery_missing, emit_token_item},
    cursor::{LexIn, SyntaxIn},
    declaration::{
        DocCommentAdmission, act_declaration_normalized, act_declaration_selected_lexical,
        binding_statement_normalized, binding_statement_selected_lexical,
        cast_declaration_normalized, cast_declaration_selected_lexical,
        doc_comment_declaration_normalized, doc_comment_selected_lexical,
        enum_declaration_normalized, enum_declaration_selected_lexical,
        error_declaration_normalized, error_declaration_selected_lexical,
        impl_declaration_normalized, impl_declaration_selected_lexical, is_binding_visibility,
        mod_declaration_normalized, mod_declaration_selected_lexical, role_declaration_normalized,
        role_declaration_selected_lexical, struct_declaration_normalized,
        struct_declaration_selected_lexical, type_declaration_normalized,
        type_declaration_selected_lexical, use_declaration_normalized,
        use_declaration_selected_lexical,
    },
    expression::{
        continue_normalized_tail, expr_from_nud_normalized,
        for_decl::{for_statement_normalized, for_statement_selected},
        is_nud_item,
    },
    handoff::{Either, MlMode, NormalizedExit, TailExit, complete, handoff},
    lexical::{
        current_item::{LineEntry, current_item},
        expression_item::scan_expression_literal_payload,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::scan_statement_payload,
        observation::{
            delimited_baseline, implicit_delimited_newline, indentation_after_newline,
            is_active_stop, is_active_stop_lex, is_close, is_separator, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_COLON, Stops, stops_for},
        yumark::FenceBoundary,
    },
    yumark::judge::StatementPosition,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StatementLineHandoff {
    OrdinaryLayout,
    BracedStatementSequence,
    CatchBracedArm,
    CatchArmSequenceThroughInlineCanonicalStatement,
}

impl StatementLineHandoff {
    pub(super) fn through_inline_statement(self) -> Self {
        match self {
            Self::CatchBracedArm | Self::CatchArmSequenceThroughInlineCanonicalStatement => {
                Self::CatchArmSequenceThroughInlineCanonicalStatement
            }
            other => other,
        }
    }
}

#[cfg(test)]
pub(super) fn statement(i: SyntaxIn, baseline: usize, stops: Stops) -> TailExit {
    ordinary_exit(statement_normalized(
        i,
        baseline,
        stops,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    ))
}

#[cfg(test)]
pub(super) fn statement_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let ambient = ambient.map(|view| view.statement(baseline));
    let (item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    statement_from_item_normalized(
        i,
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(super) fn statement_from_item_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let ambient = ambient.map(|view| view.statement(baseline));
    let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    else {
        return complete(handoff(item), line_entry);
    };
    canonical_statement_from_admission_normalized(
        i,
        item,
        admission,
        baseline,
        stops,
        StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_from_admission_normalized(
    mut i: SyntaxIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Statement.into());
    let exit = canonical_statement_contents_from_admission_normalized(
        i.rb(),
        item,
        admission,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_contents_from_admission_normalized(
    mut i: SyntaxIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match admission.0 {
        StatementKind::DocComment(doc) => {
            return doc_comment_declaration_normalized(
                i.rb(),
                item,
                doc,
                item_origin,
                line_entry,
                fence,
            );
        }
        StatementKind::Struct => {
            let exit = struct_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            return exit;
        }
        StatementKind::Enum => {
            return enum_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Error => {
            return error_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Mod => {
            let exit = mod_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            return exit;
        }
        StatementKind::Type => {
            return type_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Role => {
            return role_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Impl => {
            return impl_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Cast => {
            return cast_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Act => {
            return act_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::For => {
            return for_statement_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Binding => {
            return binding_statement_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        StatementKind::Use => {
            return use_declaration_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
        }
        StatementKind::Expression => {
            return expr_from_nud_normalized(
                i.rb(),
                item,
                None,
                baseline,
                stops,
                MlMode::All,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
    }
}

#[cfg(test)]
pub(super) fn is_canonical_statement_nud(i: SyntaxIn, item: &Item, baseline: usize) -> bool {
    classify_statement_item_normalized_at(
        i,
        item,
        baseline,
        0,
        None,
        StatementPosition::NonStatement,
    )
    .is_some()
}

#[derive(Clone, Copy)]
pub(super) struct StatementAdmission(StatementKind);

#[derive(Clone, Copy)]
pub(super) enum StatementKind {
    DocComment(DocCommentAdmission),
    Struct,
    Enum,
    Error,
    Mod,
    Type,
    Role,
    Impl,
    Cast,
    Act,
    For,
    Binding,
    Use,
    Expression,
}

pub(super) fn classify_statement_item_normalized(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<StatementAdmission> {
    let position = statement_position(item, item_origin, false);
    classify_statement_item_normalized_at(i, item, baseline, item_origin, fence, position)
}

pub(super) fn classify_statement_item_normalized_at(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    position: StatementPosition,
) -> Option<StatementAdmission> {
    i.map(
        |lex: LexIn| {
            Some(classify_statement_item_lexical_at(
                lex.remainder(),
                item,
                baseline,
                item_origin,
                fence,
                position,
            ))
        },
        |admission| admission,
    )
    .flatten()
}

pub(super) fn classify_statement_item_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<StatementAdmission> {
    let position = statement_position(item, item_origin, false);
    classify_statement_item_lexical_at(source, item, baseline, item_origin, fence, position)
}

pub(super) fn classify_statement_item_lexical_at(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    position: StatementPosition,
) -> Option<StatementAdmission> {
    if item.payload_view().is_boundary() {
        return None;
    }
    let family =
        if let Some(doc) = doc_comment_selected_lexical(source, item, item_origin, position) {
            StatementKind::DocComment(doc)
        } else if struct_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Struct
        } else if enum_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Enum
        } else if error_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Error
        } else if mod_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Mod
        } else if type_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Type
        } else if role_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Role
        } else if impl_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Impl
        } else if cast_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Cast
        } else if act_declaration_selected_lexical(source, item, baseline, item_origin, fence) {
            StatementKind::Act
        } else if for_statement_selected(item) {
            StatementKind::For
        } else if is_binding_visibility(item)
            && binding_statement_selected_lexical(source, item, baseline, item_origin, fence)
        {
            StatementKind::Binding
        } else if use_declaration_selected_lexical(source, item, item_origin, fence) {
            StatementKind::Use
        } else if !is_binding_visibility(item)
            && (is_nud_item(item) || crate::lexical::lexer::is_expression_symbol_item(source, item))
        {
            StatementKind::Expression
        } else {
            return None;
        };
    Some(StatementAdmission(family))
}

pub(super) fn statement_position(
    item: &Item,
    item_origin: usize,
    allow_same_line: bool,
) -> StatementPosition {
    if item_origin == 0 || item.leading_view().contains_line_break() {
        StatementPosition::CanonicalLineStart {
            base_col: item.leading_view().indentation_after_newline().unwrap_or(0),
        }
    } else if allow_same_line {
        StatementPosition::CanonicalSameLine
    } else {
        StatementPosition::NonStatement
    }
}

#[derive(Clone, Copy)]
enum StatementSequencePolicy {
    Indented {
        block_indent: usize,
        allow_doc_comment: bool,
    },
    Braced {
        allow_doc_comment: bool,
    },
}

pub(super) fn indented_statement_block_normalized(
    i: SyntaxIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    indented_statement_block_inner_normalized(
        i,
        base_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
        false,
        true,
    )
}

pub(super) fn indented_owner_field_body_normalized(
    i: SyntaxIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    indented_statement_block_inner_normalized(
        i,
        base_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
        false,
        false,
    )
}

pub(super) fn indented_declaration_body_normalized(
    i: SyntaxIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    indented_statement_block_inner_normalized(
        i,
        base_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
        true,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn indented_statement_block_inner_normalized(
    mut i: SyntaxIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    where_prefix: bool,
    allow_doc_comment: bool,
) -> NormalizedExit {
    let sequence = Some(if allow_doc_comment {
        crate::sequence::SequenceOwner::IndentedStatement
    } else {
        crate::sequence::SequenceOwner::IndentedOwnerField
    });
    let (mut item, mut item_origin, mut line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, base_indent, stops);
    i.state
        .start_node(SyntaxKind::IndentedStatementBlock.into());
    if item.payload_view().is_boundary() {
        emit_indented_missing(i.rb(), &mut item, item_origin);
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let block_indent = indentation_after_newline(item.leading_view())
        .filter(|&indentation| indentation > base_indent)
        .expect("C2 admission proved a strictly indented block opening");
    let first_position = statement_position(&item, item_origin, true);
    let ambient = ambient.map(|view| view.statement(block_indent));

    if !indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    while where_prefix && is_where_clause_keyword(&item) {
        let (next, next_origin, next_line_entry) = where_clause_normalized(
            i.rb(),
            item,
            block_indent,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item_origin = next_origin;
        item = next;
        line_entry = next_line_entry;
        if !indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
    }
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Indented {
            block_indent,
            allow_doc_comment,
        },
        block_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
        first_position,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

fn is_where_clause_keyword(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some("where")
}

#[allow(clippy::too_many_arguments)]
fn where_clause_normalized(
    mut i: SyntaxIn,
    keyword: Item,
    baseline: usize,
    caller_stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::WhereClause.into());
    keyword.emit_remaining(&mut *i.state, SyntaxKind::WhereKw);
    let entry = suffix_marker(i.rb());
    item_origin = advanced_origin(item_origin, entry, i.rb());

    let (subject, subject_origin, subject_line) =
        crate::type_expr::type_nud_item_normalized_with_ambient(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    if implicit_delimited_newline(baseline, subject.leading_view()) {
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            subject.extent(subject_origin).recovery_range().start,
        );
        i.state.finish_node();
        return (subject, subject_origin, subject_line);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, subject_complete) =
        crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            subject,
            baseline,
            caller_stops | STOP_COLON,
            crate::type_expr::TypeOuterBoundary::NONE,
            subject_origin,
            subject_line,
            fence,
            ambient,
        );
    item_origin = advanced_origin(subject_origin, child_entry, i.rb());
    let (item, origin, next_line_entry) =
        where_type_successor(i.rb(), exit, item_origin, baseline, caller_stops, fence);
    item_origin = origin;
    line_entry = next_line_entry;
    if !subject_complete || token_kind(&item) != Some(TokenKind::Colon) {
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            item.extent(item_origin).recovery_range().start,
        );
        i.state.finish_node();
        return (item, item_origin, line_entry);
    }

    let entry = suffix_marker(i.rb());
    emit_token_item(&mut i, item);
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let (role, role_origin, role_line) = crate::type_expr::type_nud_item_normalized_with_ambient(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    if implicit_delimited_newline(baseline, role.leading_view()) {
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            role.extent(role_origin).recovery_range().start,
        );
        i.state.finish_node();
        return (role, role_origin, role_line);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, role_complete) =
        crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            role,
            baseline,
            caller_stops,
            crate::type_expr::TypeOuterBoundary::NONE,
            role_origin,
            role_line,
            fence,
            ambient,
        );
    item_origin = advanced_origin(role_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        where_type_successor(i.rb(), exit, item_origin, baseline, caller_stops, fence);
    if !role_complete {
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            item.extent(item_origin).recovery_range().start,
        );
    }
    i.state.finish_node();
    (item, item_origin, line_entry)
}

#[allow(clippy::too_many_arguments)]
fn where_type_successor(
    i: SyntaxIn,
    exit: NormalizedExit,
    item_origin: usize,
    baseline: usize,
    caller_stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Ok(()), line_entry) => {
            statement_item_normalized(i, item_origin, line_entry, fence, baseline, caller_stops)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer a where clause")
        }
    }
}

/// The braced-primary wrapper owns its delimiters and local separator stops;
/// the closed sequence helper owns normal statement progression for both
/// current block forms.
#[allow(clippy::too_many_arguments)]
pub(super) fn braced_nud_normalized(
    mut i: SyntaxIn,
    open: Item,
    threshold: Option<&BindingPower>,
    incoming_baseline: usize,
    outer_stops: Stops,
    outer_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = braced_statement_block_with_recovery_normalized(
        i.rb(),
        open,
        incoming_baseline,
        outer_stops,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    continue_normalized_tail(
        i,
        threshold,
        incoming_baseline,
        outer_stops,
        outer_ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

pub(super) fn braced_statement_block_normalized(
    i: SyntaxIn,
    open: Item,
    incoming_baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    braced_statement_block_inner_normalized(
        i,
        open,
        incoming_baseline,
        0,
        item_origin,
        line_entry,
        fence,
        ambient,
        true,
    )
}

pub(super) fn braced_owner_field_block_normalized(
    i: SyntaxIn,
    open: Item,
    incoming_baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    braced_statement_block_inner_normalized(
        i,
        open,
        incoming_baseline,
        0,
        item_origin,
        line_entry,
        fence,
        ambient,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn braced_statement_block_with_recovery_normalized(
    i: SyntaxIn,
    open: Item,
    incoming_baseline: usize,
    inherited_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    braced_statement_block_inner_normalized(
        i,
        open,
        incoming_baseline,
        inherited_stops,
        item_origin,
        line_entry,
        fence,
        ambient,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn braced_statement_block_inner_normalized(
    mut i: SyntaxIn,
    open: Item,
    incoming_baseline: usize,
    inherited_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    allow_doc_comment: bool,
) -> NormalizedExit {
    let sequence = Some(if allow_doc_comment {
        crate::sequence::SequenceOwner::BracedStatement
    } else {
        crate::sequence::SequenceOwner::BracedOwnerField
    });
    let ambient = ambient.map(AmbientClaimView::braced);
    i.state
        .start_node(SyntaxKind::BracedStatementBlockExpression.into());
    emit_token_item(&mut i, open);
    let stops = stops_for(TokenKind::RBrace)
        | (inherited_stops & crate::lexical::stops::LAMBDA_RECOVERY_BOUNDARY);
    let (mut item, item_origin, line_entry) = statement_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        incoming_baseline,
        stops,
    );
    if item.payload_view().is_boundary() || is_close(&item) {
        let exit = braced_terminal_normalized(i.rb(), item, item_origin, line_entry);
        i.state.finish_node();
        return exit;
    }
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    let first_position = statement_position(&item, item_origin, true);
    item.emit_all_remaining_leading(&mut *i.state);
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Braced { allow_doc_comment },
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
        first_position,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn statement_sequence_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    policy: StatementSequencePolicy,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    mut first: bool,
    first_position: StatementPosition,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let mut known_admission = None;
    loop {
        match policy {
            StatementSequencePolicy::Indented {
                block_indent,
                allow_doc_comment,
            } => {
                let entry = suffix_marker(i.rb());
                let exit = indented_statement_slot_normalized(
                    i.rb(),
                    item,
                    baseline,
                    block_indent,
                    stops,
                    true,
                    item_origin,
                    line_entry,
                    fence,
                    first,
                    first_position,
                    allow_doc_comment,
                    known_admission,
                    ambient,
                    sequence,
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                (item, line_entry) = match indented_statement_successor_normalized(
                    i.rb(),
                    exit,
                    block_indent,
                    stops,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
            }
            StatementSequencePolicy::Braced { allow_doc_comment } => {
                if item.payload_view().is_boundary()
                    || item.payload_view().is_eof()
                    || is_close(&item)
                {
                    if !first
                        && !item.payload_view().is_boundary()
                        && (!is_close(&item) || token_kind(&item) == Some(TokenKind::RBrace))
                        && implicit_delimited_newline(baseline, item.leading_view())
                    {
                        emit_separator_leading(&mut i, &mut item);
                    }
                    return braced_terminal_normalized(i, item, item_origin, line_entry);
                }
                let entry = suffix_marker(i.rb());
                let exit = braced_statement_slot_normalized(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                    first,
                    first_position,
                    allow_doc_comment,
                    known_admission,
                    ambient,
                    sequence,
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                (item, line_entry, item_origin, known_admission) =
                    match braced_statement_successor_normalized(
                        i.rb(),
                        exit,
                        baseline,
                        stops,
                        item_origin,
                        fence,
                    ) {
                        Ok(next) => next,
                        Err(exit) => return exit,
                    };
            }
        }
        first = false;
    }
}

fn indented_statement_successor_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    block_indent: usize,
    stops: Stops,
) -> Result<(Item, LineEntry), NormalizedExit> {
    let NormalizedExit::Complete(Err(Either::Left(item)), line_entry) = exit else {
        return Err(exit);
    };
    if indentation_after_newline(item.leading_view()) != Some(block_indent)
        || indented_statement_outer_boundary(i.rb(), &item, block_indent, stops)
    {
        return Err(complete(handoff(item), line_entry));
    }
    Ok((item, line_entry))
}

#[allow(clippy::too_many_arguments)]
fn indented_statement_slot_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    missing_on_boundary: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
    first_position: StatementPosition,
    allow_doc_comment: bool,
    known_admission: Option<Option<StatementAdmission>>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_indented_missing(i.rb(), &mut item, item_origin);
        }
        return complete(handoff(item), line_entry);
    }
    if indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
        if missing_on_boundary {
            emit_indented_missing(i.rb(), &mut item, item_origin);
        }
        return complete(handoff(item), line_entry);
    }
    let admission = known_admission.unwrap_or_else(|| {
        classify_statement_item_normalized_at(
            i.rb(),
            &item,
            baseline,
            item_origin,
            fence,
            if allow_doc_comment {
                if first {
                    first_position
                } else {
                    statement_position(&item, item_origin, false)
                }
            } else {
                StatementPosition::NonStatement
            },
        )
    });
    if let Some(admission) = admission {
        if !first {
            emit_separator_leading(&mut i, &mut item);
        }
        return canonical_statement_from_admission_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            StatementLineHandoff::OrdinaryLayout,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }

    if !first {
        emit_separator_leading(&mut i, &mut item);
    }

    let (next, admission, next_origin, next_line_entry) = retry_indented_statement_normalized(
        i.rb(),
        item,
        baseline,
        block_indent,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    item = next;
    if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops) {
        return complete(handoff(item), next_line_entry);
    }
    canonical_statement_from_admission_normalized(
        i,
        item,
        admission.expect("retry returned an admitted canonical Statement"),
        baseline,
        stops,
        StatementLineHandoff::OrdinaryLayout,
        next_origin,
        next_line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_indented_statement_normalized(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(i, |run| {
        loop {
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_statement_item_lexical(lex, item_origin, line_entry, fence, baseline, stops)
            });
            let boundary = indented_statement_lexical_boundary(&item, block_indent)
                || indentation_after_newline(item.leading_view()) == Some(block_indent)
                || run.lexical(|lex| is_active_stop_lex(lex, &item, stops));
            let admission = if boundary {
                None
            } else {
                run.lexical(|lex| {
                    classify_statement_item_lexical(
                        lex.remainder(),
                        &item,
                        baseline,
                        item_origin,
                        fence,
                    )
                })
            };
            if boundary || admission.is_some() {
                return (item, admission, item_origin, line_entry);
            }
        }
    })
}

fn emit_indented_missing(i: SyntaxIn, item: &mut Item, origin: usize) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("boundary coordinate")
            .coordinate()
    } else {
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
        }
        item.extent(origin).recovery_range().start
    };
    emit_recovery_missing(i, LeadingTrivia::default(), at);
}

fn indented_statement_lexical_boundary(item: &Item, block_indent: usize) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn indented_statement_slot_boundary(
    mut i: SyntaxIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    indented_statement_lexical_boundary(item, block_indent) || is_active_stop(i.rb(), item, stops)
}

fn indented_statement_retry_boundary(
    mut i: SyntaxIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    indented_statement_slot_boundary(i.rb(), item, block_indent, stops)
        || indentation_after_newline(item.leading_view()) == Some(block_indent)
}

fn indented_statement_outer_boundary(
    mut i: SyntaxIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || is_close(item)
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn braced_terminal_normalized(
    mut i: SyntaxIn,
    item: Item,
    item_origin: usize,
    line_entry: LineEntry,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(missing_brace_close(i, item, item_origin), line_entry);
    }
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return complete(Ok(()), line_entry);
    }
    debug_assert!(item.payload_view().is_eof() || is_close(&item));
    complete(missing_brace_close(i, item, item_origin), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn braced_statement_slot_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
    first_position: StatementPosition,
    allow_doc_comment: bool,
    known_admission: Option<Option<StatementAdmission>>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return braced_terminal_normalized(i, item, item_origin, line_entry);
    }
    if is_separator(&item) {
        if first && token_kind(&item) == Some(TokenKind::Semicolon) {
            let (item, _, line_entry) = braced_explicit_separator_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
            return complete(handoff(item), line_entry);
        }
        // Retire the newline separator before handing this fresh required-slot
        // punctuation to the explicit separator owner; otherwise successor
        // selection retries the same newline-leading Item indefinitely.
        if implicit_delimited_newline(baseline, item.leading_view()) {
            emit_separator_leading(&mut i, &mut item);
        }
        emit_braced_missing(i.rb(), &item, item_origin);
        return complete(handoff(item), line_entry);
    }
    let admission = known_admission.unwrap_or_else(|| {
        classify_statement_item_normalized_at(
            i.rb(),
            &item,
            baseline,
            item_origin,
            fence,
            if !allow_doc_comment {
                StatementPosition::NonStatement
            } else if first {
                first_position
            } else {
                statement_position(&item, item_origin, false)
            },
        )
    });
    if let Some(admission) = admission {
        if !first && implicit_delimited_newline(baseline, item.leading_view()) {
            emit_separator_leading(&mut i, &mut item);
        }
        return canonical_statement_from_admission_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            StatementLineHandoff::BracedStatementSequence,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }

    if !first && implicit_delimited_newline(baseline, item.leading_view()) {
        emit_separator_leading(&mut i, &mut item);
    }

    let (item, admission, item_origin, line_entry) = retry_braced_statement_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if braced_statement_boundary(&item, baseline) {
        complete(handoff(item), line_entry)
    } else if let Some(admission) = admission {
        canonical_statement_from_admission_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            StatementLineHandoff::BracedStatementSequence,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_braced_statement_normalized(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(i, |run| {
        loop {
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_statement_item_lexical(lex, item_origin, line_entry, fence, baseline, stops)
            });
            let boundary = braced_statement_boundary(&item, baseline);
            let admission = if boundary {
                None
            } else {
                run.lexical(|lex| {
                    classify_statement_item_lexical(
                        lex.remainder(),
                        &item,
                        baseline,
                        item_origin,
                        fence,
                    )
                })
            };
            if boundary || admission.is_some() {
                return (item, admission, item_origin, line_entry);
            }
        }
    })
}

fn braced_statement_boundary(item: &Item, baseline: usize) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn braced_statement_successor_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry, usize, Option<Option<StatementAdmission>>), NormalizedExit> {
    let (exit, item_origin) = match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            let (item, item_origin, line_entry) =
                statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
            (complete(handoff(item), line_entry), item_origin)
        }
        exit => (exit, item_origin),
    };
    match exit {
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized canonical statements do not defer declaration owners")
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("completed child has acquired its enclosing sequence successor")
        }
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            if implicit_delimited_newline(baseline, end.item.leading_view()) {
                emit_separator_leading(&mut i, &mut end.item);
            }
            Err(complete(
                missing_brace_close(i, end.item, item_origin),
                line_entry,
            ))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary()
                || (is_close(&item) && token_kind(&item) != Some(TokenKind::RBrace)) =>
        {
            Err(complete(
                missing_brace_close(i, item, item_origin),
                line_entry,
            ))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if implicit_delimited_newline(baseline, item.leading_view()) =>
        {
            Ok((item, line_entry, item_origin, None))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if token_kind(&item) == Some(TokenKind::RBrace) =>
        {
            emit_token_item(&mut i, item);
            Err(complete(Ok(()), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) if is_separator(&item) => {
            let (item, item_origin, line_entry) = braced_explicit_separator_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
            Ok((item, line_entry, item_origin, None))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            let admission =
                classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence);
            if admission.is_some() {
                emit_braced_missing(i.rb(), &item, item_origin);
            }
            Ok((item, line_entry, item_origin, Some(admission)))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn braced_explicit_separator_normalized(
    mut i: SyntaxIn,
    separator: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    emit_token_item(&mut i, separator);
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    if !item.payload_view().is_boundary()
        && !(is_close(&item) && token_kind(&item) != Some(TokenKind::RBrace))
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.finish_node();
    (item, item_origin, line_entry)
}

fn emit_separator_leading(i: &mut SyntaxIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.finish_node();
}

fn missing_brace_close(mut i: SyntaxIn, mut item: Item, origin: usize) -> TailExit {
    if item.payload_view().is_eof() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_braced_missing(i.rb(), &item, origin);
    handoff(item)
}

fn emit_braced_missing(i: SyntaxIn, item: &Item, origin: usize) {
    let at = item
        .payload_view()
        .pending_boundary()
        .map(|boundary| boundary.coordinate())
        .unwrap_or_else(|| item.extent(origin).recovery_range().start);
    emit_recovery_missing(i, LeadingTrivia::default(), at);
}

pub(super) fn statement_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_statement_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        ))
    })
    .expect("statement payload scanning is total")
}

pub(super) fn scan_statement_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
        current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, leading, origin, fence, _| {
                scan_expression_literal_payload(lex.rb(), OperatorSite::Nud).or_else(|| {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                })
            },
        )
        .expect("statement payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("a Statement coordinate fits usize"),
        current.next_line_entry,
    )
}
