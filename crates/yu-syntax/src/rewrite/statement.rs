//! Direct canonical statements and their closed sequence owners.

use super::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    act_decl::{act_declaration_normalized, act_declaration_selected_normalized},
    binding::{
        binding_statement_normalized, binding_statement_selected_normalized, is_binding_visibility,
    },
    cast_decl::{cast_declaration_normalized, cast_declaration_selected_normalized},
    current_item::{CurrentItem, LineEntry, current_item},
    driver::{
        Either, MlMode, NormalizedExit, TailExit, advanced_origin, complete,
        continue_normalized_tail, delimited_baseline, expr_from_nud_normalized, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_nud_item,
        is_separator, ordinary_exit, scan_expression_literal_payload, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    enum_decl::{enum_declaration_normalized, enum_declaration_selected_normalized},
    error_decl::{error_declaration_normalized, error_declaration_selected_normalized},
    for_decl::{for_statement_normalized, for_statement_selected},
    impl_decl::{impl_declaration_normalized, impl_declaration_selected_normalized},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::scan_statement_payload,
    mod_decl::{mod_declaration_normalized, mod_declaration_selected_normalized},
    operator::stops_for,
    role_decl::{role_declaration_normalized, role_declaration_selected_normalized},
    struct_decl::{struct_declaration_normalized, struct_declaration_selected_normalized},
    type_decl::{type_declaration_normalized, type_declaration_selected_normalized},
    use_decl::{use_declaration_normalized, use_declaration_selected_normalized},
    yumark::FenceBoundary,
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

pub(super) fn statement(i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    ordinary_exit(statement_normalized(
        i,
        baseline,
        stops,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
    ))
}

pub(super) fn statement_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
    )
}

pub(super) fn statement_from_item(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    ordinary_exit(statement_from_item_normalized(
        i,
        item,
        baseline,
        stops,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn statement_from_item_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
    )
}

pub(super) fn canonical_statement(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(canonical_statement_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let admission = classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        .expect("canonical Statement wrapper requires an admitted Item");
    canonical_statement_from_admission_normalized(
        i,
        item,
        admission,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_from_admission_normalized(
    mut i: RewriteIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
    );
    i.state.finish_node();
    exit
}

/// Emit one already-selected canonical Statement inside a caller-owned
/// `Statement` node.  Recovery owners use this after emitting their local
/// prefix recovery without adding a nested Statement wrapper.
#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_contents_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let admission = classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        .expect("canonical Statement contents require an admitted Item");
    canonical_statement_contents_from_admission_normalized(
        i,
        item,
        admission,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_contents_from_admission_normalized(
    mut i: RewriteIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    match admission.0 {
        StatementFamily::Struct => {
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
            );
            return exit;
        }
        StatementFamily::Enum => {
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
            );
        }
        StatementFamily::Error => {
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
            );
        }
        StatementFamily::Mod => {
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
            );
            return exit;
        }
        StatementFamily::Type => {
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
            );
        }
        StatementFamily::Role => {
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
            );
        }
        StatementFamily::Impl => {
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
            );
        }
        StatementFamily::Cast => {
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
            );
        }
        StatementFamily::Act => {
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
            );
        }
        StatementFamily::For => {
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
            );
        }
        StatementFamily::Binding => {
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
            );
        }
        StatementFamily::Use => {
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
        StatementFamily::Expression => {
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
            );
        }
    }
}

pub(super) fn is_canonical_statement_nud(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    classify_statement_item_normalized(i, item, baseline, 0, None).is_some()
}

pub(super) fn is_canonical_statement_nud_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    classify_statement_item_normalized(i, item, baseline, item_origin, fence).is_some()
}

#[derive(Clone, Copy)]
pub(super) struct StatementAdmission(StatementFamily);

#[derive(Clone, Copy)]
enum StatementFamily {
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
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<StatementAdmission> {
    if item.payload_view().is_boundary() {
        return None;
    }
    let family =
        if struct_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Struct
        } else if enum_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Enum
        } else if error_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence)
        {
            StatementFamily::Error
        } else if mod_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Mod
        } else if type_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Type
        } else if role_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Role
        } else if impl_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Impl
        } else if cast_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Cast
        } else if act_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
            StatementFamily::Act
        } else if for_statement_selected(item) {
            StatementFamily::For
        } else if is_binding_visibility(item)
            && binding_statement_selected_normalized(i.rb(), item, baseline, item_origin, fence)
        {
            StatementFamily::Binding
        } else if use_declaration_selected_normalized(i.rb(), item, item_origin, fence) {
            StatementFamily::Use
        } else if !is_binding_visibility(item) && is_nud_item(item) {
            StatementFamily::Expression
        } else {
            return None;
        };
    Some(StatementAdmission(family))
}

#[derive(Clone, Copy)]
enum StatementSequencePolicy {
    Indented { block_indent: usize },
    Braced,
}

/// The canonical indented sequence owns its opening trivia and equal-indent
/// separators; dedent and unimplemented statement starts remain pending Items.
pub(super) fn indented_statement_block(i: RewriteIn, base_indent: usize, stops: Stops) -> TailExit {
    ordinary_exit(indented_statement_block_normalized(
        i,
        base_indent,
        stops,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(base_indent)).into(),
    ))
}

pub(super) fn indented_statement_block_normalized(
    mut i: RewriteIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, base_indent, stops);
    i.state
        .start_node(SyntaxKind::IndentedStatementBlock.into());
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let block_indent = indentation_after_newline(item.leading_view())
        .filter(|&indentation| indentation > base_indent)
        .expect("C2 admission proved a strictly indented block opening");
    let ambient = ambient.map(|view| view.statement(block_indent));

    item.emit_all_remaining_leading(&mut *i.state);
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Indented { block_indent },
        block_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
        ambient,
    );
    i.state.finish_node();
    exit
}

/// The braced-primary wrapper owns its delimiters and local separator stops;
/// the closed sequence helper owns normal statement progression for both
/// current block forms.
#[allow(clippy::too_many_arguments)]
pub(super) fn braced_nud_normalized(
    mut i: RewriteIn,
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
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = braced_statement_block_normalized(
        i.rb(),
        open,
        incoming_baseline,
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
    )
}

/// Construct the existing braced canonical-statement owner without attaching
/// an expression tail. Declaration bodies reuse this exact delimiter scope.
pub(super) fn braced_statement_block(
    i: RewriteIn,
    open: Item,
    incoming_baseline: usize,
) -> TailExit {
    ordinary_exit(braced_statement_block_normalized(
        i,
        open,
        incoming_baseline,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(incoming_baseline)).into(),
    ))
}

pub(super) fn braced_statement_block_normalized(
    mut i: RewriteIn,
    open: Item,
    incoming_baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let ambient = ambient.map(AmbientClaimView::braced);
    i.state
        .start_node(SyntaxKind::BracedStatementBlockExpression.into());
    emit_token_item(&mut i, open);
    let stops = stops_for(TokenKind::RBrace);
    let (mut item, item_origin, line_entry) = statement_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        incoming_baseline,
        stops,
    );
    if item.payload_view().is_boundary() {
        let exit = braced_terminal_normalized(i.rb(), item, line_entry);
        i.state.finish_node();
        return exit;
    }
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    item.emit_all_remaining_leading(&mut *i.state);
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Braced,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
        ambient,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn statement_sequence_normalized(
    mut i: RewriteIn,
    mut item: Item,
    policy: StatementSequencePolicy,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    mut first: bool,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let mut known_admission = None;
    loop {
        match policy {
            StatementSequencePolicy::Indented { block_indent } => {
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
                    known_admission,
                    ambient,
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
            StatementSequencePolicy::Braced => {
                if item.payload_view().is_boundary()
                    || item.payload_view().is_eof()
                    || token_kind(&item) == Some(TokenKind::RBrace)
                {
                    if !first
                        && !item.payload_view().is_boundary()
                        && implicit_delimited_newline(baseline, item.leading_view())
                    {
                        emit_separator_leading(&mut i, &mut item);
                    }
                    return braced_terminal_normalized(i, item, line_entry);
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
                    known_admission,
                    ambient,
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
    mut i: RewriteIn,
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
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    missing_on_boundary: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
    known_admission: Option<Option<StatementAdmission>>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    if indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
        if missing_on_boundary {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    let admission = known_admission.unwrap_or_else(|| {
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
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
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_indented_statement_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops) {
            i.state.finish_node();
            return (item, None, item_origin, line_entry);
        }
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return (item, Some(admission), item_origin, line_entry);
        }
    }
}

fn indented_statement_slot_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn indented_statement_retry_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    indented_statement_slot_boundary(i.rb(), item, block_indent, stops)
        || indentation_after_newline(item.leading_view()) == Some(block_indent)
}

fn indented_statement_outer_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn braced_terminal_normalized(
    mut i: RewriteIn,
    item: Item,
    line_entry: LineEntry,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(missing_brace_close(i, item), line_entry);
    }
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return complete(Ok(()), line_entry);
    }
    debug_assert!(item.payload_view().is_eof());
    complete(missing_brace_close(i, item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn braced_statement_slot_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
    known_admission: Option<Option<StatementAdmission>>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return braced_terminal_normalized(i, item, line_entry);
    }
    let admission = known_admission.unwrap_or_else(|| {
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
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
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_braced_statement_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if braced_statement_boundary(&item, baseline) {
            i.state.finish_node();
            return (item, None, item_origin, line_entry);
        }
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return (item, Some(admission), item_origin, line_entry);
        }
    }
}

fn braced_statement_boundary(item: &Item, baseline: usize) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || token_kind(item) == Some(TokenKind::RBrace)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn braced_statement_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry, usize, Option<Option<StatementAdmission>>), NormalizedExit> {
    match exit {
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized canonical statements do not defer declaration owners")
        }
        NormalizedExit::Complete(Ok(()), line_entry) => Err(complete(Ok(()), line_entry)),
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            if implicit_delimited_newline(baseline, end.item.leading_view()) {
                emit_separator_leading(&mut i, &mut end.item);
            }
            Err(complete(missing_brace_close(i, end.item), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            Err(complete(missing_brace_close(i, item), line_entry))
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
                emit_missing(&mut i, LeadingTrivia::default());
            }
            Ok((item, line_entry, item_origin, Some(admission)))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn braced_explicit_separator_normalized(
    mut i: RewriteIn,
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
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.finish_node();
    (item, item_origin, line_entry)
}

fn emit_separator_leading(i: &mut RewriteIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.finish_node();
}

fn missing_brace_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(item)
}

pub(super) fn statement_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
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
        })
        .expect("statement payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}
