//! Direct expression ownership and Item handoff for the parser.

use super::required_operand::required_expr_after_accept_normalized;
use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
#[cfg(test)]
use crate::lexical::{current_item::CurrentItem, lexer::scan_nud_payload};

use reborrow_generic::Reborrow as _;

use crate::{
    lexical::operator_scan::OperatorSite, operator_table::BindingPower, syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::emit::{emit_identifier_core, emit_integer_core, emit_operator_use},
    cursor::SyntaxIn,
    expression::{
        case_like::{CaseLikeFamily, case_like_nud_normalized},
        delimited::parenthesized_nud_normalized,
        if_expr::if_nud_normalized,
        tails::{
            call_tail_normalized, colon_tail_normalized, dot_tail_normalized,
            index_tail_normalized, path_tail_normalized, with_tail_normalized,
        },
    },
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingView, OperatorUse, TokenKind},
        stops::Stops,
        yumark::FenceBoundary,
    },
    literal::{
        NormalizedRuleLiteralExit, NormalizedStringLiteralExit, rule_literal_normalized,
        string_literal_with_virtual_statements_normalized, string_mode_from_opener,
    },
    statement::{StatementLineHandoff, braced_nud_normalized},
};

use crate::{
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        expression_item::expression_item,
        observation::{
            indentation_after_newline, is_active_stop, is_contextual_word, is_line_stop, token_kind,
        },
        position::{advanced_origin, suffix_marker},
    },
};

#[cfg(test)]
use crate::{
    handoff::TailExit,
    lexical::{current_item::current_item, expression_item::scan_expression_literal_payload},
};

#[cfg(test)]
pub(crate) fn expr(i: SyntaxIn) -> Option<TailExit> {
    expr_normalized(
        i,
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .map(ordinary_exit)
}

#[cfg(test)]
pub(crate) fn expr_normalized(
    mut i: SyntaxIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> Option<NormalizedExit> {
    let (nud, item_origin, line_entry) =
        optional_nud_item(i.rb(), item_origin, line_entry, fence, baseline, stops)?;
    Some(expr_from_nud_normalized(
        i,
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    ))
}

pub(crate) fn expr_from_nud_normalized(
    mut i: SyntaxIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = append_nud(
        i.rb(),
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
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
pub(super) fn append_nud(
    mut i: SyntaxIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if is_expression_rule_literal_opener(&nud) {
        return append_rule_literal_nud(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if let Some(mode) = string_mode_from_opener(&nud) {
        return append_string_literal_nud(
            i,
            nud,
            mode,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if is_contextual_word(i.rb(), &nud, "case") {
        return case_like_nud_normalized(
            i,
            CaseLikeFamily::Case,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if is_contextual_word(i.rb(), &nud, "catch") {
        return case_like_nud_normalized(
            i,
            CaseLikeFamily::Catch,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if is_contextual_word(i.rb(), &nud, "if") {
        return if_nud_normalized(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_identifier_core(&mut i, nud);
            scan_tail_after_accept_normalized(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        Some(TokenKind::Integer) => {
            emit_integer_core(&mut i, nud);
            scan_tail_after_accept_normalized(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        Some(TokenKind::LParen) => parenthesized_nud_normalized(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::LBrace) => braced_nud_normalized(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::Operator) => operator_nud(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        _ => unreachable!("the NUD scanner accepts only normal core items and `(`"),
    }
}

#[allow(clippy::too_many_arguments)]
fn append_string_literal_nud(
    mut i: SyntaxIn,
    opener: Item,
    mode: crate::literal::StringMode,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = string_literal_with_virtual_statements_normalized(
        i.rb(),
        opener,
        mode,
        item_origin,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedStringLiteralExit::Complete(line_entry) => scan_tail_after_accept_normalized(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        NormalizedStringLiteralExit::Boundary(item, line_entry) => {
            complete(handoff(item), line_entry)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn append_rule_literal_nud(
    mut i: SyntaxIn,
    opener: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = rule_literal_normalized(
        i.rb(),
        opener,
        item_origin,
        LineEntry::InLine,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedRuleLiteralExit::Complete(line_entry) => scan_tail_after_accept_normalized(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        NormalizedRuleLiteralExit::Boundary(item, line_entry) => {
            complete(handoff(item), line_entry)
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn scan_tail_after_accept_normalized(
    mut i: SyntaxIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Led,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    tail_normalized(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn continue_normalized_tail(
    i: SyntaxIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => scan_tail_after_accept_normalized(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => tail_normalized(
            i,
            item,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn tail_normalized(
    mut i: SyntaxIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if is_active_stop(i.rb(), &item, stops) || is_line_stop(&item, stops) {
        return complete(handoff(item), line_entry);
    }
    let assignment = token_kind(&item) == Some(TokenKind::Equals);
    let annotation = is_contextual_word(i.rb(), &item, "as");
    if assignment || annotation {
        if threshold.is_some()
            || matches!(ml_mode, MlMode::None)
            || !chain_continuation(item.leading_view(), baseline)
        {
            return complete(handoff(item), line_entry);
        }
        if assignment {
            return super::tails::assignment_tail_normalized(
                i,
                item,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        if annotation {
            return super::tails::type_annotation_tail_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
    }
    if is_with_tail_item(i.rb(), &item, baseline, ml_mode) {
        return with_tail_normalized(
            i,
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
    if item.leading_view().is_grammar_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => {
                return call_tail_normalized(
                    i,
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                    sequence,
                );
            }
            Some(TokenKind::LBracket) => {
                return index_tail_normalized(
                    i,
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                    sequence,
                );
            }
            _ => {}
        }
    }
    match token_kind(&item) {
        Some(TokenKind::Dot) => {
            return dot_tail_normalized(
                i,
                item,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        Some(TokenKind::PathSeparator) => {
            return path_tail_normalized(
                i,
                item,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        Some(TokenKind::Operator) if is_led_operator(&item) => {
            return operator_tail(
                i,
                item,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
        _ => {}
    }
    if is_ml_argument(&item, baseline, ml_mode) {
        return ml_argument(
            i,
            item,
            threshold,
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
    if token_kind(&item) == Some(TokenKind::Colon) {
        return colon_tail_normalized(
            i,
            item,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    complete(handoff(item), line_entry)
}

fn is_with_tail_item(mut i: SyntaxIn, item: &Item, baseline: usize, ml_mode: MlMode) -> bool {
    !matches!(ml_mode, MlMode::None)
        && chain_continuation(item.leading_view(), baseline)
        && is_contextual_word(i.rb(), item, "with")
}

fn is_ml_argument(item: &Item, baseline: usize, mode: MlMode) -> bool {
    if !is_nud_item(item) || item.leading_view().is_grammar_empty() || matches!(mode, MlMode::None)
    {
        return false;
    }
    let indentation = indentation_after_newline(item.leading_view());
    match mode {
        MlMode::All => indentation.is_none_or(|indentation| indentation > baseline),
        MlMode::LayoutOnly => indentation.is_some_and(|indentation| indentation > baseline),
        MlMode::None => false,
    }
}

pub(crate) fn chain_continuation(leading: LeadingView<'_>, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

pub(crate) fn is_led_operator(item: &Item) -> bool {
    matches!(
        operator_use(item),
        Some(OperatorUse::Infix { .. } | OperatorUse::Suffix(_))
    )
}

#[allow(clippy::too_many_arguments)]
fn ml_argument(
    mut i: SyntaxIn,
    argument: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::MlArgument.into());
    let entry = suffix_marker(i.rb());
    let exit = expr_from_nud_normalized(
        i.rb(),
        argument,
        threshold,
        baseline,
        stops,
        MlMode::None,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    let child_origin = advanced_origin(item_origin, entry, i.rb());
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
        exit,
        child_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn operator_nud(
    mut i: SyntaxIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let entry = suffix_marker(i.rb());
            let rhs = required_expr_after_accept_normalized(
                i.rb(),
                Some(&right),
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            continue_normalized_tail(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                item_origin,
                fence,
                ambient,
                sequence,
            )
        }
        Some(OperatorUse::Nullfix) => {
            emit_operator_use(&mut i, operator, SyntaxKind::NullfixOperatorUse);
            scan_tail_after_accept_normalized(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        _ => unreachable!("the NUD scanner accepts only prefix and nullfix operators"),
    }
}

#[allow(clippy::too_many_arguments)]
fn operator_tail(
    mut i: SyntaxIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return complete(handoff(operator), line_entry);
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let entry = suffix_marker(i.rb());
            let rhs = required_expr_after_accept_normalized(
                i.rb(),
                Some(&right),
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            continue_normalized_tail(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                item_origin,
                fence,
                ambient,
                sequence,
            )
        }
        Some(OperatorUse::Suffix(left)) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return complete(handoff(operator), line_entry);
            }
            emit_operator_use(&mut i, operator, SyntaxKind::SuffixOperatorUse);
            scan_tail_after_accept_normalized(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        _ => unreachable!("the LED scanner accepts only infix and suffix operators"),
    }
}

#[cfg(test)]
fn optional_nud_item(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
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
            |mut lex, leading, origin, fence, _| {
                scan_expression_literal_payload(lex.rb(), OperatorSite::Nud)
                    .or_else(|| scan_nud_payload(lex, leading, origin, fence, baseline, stops))
            },
        )?;
        let payload = current.item.payload_view();
        if payload.is_boundary() || payload.is_eof() || !is_nud_item(&current.item) {
            return None;
        }
        Some(current)
    })?;
    let item_origin = advanced_origin(item_origin, entry, i);
    Some((item, item_origin, next_line_entry))
}

pub(crate) fn is_nud_item(item: &Item) -> bool {
    is_statement_nud(item)
        || matches!(
            operator_use(item),
            Some(OperatorUse::Prefix(_) | OperatorUse::Nullfix)
        )
}

fn is_statement_nud(item: &Item) -> bool {
    is_normal_core_item(item)
        || token_kind(item) == Some(TokenKind::LBrace)
        || string_mode_from_opener(item).is_some()
        || is_expression_rule_literal_opener(item)
}

fn is_expression_rule_literal_opener(item: &Item) -> bool {
    item.payload_view().spelling() == Some("~\"")
}

fn is_normal_core_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::Integer | TokenKind::LParen)
    )
}

fn operator_use(item: &Item) -> Option<&OperatorUse> {
    item.payload_view().operator_use()
}

#[cfg(test)]
use crate::handoff::ordinary_exit;
