//! Direct ownership for the paired NUD `case` and `catch` expressions.

use crate::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    lexical::operator_scan::OperatorSite,
    operator_table::BindingPower,
    recovery_record::{
        CaseLikeRole, ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{emit_missing, emit_recovery_missing, emit_token_item},
    },
    cursor::SyntaxIn,
    expression::{
        continue_normalized_tail, expr_from_nud_normalized, is_nud_item,
        required_expr_item_normalized,
    },
    handoff::{Either, MlMode, NormalizedExit, TailExit, complete, handoff},
    lexical::{
        current_item::{CurrentItem, LineEntry, current_item},
        expression_item::expression_item,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_case_label_payload,
            scan_expression_payload, scan_pattern_nud_payload,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop,
            is_contextual_word, is_line_stop, is_separator, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_ARROW, STOP_COLON, STOP_COMMA, STOP_LBRACE, STOP_LINE_BREAK, Stops},
        yumark::FenceBoundary,
    },
    pattern::{
        PATTERN_STOP_ARM_GUARD_IF, PATTERN_STOP_ARM_GUARD_WHERE,
        PATTERN_STOP_ARM_RECOVERY_SEPARATOR, PATTERN_STOP_ARROW, PATTERN_STOP_COMMA,
        PATTERN_STOP_RBRACE, PATTERN_STOP_RBRACKET, PATTERN_STOP_RPAREN, PATTERN_STOP_SEMICOLON,
        PatternStops, is_pattern_nud, pattern_from_entry_item_normalized, pattern_stops_from_owner,
    },
    statement::{StatementLineHandoff, indented_statement_block_normalized},
};

#[derive(Clone, Copy)]
pub(crate) enum CaseLikeFamily {
    Case,
    Catch,
}

#[derive(Clone, Copy)]
enum ArmSequencePolicy {
    CaseInline,
    CatchInline,
    Indented {
        family: CaseLikeFamily,
        arm_indent: usize,
    },
    CatchBraced {
        baseline: usize,
    },
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn case_like_nud_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    mut keyword: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    outer_stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(family.expression_node().into());
    emit_keyword(&mut i, keyword, family.keyword_node());
    let entry = suffix_marker(i.rb());
    let exit = case_like_head_normalized(
        i.rb(),
        family,
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        outer_stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn case_like_head_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let scrutinee_stops = outer_stops | STOP_COLON | family.scrutinee_extra_stops();
    let (mut item, next_origin, next_line_entry) = case_head_item(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        scrutinee_stops,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    if item.payload_view().token_kind() == Some(TokenKind::SigilIdentifier) {
        item.emit_all_remaining_leading(&mut *i.state);
        i.state.start_node(family.label_node().into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            scrutinee_stops,
        );
    }

    i.state.start_node(family.scrutinee_node().into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let entry = suffix_marker(i.rb());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::CaseLike(CaseLikeRole::Scrutinee),
        None,
        baseline,
        scrutinee_stops,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    i.state.finish_node();

    match exit {
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            complete(
                missing_block(i, family, handoff(item), item_origin),
                line_entry,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(introducer)), line_entry)
            if token_kind(&introducer) == Some(TokenKind::Colon) =>
        {
            colon_block_normalized(
                i,
                family,
                introducer,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(open)), line_entry)
            if matches!(family, CaseLikeFamily::Catch)
                && token_kind(&open) == Some(TokenKind::LBrace) =>
        {
            catch_braced_block_normalized(
                i,
                open,
                baseline,
                outer_stops,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        NormalizedExit::Complete(exit, line_entry) => {
            complete(missing_block(i, family, exit, item_origin), line_entry)
        }
    }
}

fn case_head_item(
    mut i: SyntaxIn,
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
                    scan_case_label_payload(lex.rb()).or_else(|| {
                        scan_expression_payload(
                            lex,
                            OperatorSite::Nud,
                            leading,
                            origin,
                            fence,
                            baseline,
                            stops,
                        )
                    })
                },
            )
        })
        .expect("case-like head payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}

#[allow(clippy::too_many_arguments)]
fn colon_block_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    colon: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(family.block_node().into());
    emit_token_item(&mut i, colon);
    let indentation = introduced_body_indentation_normalized(i.rb(), item_origin, fence);
    let exit = match indentation {
        None => {
            let policy = match family {
                CaseLikeFamily::Case => ArmSequencePolicy::CaseInline,
                CaseLikeFamily::Catch => ArmSequencePolicy::CatchInline,
            };
            arm_sequence_normalized(
                i.rb(),
                policy,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        Some(arm_indent) if arm_indent > baseline => arm_sequence_normalized(
            i.rb(),
            ArmSequencePolicy::Indented { family, arm_indent },
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => wrong_indent_block_normalized(i.rb(), family, item_origin, line_entry, fence),
    };
    i.state.finish_node();
    exit
}

fn wrong_indent_block_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        pattern_item_normalized(i.rb(), item_origin, line_entry, fence, 0);
    i.state.start_node(family.arm_node().into());
    emit_structural_missing(i.rb(), CaseLikeRole::Arm, &item, item_origin);
    i.state.finish_node();
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn catch_braced_block_normalized(
    mut i: SyntaxIn,
    open: Item,
    baseline: usize,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let ambient = ambient.map(AmbientClaimView::braced);
    i.state.start_node(SyntaxKind::CatchBlock.into());
    emit_token_item(&mut i, open);
    let exit = arm_sequence_normalized(
        i.rb(),
        ArmSequencePolicy::CatchBraced { baseline },
        baseline,
        outer_stops,
        StatementLineHandoff::CatchBracedArm,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

fn missing_block(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    exit: TailExit,
    item_origin: usize,
) -> TailExit {
    i.state.start_node(family.block_node().into());
    let exit = match exit {
        Err(Either::Left(mut item)) => {
            if !item.payload_view().is_boundary()
                && !matches!(
                    token_kind(&item),
                    Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                )
                && !item.leading_view().has_ordinary_newline()
            {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            emit_structural_missing(i.rb(), CaseLikeRole::Block, &item, item_origin);
            handoff(item)
        }
        Err(Either::Right(mut end)) => {
            end.item.emit_all_remaining_leading(&mut *i.state);
            emit_structural_missing(i.rb(), CaseLikeRole::Block, &end.item, item_origin);
            Err(Either::Right(end))
        }
        Ok(()) => unreachable!("a direct scrutinee always leaves a boundary item"),
    };
    i.state.finish_node();
    exit
}

fn emit_structural_missing(i: SyntaxIn, role: CaseLikeRole, item: &Item, item_origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    let expected = match role {
        CaseLikeRole::Block => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        CaseLikeRole::Arm => ExpectedSyntax::Pattern,
        _ => unreachable!("only structural CaseLike slots publish here"),
    };
    let role = GrammarRole::CaseLike(role);
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        RecoveryDraft::new(
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
}

#[allow(clippy::too_many_arguments)]
fn arm_sequence_normalized(
    mut i: SyntaxIn,
    policy: ArmSequencePolicy,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let first_stops = policy.first_pattern_stops(outer_stops);
    let sequence = Some(match policy {
        ArmSequencePolicy::CaseInline => crate::sequence::SequenceOwner::CaseInline,
        ArmSequencePolicy::CatchInline => crate::sequence::SequenceOwner::CatchInline,
        ArmSequencePolicy::Indented {
            family: CaseLikeFamily::Case,
            ..
        } => crate::sequence::SequenceOwner::CaseIndented,
        ArmSequencePolicy::Indented {
            family: CaseLikeFamily::Catch,
            ..
        } => crate::sequence::SequenceOwner::CatchIndented,
        ArmSequencePolicy::CatchBraced { .. } => crate::sequence::SequenceOwner::CatchBraced,
    });
    let (mut item, next_origin, next_line_entry) =
        pattern_item_normalized(i.rb(), item_origin, line_entry, fence, first_stops);
    item_origin = next_origin;
    line_entry = next_line_entry;
    loop {
        if policy.accepts_arm_entry(i.rb(), &item, outer_stops) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        let entry = suffix_marker(i.rb());
        let exit = arm_normalized(
            i.rb(),
            policy.family(),
            item,
            policy.arm_baseline(baseline),
            policy.body_stops(),
            first_stops,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        let next = match exit {
            NormalizedExit::Deferred(item, line_entry) => {
                return NormalizedExit::Deferred(item, line_entry);
            }
            NormalizedExit::Complete(Err(Either::Left(next)), next_line_entry) => {
                line_entry = next_line_entry;
                next
            }
            NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry)
                if matches!(policy, ArmSequencePolicy::CatchBraced { .. }) =>
            {
                end.item.emit_all_remaining_leading(&mut *i.state);
                emit_missing(&mut i, LeadingTrivia::default());
                return complete(Err(Either::Right(end)), line_entry);
            }
            exit => return exit,
        };
        let entry = suffix_marker(i.rb());
        (item, line_entry) = match policy.successor_normalized(
            i.rb(),
            next,
            first_stops,
            outer_stops,
            item_origin,
            line_entry,
            fence,
        ) {
            Ok(item) => item,
            Err(exit) => return exit,
        };
        item_origin = advanced_origin(item_origin, entry, i.rb());
    }
}

#[allow(clippy::too_many_arguments)]
fn arm_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    item: Item,
    arm_baseline: usize,
    body_stops: Stops,
    first_stops: PatternStops,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(family.arm_node().into());
    let entry = suffix_marker(i.rb());
    let exit = pattern_from_entry_item_normalized(
        i.rb(),
        item,
        CaseLikeRole::Pattern,
        arm_baseline,
        first_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let item =
        match arm_successor_normalized(i.rb(), exit, first_stops, item_origin, line_entry, fence) {
            Ok(item) => item,
            Err(exit) => return finish_absent_arm_normalized(i, exit),
        };
    item_origin = item.1;
    line_entry = item.2;
    let item = item.0;

    if item.payload_view().is_boundary() {
        return finish_absent_arm_normalized(i, complete(handoff(item), line_entry));
    }

    let item = if matches!(family, CaseLikeFamily::Catch)
        && token_kind(&item) == Some(TokenKind::Comma)
    {
        let mut comma = item;
        comma.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, comma);
        let handler_stops = family.handler_pattern_stops(outer_stops);
        let (handler, next_origin, next_line_entry) =
            pattern_item_normalized(i.rb(), item_origin, line_entry, fence, handler_stops);
        item_origin = next_origin;
        line_entry = next_line_entry;
        let entry = suffix_marker(i.rb());
        let exit = pattern_from_entry_item_normalized(
            i.rb(),
            handler,
            CaseLikeRole::Handler,
            arm_baseline,
            handler_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        match arm_successor_normalized(i.rb(), exit, first_stops, item_origin, line_entry, fence) {
            Ok((item, next_origin, next_line_entry)) => {
                item_origin = next_origin;
                line_entry = next_line_entry;
                item
            }
            Err(exit) => return finish_absent_arm_normalized(i, exit),
        }
    } else {
        item
    };

    let item = if let Some(kind) = guard_kind(i.rb(), &item) {
        guard_normalized(
            i.rb(),
            family,
            item,
            arm_baseline,
            outer_stops,
            kind,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        Ok((item, item_origin, line_entry))
    };
    let item = match item {
        Ok((item, next_origin, next_line_entry)) => {
            item_origin = next_origin;
            line_entry = next_line_entry;
            item
        }
        Err(exit) => return finish_absent_arm_normalized(i, exit),
    };

    let entry = suffix_marker(i.rb());
    let exit = if item.payload_view().is_boundary() {
        missing_arrow_then_body_normalized(
            i.rb(),
            item,
            arm_baseline,
            body_stops | outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else if token_kind(&item) == Some(TokenKind::Arrow) {
        let mut arrow = item;
        let arrow_baseline =
            indentation_after_newline(arrow.leading_view()).unwrap_or(arm_baseline);
        arrow.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, arrow);
        arm_body_normalized(
            i.rb(),
            arrow_baseline,
            body_stops | outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        missing_arrow_then_body_normalized(
            i.rb(),
            item,
            arm_baseline,
            body_stops | outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    };
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let exit = arm_terminal_normalized(i.rb(), exit, first_stops, item_origin, fence);
    i.state.finish_node();
    exit
}

fn finish_absent_arm_normalized(mut i: SyntaxIn, exit: NormalizedExit) -> NormalizedExit {
    if matches!(exit, NormalizedExit::Deferred(..)) {
        i.state.finish_node();
        return exit;
    }
    emit_missing(&mut i, LeadingTrivia::default());
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    exit
}

fn arm_successor_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    first_stops: PatternStops,
    item_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            let (item, item_origin, line_entry) =
                pattern_item_normalized(i.rb(), item_origin, line_entry, fence, first_stops);
            Ok((item, item_origin, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            Ok((item, item_origin, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            Err(complete(Err(Either::Right(end)), line_entry))
        }
        NormalizedExit::Deferred(item, line_entry) => {
            Err(NormalizedExit::Deferred(item, line_entry))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn guard_normalized(
    mut i: SyntaxIn,
    family: CaseLikeFamily,
    mut keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    kind: SyntaxKind,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(family.guard_node().into());
    emit_keyword(&mut i, keyword, kind);
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        outer_stops | STOP_ARROW,
    );
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let entry = suffix_marker(i.rb());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::CaseLike(CaseLikeRole::Guard),
        None,
        baseline,
        outer_stops | STOP_ARROW,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    i.state.finish_node();
    arm_successor_normalized(i, exit, 0, item_origin, line_entry, fence)
}

#[allow(clippy::too_many_arguments)]
fn missing_arrow_then_body_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    arm_baseline: usize,
    body_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if !implicit_delimited_newline(arm_baseline, item.leading_view()) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    arm_inline_body_item_normalized(
        i,
        item,
        arm_baseline,
        body_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn arm_body_normalized(
    mut i: SyntaxIn,
    arrow_baseline: usize,
    body_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if introduced_body_indentation_normalized(i.rb(), item_origin, fence)
        .is_some_and(|indentation| indentation > arrow_baseline)
    {
        indented_statement_block_normalized(
            i,
            arrow_baseline,
            crate::recovery_record::GrammarRole::ColonApplication(
                crate::recovery_record::ColonApplicationRole::IndentedStatement,
            ),
            body_stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        let (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            arrow_baseline,
            body_stops,
        );
        arm_inline_body_item_normalized(
            i,
            item,
            arrow_baseline,
            body_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn arm_inline_body_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if arm_body_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if is_nud_item(&item) {
        return expr_from_nud_normalized(
            i,
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

    (item, item_origin, line_entry) = retry_arm_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if arm_body_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    debug_assert!(is_nud_item(&item));
    expr_from_nud_normalized(
        i,
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
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_arm_body_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if item.payload_view().is_boundary()
            || arm_body_boundary(i.rb(), &item, baseline, stops)
            || is_nud_item(&item)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn arm_body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn arm_terminal_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    first_stops: PatternStops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let NormalizedExit::Complete(Err(Either::Left(semicolon)), line_entry) = exit else {
        return exit;
    };
    if semicolon.payload_view().is_boundary() {
        return complete(handoff(semicolon), line_entry);
    }
    if token_kind(&semicolon) != Some(TokenKind::Semicolon) {
        return complete(handoff(semicolon), line_entry);
    }
    emit_token_item(&mut i, semicolon);
    let (item, _, line_entry) =
        pattern_item_normalized(i, item_origin, line_entry, fence, first_stops);
    complete(handoff(item), line_entry)
}

fn guard_kind(mut i: SyntaxIn, item: &Item) -> Option<SyntaxKind> {
    if item.payload_view().is_boundary() {
        None
    } else if is_contextual_word(i.rb(), item, "if") {
        Some(SyntaxKind::IfKw)
    } else if is_contextual_word(i, item, "where") {
        Some(SyntaxKind::WhereKw)
    } else {
        None
    }
}

impl ArmSequencePolicy {
    fn family(self) -> CaseLikeFamily {
        match self {
            Self::CaseInline => CaseLikeFamily::Case,
            Self::CatchInline | Self::CatchBraced { .. } => CaseLikeFamily::Catch,
            Self::Indented { family, .. } => family,
        }
    }

    fn arm_baseline(self, default: usize) -> usize {
        match self {
            Self::Indented { arm_indent, .. } => arm_indent,
            Self::CatchBraced { baseline } => baseline,
            Self::CaseInline | Self::CatchInline => default,
        }
    }

    fn first_pattern_stops(self, outer_stops: Stops) -> PatternStops {
        let common = PATTERN_STOP_ARROW | PATTERN_STOP_ARM_GUARD_IF | PATTERN_STOP_ARM_GUARD_WHERE;
        match self.family() {
            CaseLikeFamily::Case => {
                common | PATTERN_STOP_ARM_RECOVERY_SEPARATOR | pattern_stops_from_owner(outer_stops)
            }
            CaseLikeFamily::Catch => {
                common | PATTERN_STOP_COMMA | pattern_stops_from_owner(outer_stops)
            }
        }
    }

    fn body_stops(self) -> Stops {
        match self {
            Self::CaseInline => STOP_COMMA | STOP_LINE_BREAK,
            Self::CatchInline => STOP_LINE_BREAK,
            Self::Indented { .. } => STOP_COMMA,
            Self::CatchBraced { .. } => {
                STOP_COMMA | STOP_LINE_BREAK | crate::lexical::stops::stops_for(TokenKind::RBrace)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn successor_normalized(
        self,
        i: SyntaxIn,
        item: Item,
        first_stops: PatternStops,
        outer_stops: Stops,
        item_origin: usize,
        line_entry: LineEntry,
        fence: Option<&FenceBoundary>,
    ) -> Result<(Item, LineEntry), NormalizedExit> {
        match self {
            Self::CatchInline => Err(complete(handoff(item), line_entry)),
            Self::CaseInline => inline_successor_normalized(
                i,
                self,
                item,
                first_stops,
                outer_stops,
                item_origin,
                line_entry,
                fence,
            ),
            Self::Indented { arm_indent, .. } => indented_successor_normalized(
                i,
                self,
                item,
                arm_indent,
                first_stops,
                outer_stops,
                item_origin,
                line_entry,
                fence,
            ),
            Self::CatchBraced { .. } => braced_successor_normalized(
                i,
                self,
                item,
                first_stops,
                outer_stops,
                item_origin,
                line_entry,
                fence,
            ),
        }
    }

    fn accepts_arm_entry(self, mut i: SyntaxIn, item: &Item, outer_stops: Stops) -> bool {
        if sequence_outer_boundary(i.rb(), item, outer_stops) {
            return false;
        }
        match self {
            Self::CaseInline | Self::CatchInline => {
                indentation_after_newline(item.leading_view()).is_none()
            }
            Self::Indented { arm_indent, .. } => indentation_after_newline(item.leading_view())
                .is_none_or(|indentation| indentation == arm_indent),
            Self::CatchBraced { .. } => true,
        }
    }

    fn boundary_after_separator(self, mut i: SyntaxIn, item: &Item, outer_stops: Stops) -> bool {
        if sequence_outer_boundary(i.rb(), item, outer_stops) {
            return true;
        }
        match self {
            Self::CaseInline => indentation_after_newline(item.leading_view()).is_some(),
            Self::CatchInline => true,
            Self::Indented { arm_indent, .. } => indentation_after_newline(item.leading_view())
                .is_some_and(|indentation| indentation != arm_indent),
            Self::CatchBraced { .. } => false,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_successor_normalized(
    mut i: SyntaxIn,
    policy: ArmSequencePolicy,
    item: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry), NormalizedExit> {
    if item.payload_view().is_boundary() {
        return Err(complete(handoff(item), line_entry));
    }
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor_normalized(
            i,
            policy,
            item,
            first_stops,
            outer_stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops)
        || indentation_after_newline(item.leading_view()).is_some()
    {
        return Err(complete(handoff(item), line_entry));
    }
    if is_pattern_nud(&item, first_stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok((item, line_entry));
    }
    Err(complete(handoff(item), line_entry))
}

#[allow(clippy::too_many_arguments)]
fn indented_successor_normalized(
    mut i: SyntaxIn,
    policy: ArmSequencePolicy,
    item: Item,
    arm_indent: usize,
    first_stops: PatternStops,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry), NormalizedExit> {
    if item.payload_view().is_boundary() {
        return Err(complete(handoff(item), line_entry));
    }
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor_normalized(
            i,
            policy,
            item,
            first_stops,
            outer_stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops) {
        return Err(complete(handoff(item), line_entry));
    }
    if indentation_after_newline(item.leading_view()) == Some(arm_indent)
        && is_pattern_nud(&item, first_stops)
    {
        return Ok((item, line_entry));
    }
    Err(complete(handoff(item), line_entry))
}

#[allow(clippy::too_many_arguments)]
fn braced_successor_normalized(
    mut i: SyntaxIn,
    policy: ArmSequencePolicy,
    item: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry), NormalizedExit> {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(item), line_entry));
    }
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return Err(complete(Ok(()), line_entry));
    }
    if item.payload_view().is_eof() {
        let mut item = item;
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(item), line_entry));
    }
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor_normalized(
            i,
            policy,
            item,
            first_stops,
            outer_stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops) {
        return Err(complete(handoff(item), line_entry));
    }
    if indentation_after_newline(item.leading_view()).is_some()
        && is_pattern_nud(&item, first_stops)
    {
        return Ok((item, line_entry));
    }
    if is_pattern_nud(&item, first_stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok((item, line_entry));
    }
    Err(complete(handoff(item), line_entry))
}

#[allow(clippy::too_many_arguments)]
fn separator_successor_normalized(
    mut i: SyntaxIn,
    policy: ArmSequencePolicy,
    separator: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry), NormalizedExit> {
    i.state.start_node(policy.family().separator_node().into());
    emit_token_item(&mut i, separator);
    let (item, _, line_entry) =
        pattern_item_normalized(i.rb(), item_origin, line_entry, fence, first_stops);
    i.state.finish_node();
    if item.payload_view().is_boundary() {
        return Err(complete(handoff(item), line_entry));
    }
    if policy.boundary_after_separator(i.rb(), &item, outer_stops) {
        return Err(complete(handoff(item), line_entry));
    }
    Ok((item, line_entry))
}

fn pattern_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: PatternStops,
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
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("Pattern payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}

fn sequence_outer_boundary(i: SyntaxIn, item: &Item, outer_stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
        || is_active_stop(i, item, outer_stops)
}

impl CaseLikeFamily {
    fn expression_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseExpression,
            Self::Catch => SyntaxKind::CatchExpression,
        }
    }

    fn keyword_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseKw,
            Self::Catch => SyntaxKind::CatchKw,
        }
    }

    fn label_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseLabel,
            Self::Catch => SyntaxKind::CatchLabel,
        }
    }

    fn scrutinee_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseScrutinee,
            Self::Catch => SyntaxKind::CatchScrutinee,
        }
    }

    fn block_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseBlock,
            Self::Catch => SyntaxKind::CatchBlock,
        }
    }

    fn arm_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseArm,
            Self::Catch => SyntaxKind::CatchArm,
        }
    }

    fn guard_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseGuard,
            Self::Catch => SyntaxKind::CatchGuard,
        }
    }

    fn separator_node(self) -> SyntaxKind {
        match self {
            Self::Case => SyntaxKind::CaseArmSeparator,
            Self::Catch => SyntaxKind::CatchArmSeparator,
        }
    }

    fn scrutinee_extra_stops(self) -> Stops {
        match self {
            Self::Case => 0,
            Self::Catch => STOP_LBRACE,
        }
    }

    fn handler_pattern_stops(self, outer_stops: Stops) -> PatternStops {
        match self {
            Self::Case => unreachable!("only Catch owns a handler Pattern"),
            Self::Catch => {
                PATTERN_STOP_ARROW
                    | PATTERN_STOP_ARM_GUARD_IF
                    | PATTERN_STOP_ARM_GUARD_WHERE
                    | PATTERN_STOP_RPAREN
                    | PATTERN_STOP_RBRACKET
                    | PATTERN_STOP_RBRACE
                    | PATTERN_STOP_SEMICOLON
                    | pattern_stops_from_owner(outer_stops)
            }
        }
    }
}

fn emit_keyword(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    let spelling = match kind {
        SyntaxKind::CaseKw => "case",
        SyntaxKind::CatchKw => "catch",
        SyntaxKind::IfKw => "if",
        SyntaxKind::WhereKw => "where",
        _ => unreachable!("case-like owners accept only their fixed words"),
    };
    debug_assert_eq!(item.payload_view().spelling(), Some(spelling));
    item.emit_remaining(&mut *i.state, kind);
}
