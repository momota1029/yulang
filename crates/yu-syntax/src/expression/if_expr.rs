//! Direct ownership for NUD `if` expressions and their arm boundaries.

use crate::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    lexical::operator_scan::OperatorSite,
    operator_table::BindingPower,
    recovery_record::{
        ExpectationSources, ExpectedSyntax, GrammarRole, IfExpressionRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    cursor::{LexIn, SyntaxIn},
    expression::{
        continue_normalized_tail, expr_from_nud_normalized, is_nud_item,
        is_required_operand_boundary, required_expr_item_normalized,
    },
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        expression_item::{expression_item, scan_expression_item_lexical},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::introduced_body_indentation_normalized,
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop_lex,
            is_contextual_word, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_COLON, STOP_ELSE, STOP_ELSIF, STOP_LBRACE, Stops},
        yumark::FenceBoundary,
    },
    statement::{StatementLineHandoff, indented_statement_block_normalized},
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn if_nud_normalized(
    mut i: SyntaxIn,
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
    let companion = ambient.view.map(|view| view.if_companion(baseline));
    let arm_ambient = ambient.map(|view| view.with_if(companion.as_ref().unwrap()));
    i.state.start_node(SyntaxKind::IfExpression.into());
    let entry = suffix_marker(i.rb());
    let exit = if_arm_normalized(
        i.rb(),
        keyword,
        SyntaxKind::IfKw,
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        arm_ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    let entry = suffix_marker(i.rb());
    let exit = if_continuations_normalized(
        i.rb(),
        exit,
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        fence,
        arm_ambient,
        ambient,
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
        ambient.if_outer_tail(),
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn if_continuations_normalized(
    mut i: SyntaxIn,
    mut exit: NormalizedExit,
    if_baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    fence: Option<&FenceBoundary>,
    arm_ambient: AmbientClaimContext<'_>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    loop {
        let NormalizedExit::Complete(Err(Either::Left(mut keyword)), line_entry) = exit else {
            return exit;
        };
        if keyword.payload_view().is_boundary() {
            return complete(handoff(keyword), line_entry);
        }
        let Some(kind) = arm_keyword(i.rb(), &keyword, if_baseline) else {
            return complete(handoff(keyword), line_entry);
        };
        keyword.emit_all_remaining_leading(&mut *i.state);
        let entry = suffix_marker(i.rb());
        exit = match kind {
            SyntaxKind::ElsifKw => if_arm_normalized(
                i.rb(),
                keyword,
                kind,
                if_baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                arm_ambient,
            ),
            SyntaxKind::ElseKw => else_arm_normalized(
                i.rb(),
                keyword,
                if_baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            _ => unreachable!("only if-continuation keyword kinds are selected"),
        };
        item_origin = advanced_origin(item_origin, entry, i.rb());
        if kind == SyntaxKind::ElseKw {
            return exit;
        }
    }
}

fn arm_keyword(i: SyntaxIn, item: &Item, if_baseline: usize) -> Option<SyntaxKind> {
    match active_statement_companion(i, item, if_baseline, STOP_ELSIF | STOP_ELSE) {
        Some(ActiveStatementCompanion::Elsif) => Some(SyntaxKind::ElsifKw),
        Some(ActiveStatementCompanion::Else) => Some(SyntaxKind::ElseKw),
        None => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ActiveStatementCompanion {
    Elsif,
    Else,
}

pub(crate) fn active_statement_companion(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> Option<ActiveStatementCompanion> {
    if item.payload_view().is_boundary() {
        return None;
    }
    let continuation = indentation_after_newline(item.leading_view())
        .is_none_or(|indentation| indentation >= baseline);
    continuation.then_some(())?;
    if stops & STOP_ELSIF != 0 && is_contextual_word(i.rb(), item, "elsif") {
        Some(ActiveStatementCompanion::Elsif)
    } else if stops & STOP_ELSE != 0 && is_contextual_word(i, item, "else") {
        Some(ActiveStatementCompanion::Else)
    } else {
        None
    }
}

#[allow(clippy::too_many_arguments)]
fn if_arm_normalized(
    mut i: SyntaxIn,
    keyword: Item,
    keyword_kind: SyntaxKind,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let sequence = Some(crate::sequence::SequenceOwner::If);
    i.state.start_node(SyntaxKind::IfArm.into());
    emit_contextual_keyword(&mut i, keyword, keyword_kind);

    let condition_stops = outer_stops | STOP_COLON | STOP_LBRACE | STOP_ELSIF | STOP_ELSE;
    let entry = suffix_marker(i.rb());
    let (exit, condition_missing) = condition_normalized(
        i.rb(),
        baseline,
        condition_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());

    let exit = match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            missing_if_arm_normalized(
                i.rb(),
                complete(handoff(item), line_entry),
                condition_missing,
                item_origin,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(colon)), line_entry)
            if token_kind(&colon) == Some(TokenKind::Colon) =>
        {
            emit_token_item(&mut i, colon);
            colon_body_normalized(
                i.rb(),
                InlineBodyRole::Body,
                baseline,
                outer_stops | STOP_ELSIF | STOP_ELSE,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        exit => missing_if_arm_normalized(i.rb(), exit, condition_missing, item_origin),
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn condition_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> (NormalizedExit, bool) {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let missing = is_required_operand_boundary(i.rb(), &item, stops);
    i.state.start_node(SyntaxKind::Condition.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::IfExpression(IfExpressionRole::Condition),
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
    i.state.finish_node();
    i.state.finish_node();
    (exit, missing)
}

fn missing_if_arm_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    condition_missing: bool,
    item_origin: usize,
) -> NormalizedExit {
    if condition_missing {
        return exit;
    }
    match exit {
        NormalizedExit::Complete(Err(Either::Left(mut item)), line_entry) => {
            if !item.payload_view().is_boundary() {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            emit_if_missing(i.rb(), &item, item_origin, IfExpressionRole::BodyIntroducer);
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            end.item.emit_all_remaining_leading(&mut *i.state);
            emit_if_missing(
                i.rb(),
                &end.item,
                item_origin,
                IfExpressionRole::BodyIntroducer,
            );
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("a direct condition always returns a boundary item")
        }
        deferred @ NormalizedExit::Deferred(..) => deferred,
    }
}

#[allow(clippy::too_many_arguments)]
fn else_arm_normalized(
    mut i: SyntaxIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let sequence = Some(crate::sequence::SequenceOwner::If);
    #[cfg(test)]
    ambient.observe(crate::ambient_claim::ProofSite::ElseBody);
    i.state.start_node(SyntaxKind::ElseArm.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::ElseKw);

    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        outer_stops,
    );
    if item.payload_view().is_boundary() {
        emit_if_missing(i.rb(), &item, item_origin, IfExpressionRole::ElseBody);
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let exit = if token_kind(&item) == Some(TokenKind::Colon) {
        emit_token_item(&mut i, item);
        colon_body_normalized(
            i.rb(),
            InlineBodyRole::ElseBody,
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        inline_body_item_normalized(
            i.rb(),
            item,
            InlineBodyRole::ElseBody,
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    };
    i.state.finish_node();
    exit
}

#[derive(Clone, Copy)]
enum InlineBodyRole {
    Body,
    ElseBody,
}

impl InlineBodyRole {
    fn recovery_role(self) -> IfExpressionRole {
        match self {
            Self::Body => IfExpressionRole::Body,
            Self::ElseBody => IfExpressionRole::ElseBody,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
    mut i: SyntaxIn,
    inline_role: InlineBodyRole,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if introduced_body_indentation_normalized(i.rb(), item_origin, fence)
        .is_some_and(|indentation| indentation > baseline)
    {
        indented_statement_block_normalized(
            i,
            baseline,
            GrammarRole::IfExpression(IfExpressionRole::IndentedStatement),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        inline_body_normalized(
            i,
            inline_role,
            baseline,
            stops,
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
fn inline_body_normalized(
    mut i: SyntaxIn,
    role: InlineBodyRole,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    inline_body_item_normalized(
        i,
        item,
        role,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_body_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    role: InlineBodyRole,
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
        emit_if_missing(i.rb(), &item, item_origin, role.recovery_role());
        return complete(handoff(item), line_entry);
    }
    if inline_boundary(i.rb(), &item, baseline, stops) {
        emit_inline_missing(&mut i, &mut item, baseline, item_origin, role);
        return complete(handoff(item), line_entry);
    }

    emit_inline_leading(&mut i, &mut item);
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

    (item, item_origin, line_entry) = retry_inline_body_normalized(
        i.rb(),
        item,
        role,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if inline_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            emit_inline_leading(&mut i, &mut item);
        }
        return complete(handoff(item), line_entry);
    }
    emit_inline_leading(&mut i, &mut item);
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
fn retry_inline_body_normalized(
    i: SyntaxIn,
    mut item: Item,
    role: InlineBodyRole,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind = match token_kind(&item).expect("inline Error owns a lexical Item") {
                    TokenKind::Operator => SyntaxKind::Operator,
                    kind => token_syntax_kind(kind),
                };
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    scan_expression_item_lexical(
                        lex,
                        OperatorSite::Nud,
                        item_origin,
                        line_entry,
                        fence,
                        baseline,
                        stops,
                    )
                });
                if item.payload_view().is_boundary()
                    || run.lexical(|lex| inline_boundary_lex(lex, &item, baseline, stops))
                    || is_nud_item(&item)
                {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| {
            if_recovery_draft(role.recovery_role(), RecoveryKind::Error, range, unexpected)
        },
    )
}

fn inline_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    i.token(|lex| Some(inline_boundary_lex(lex, item, baseline, stops)))
        .expect("inline boundary observation is total")
}

fn inline_boundary_lex(i: LexIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || crate::lexical::observation::is_separator(item)
        || is_active_stop_lex(i, item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
        || token_kind(item) == Some(TokenKind::LBrace)
}

fn emit_inline_leading(i: &mut SyntaxIn, item: &mut Item) {
    if !item.leading_view().is_grammar_empty() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

fn emit_inline_missing(
    i: &mut SyntaxIn,
    item: &mut Item,
    baseline: usize,
    item_origin: usize,
    role: InlineBodyRole,
) {
    if !implicit_delimited_newline(baseline, item.leading_view()) {
        emit_inline_leading(i, item);
    }
    emit_if_missing(i.rb(), item, item_origin, role.recovery_role());
}

fn emit_if_missing(i: SyntaxIn, item: &Item, item_origin: usize, role: IfExpressionRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        if_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn if_recovery_draft(
    role: IfExpressionRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = if role == IfExpressionRole::BodyIntroducer {
        ExpectedSyntax::Punctuation(crate::recovery_record::PunctuationEvidence::Colon)
    } else {
        ExpectedSyntax::Expression
    };
    let role = GrammarRole::IfExpression(role);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn emit_contextual_keyword(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    let spelling = match kind {
        SyntaxKind::IfKw => "if",
        SyntaxKind::ElsifKw => "elsif",
        SyntaxKind::ElseKw => "else",
        _ => unreachable!("only if-expression keyword kinds are emitted here"),
    };
    debug_assert_eq!(item.payload_view().spelling(), Some(spelling));
    item.emit_remaining(&mut *i.state, kind);
}
