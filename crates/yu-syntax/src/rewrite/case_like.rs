//! Direct ownership for the paired NUD `case` and `catch` expressions.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    driver::{
        Either, MlMode, TailExit, continue_completed_tail, expr_from_nud, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_contextual_word,
        is_line_stop, is_nud_item, is_separator, required_expr_item, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{
        introduced_body_indentation, pattern_nud_item_after_trivia,
        scan_apostrophe_sigil_identifier, scan_trivia, tail_item_after_trivia,
    },
    operator::{STOP_ARROW, STOP_COLON, STOP_COMMA, STOP_LBRACE, STOP_LINE_BREAK},
    pattern::{
        PATTERN_STOP_ARM_GUARD_IF, PATTERN_STOP_ARM_GUARD_WHERE,
        PATTERN_STOP_ARM_RECOVERY_SEPARATOR, PATTERN_STOP_ARROW, PATTERN_STOP_COMMA,
        PATTERN_STOP_RBRACE, PATTERN_STOP_RBRACKET, PATTERN_STOP_RPAREN, PATTERN_STOP_SEMICOLON,
        PatternStops, is_pattern_nud, pattern_from_entry_item, pattern_stops_from_owner,
    },
    statement::{StatementLineHandoff, indented_statement_block},
};

#[derive(Clone, Copy)]
pub(super) enum CaseLikeFamily {
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

pub(super) fn case_like_nud(
    mut i: RewriteIn,
    family: CaseLikeFamily,
    mut keyword: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    outer_stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(family.expression_node().into());
    emit_keyword(&mut i, keyword, family.keyword_node());
    let exit = case_like_head(i.rb(), family, baseline, outer_stops, line_handoff);
    i.state.finish_node();
    continue_completed_tail(
        i,
        threshold,
        baseline,
        outer_stops,
        ml_mode,
        line_handoff,
        exit,
    )
}

fn case_like_head(
    mut i: RewriteIn,
    family: CaseLikeFamily,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &leading);
    if let Some(label) = i.token(scan_apostrophe_sigil_identifier) {
        i.state.start_node(family.label_node().into());
        emit_token_item(
            &mut i,
            Item::plain(LeadingTrivia::default(), Payload::Token(label)),
        );
        i.state.finish_node();
        let leading = scan_trivia(i.rb());
        emit_leading_trivia(&mut i, &leading);
    }

    let scrutinee_stops = outer_stops | STOP_COLON | family.scrutinee_extra_stops();
    let item = tail_item_after_trivia(
        i.rb(),
        LeadingTrivia::default(),
        OperatorSite::Nud,
        baseline,
        scrutinee_stops,
    );
    i.state.start_node(family.scrutinee_node().into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item(
        i.rb(),
        item,
        None,
        baseline,
        scrutinee_stops,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    i.state.finish_node();

    match exit {
        Err(Either::Left(introducer)) if token_kind(&introducer) == Some(TokenKind::Colon) => {
            colon_block(i, family, introducer, baseline, outer_stops, line_handoff)
        }
        Err(Either::Left(open))
            if matches!(family, CaseLikeFamily::Catch)
                && token_kind(&open) == Some(TokenKind::LBrace) =>
        {
            catch_braced_block(i, open, baseline, outer_stops)
        }
        exit => missing_block(i, family, exit),
    }
}

fn colon_block(
    mut i: RewriteIn,
    family: CaseLikeFamily,
    colon: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(family.block_node().into());
    emit_token_item(&mut i, colon);
    let indentation = introduced_body_indentation(i.rb());
    let exit = match indentation {
        None => {
            let policy = match family {
                CaseLikeFamily::Case => ArmSequencePolicy::CaseInline,
                CaseLikeFamily::Catch => ArmSequencePolicy::CatchInline,
            };
            arm_sequence(i.rb(), policy, baseline, outer_stops, line_handoff)
        }
        Some(arm_indent) if arm_indent > baseline => arm_sequence(
            i.rb(),
            ArmSequencePolicy::Indented { family, arm_indent },
            baseline,
            outer_stops,
            line_handoff,
        ),
        Some(_) => wrong_indent_block(i.rb(), family),
    };
    i.state.finish_node();
    exit
}

fn wrong_indent_block(mut i: RewriteIn, family: CaseLikeFamily) -> TailExit {
    let item = scan_arm_item(i.rb(), 0);
    i.state.start_node(family.arm_node().into());
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    handoff(item)
}

fn catch_braced_block(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    outer_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::CatchBlock.into());
    emit_token_item(&mut i, open);
    let opening = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &opening);
    let exit = arm_sequence(
        i.rb(),
        ArmSequencePolicy::CatchBraced { baseline },
        baseline,
        outer_stops,
        StatementLineHandoff::CatchBracedArm,
    );
    i.state.finish_node();
    exit
}

fn missing_block(mut i: RewriteIn, family: CaseLikeFamily, exit: TailExit) -> TailExit {
    i.state.start_node(family.block_node().into());
    let exit = match exit {
        Err(Either::Left(mut item)) => {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            handoff(item)
        }
        Err(Either::Right(mut end)) => {
            end.item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            Err(Either::Right(end))
        }
        Ok(()) => unreachable!("a direct scrutinee always leaves a boundary item"),
    };
    i.state.finish_node();
    exit
}

fn arm_sequence(
    mut i: RewriteIn,
    policy: ArmSequencePolicy,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let first_stops = policy.first_pattern_stops(outer_stops);
    let mut item = scan_arm_item(i.rb(), first_stops);
    loop {
        if policy.accepts_arm_entry(i.rb(), &item, outer_stops) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        let exit = arm(
            i.rb(),
            policy.family(),
            item,
            policy.arm_baseline(baseline),
            policy.body_stops(),
            first_stops,
            outer_stops,
            line_handoff,
        );
        let next = match exit {
            Err(Either::Left(next)) => next,
            Err(Either::Right(mut end))
                if matches!(policy, ArmSequencePolicy::CatchBraced { .. }) =>
            {
                end.item.emit_all_remaining_leading(&mut *i.state);
                emit_missing(&mut i, LeadingTrivia::default());
                return Err(Either::Right(end));
            }
            exit => return exit,
        };
        item = match policy.successor(i.rb(), next, first_stops, outer_stops) {
            Ok(item) => item,
            Err(exit) => return exit,
        };
    }
}

fn arm(
    mut i: RewriteIn,
    family: CaseLikeFamily,
    item: Item,
    arm_baseline: usize,
    body_stops: Stops,
    first_stops: PatternStops,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(family.arm_node().into());
    let exit = pattern_from_entry_item(i.rb(), item, arm_baseline, first_stops, line_handoff);
    let item = match arm_successor(i.rb(), exit, first_stops) {
        Ok(item) => item,
        Err(exit) => return finish_absent_arm(i, exit),
    };

    let item =
        if matches!(family, CaseLikeFamily::Catch) && token_kind(&item) == Some(TokenKind::Comma) {
            let mut comma = item;
            comma.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, comma);
            let handler_stops = family.handler_pattern_stops(outer_stops);
            let handler = scan_arm_item(i.rb(), handler_stops);
            let exit =
                pattern_from_entry_item(i.rb(), handler, arm_baseline, handler_stops, line_handoff);
            match arm_successor(i.rb(), exit, first_stops) {
                Ok(item) => item,
                Err(exit) => return finish_absent_arm(i, exit),
            }
        } else {
            item
        };

    let item = if let Some(kind) = guard_kind(i.rb(), &item) {
        guard(
            i.rb(),
            family,
            item,
            arm_baseline,
            outer_stops,
            kind,
            line_handoff,
        )
    } else {
        Ok(item)
    };
    let item = match item {
        Ok(item) => item,
        Err(exit) => return finish_absent_arm(i, exit),
    };

    let exit = if token_kind(&item) == Some(TokenKind::Arrow) {
        let mut arrow = item;
        let arrow_baseline =
            indentation_after_newline(arrow.leading_view()).unwrap_or(arm_baseline);
        arrow.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, arrow);
        arm_body(
            i.rb(),
            arrow_baseline,
            body_stops | outer_stops,
            line_handoff,
        )
    } else {
        missing_arrow_then_body(
            i.rb(),
            item,
            arm_baseline,
            body_stops | outer_stops,
            line_handoff,
        )
    };
    let exit = arm_terminal(i.rb(), exit, first_stops);
    i.state.finish_node();
    exit
}

fn finish_absent_arm(mut i: RewriteIn, exit: TailExit) -> TailExit {
    emit_missing(&mut i, LeadingTrivia::default());
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    exit
}

fn arm_successor(
    i: RewriteIn,
    exit: TailExit,
    first_stops: PatternStops,
) -> Result<Item, TailExit> {
    match exit {
        Ok(()) => Ok(scan_arm_item(i, first_stops)),
        Err(Either::Left(item)) => Ok(item),
        Err(Either::Right(end)) => Err(Err(Either::Right(end))),
    }
}

fn guard(
    mut i: RewriteIn,
    family: CaseLikeFamily,
    mut keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    kind: SyntaxKind,
    line_handoff: StatementLineHandoff,
) -> Result<Item, TailExit> {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(family.guard_node().into());
    emit_keyword(&mut i, keyword, kind);
    let leading = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &leading);
    let item = tail_item_after_trivia(
        i.rb(),
        LeadingTrivia::default(),
        OperatorSite::Nud,
        baseline,
        outer_stops | STOP_ARROW,
    );
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item(
        i.rb(),
        item,
        None,
        baseline,
        outer_stops | STOP_ARROW,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    i.state.finish_node();
    arm_successor(i, exit, 0)
}

fn missing_arrow_then_body(
    mut i: RewriteIn,
    mut item: Item,
    arm_baseline: usize,
    body_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if !implicit_delimited_newline(arm_baseline, item.leading_view()) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    arm_inline_body_item(i, item, arm_baseline, body_stops, line_handoff)
}

fn arm_body(
    mut i: RewriteIn,
    arrow_baseline: usize,
    body_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if introduced_body_indentation(i.rb()).is_some_and(|indentation| indentation > arrow_baseline) {
        indented_statement_block(i, arrow_baseline, body_stops)
    } else {
        let leading = scan_trivia(i.rb());
        let item = tail_item_after_trivia(
            i.rb(),
            leading,
            OperatorSite::Nud,
            arrow_baseline,
            body_stops,
        );
        arm_inline_body_item(i, item, arrow_baseline, body_stops, line_handoff)
    }
}

fn arm_inline_body_item(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if arm_body_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if is_nud_item(&item) {
        return expr_from_nud(i, item, None, baseline, stops, MlMode::All, line_handoff);
    }

    item = retry_arm_body(i.rb(), item, baseline, stops);
    if arm_body_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    debug_assert!(is_nud_item(&item));
    expr_from_nud(i, item, None, baseline, stops, MlMode::All, line_handoff)
}

fn retry_arm_body(mut i: RewriteIn, mut item: Item, baseline: usize, stops: Stops) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
        if arm_body_boundary(i.rb(), &item, baseline, stops) || is_nud_item(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn arm_body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn arm_terminal(mut i: RewriteIn, exit: TailExit, first_stops: PatternStops) -> TailExit {
    let Err(Either::Left(semicolon)) = exit else {
        return exit;
    };
    if token_kind(&semicolon) != Some(TokenKind::Semicolon) {
        return handoff(semicolon);
    }
    emit_token_item(&mut i, semicolon);
    handoff(scan_arm_item(i, first_stops))
}

fn scan_arm_item(mut i: RewriteIn, stops: PatternStops) -> Item {
    let leading = scan_trivia(i.rb());
    pattern_nud_item_after_trivia(i, leading, stops)
}

fn guard_kind(mut i: RewriteIn, item: &Item) -> Option<SyntaxKind> {
    if is_contextual_word(i.rb(), item, "if") {
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
                STOP_COMMA | STOP_LINE_BREAK | super::operator::stops_for(TokenKind::RBrace)
            }
        }
    }

    fn successor(
        self,
        i: RewriteIn,
        item: Item,
        first_stops: PatternStops,
        outer_stops: Stops,
    ) -> Result<Item, TailExit> {
        match self {
            Self::CatchInline => Err(handoff(item)),
            Self::CaseInline => inline_successor(i, self, item, first_stops, outer_stops),
            Self::Indented { arm_indent, .. } => {
                indented_successor(i, self, item, arm_indent, first_stops, outer_stops)
            }
            Self::CatchBraced { .. } => braced_successor(i, self, item, first_stops, outer_stops),
        }
    }

    fn accepts_arm_entry(self, mut i: RewriteIn, item: &Item, outer_stops: Stops) -> bool {
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

    fn boundary_after_separator(self, mut i: RewriteIn, item: &Item, outer_stops: Stops) -> bool {
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

fn inline_successor(
    mut i: RewriteIn,
    policy: ArmSequencePolicy,
    item: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
) -> Result<Item, TailExit> {
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor(i, policy, item, first_stops, outer_stops);
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops)
        || indentation_after_newline(item.leading_view()).is_some()
    {
        return Err(handoff(item));
    }
    if is_pattern_nud(&item, first_stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(item);
    }
    Err(handoff(item))
}

fn indented_successor(
    mut i: RewriteIn,
    policy: ArmSequencePolicy,
    item: Item,
    arm_indent: usize,
    first_stops: PatternStops,
    outer_stops: Stops,
) -> Result<Item, TailExit> {
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor(i, policy, item, first_stops, outer_stops);
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops) {
        return Err(handoff(item));
    }
    if indentation_after_newline(item.leading_view()) == Some(arm_indent)
        && is_pattern_nud(&item, first_stops)
    {
        return Ok(item);
    }
    Err(handoff(item))
}

fn braced_successor(
    mut i: RewriteIn,
    policy: ArmSequencePolicy,
    item: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
) -> Result<Item, TailExit> {
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return Err(Ok(()));
    }
    if item.payload_view().is_eof() {
        let mut item = item;
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(handoff(item));
    }
    if token_kind(&item) == Some(TokenKind::Comma) {
        return separator_successor(i, policy, item, first_stops, outer_stops);
    }
    if sequence_outer_boundary(i.rb(), &item, outer_stops) {
        return Err(handoff(item));
    }
    if indentation_after_newline(item.leading_view()).is_some()
        && is_pattern_nud(&item, first_stops)
    {
        return Ok(item);
    }
    if is_pattern_nud(&item, first_stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(item);
    }
    Err(handoff(item))
}

fn separator_successor(
    mut i: RewriteIn,
    policy: ArmSequencePolicy,
    separator: Item,
    first_stops: PatternStops,
    outer_stops: Stops,
) -> Result<Item, TailExit> {
    i.state.start_node(policy.family().separator_node().into());
    emit_token_item(&mut i, separator);
    let item = scan_arm_item(i.rb(), first_stops);
    i.state.finish_node();
    if policy.boundary_after_separator(i.rb(), &item, outer_stops) {
        return Err(handoff(item));
    }
    Ok(item)
}

fn sequence_outer_boundary(i: RewriteIn, item: &Item, outer_stops: Stops) -> bool {
    item.payload_view().is_eof()
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

fn emit_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
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
