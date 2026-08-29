use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum BindingStyleBodyLayout {
    Inline {
        trivia: TriviaRun,
    },
    Indented {
        opening_trivia: TriviaRun,
        block_indent: usize,
    },
    OuterBoundary,
}

/// The shared layout helper does not decide whether an owner-specific
/// malformed inline run is terminal.  Binding preserves its established
/// Missing-after-retry behavior; Cast uses the terminal variant to avoid
/// stacking a second Missing over its one Error episode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BindingStyleInlineRecovery {
    None,
    Retry,
    TerminalError,
}

/// Classifies the body after an already-committed `=`-style introducer.
///
/// The shallow-newline branch rolls back the trivia so the surrounding
/// statement owner keeps that boundary.  The two builders deliberately stay
/// owner-supplied: the shared decision owns layout and recovery timing, not a
/// declaration's AST/CST identity.
pub(super) fn classify_binding_style_body_layout<E>(
    base_indent: usize,
    i: &mut SynIn<E>,
) -> BindingStyleBodyLayout
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let has_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
    if !has_newline {
        return BindingStyleBodyLayout::Inline { trivia };
    }
    let block_indent = i.local.line().line_indent;
    if block_indent > base_indent {
        BindingStyleBodyLayout::Indented {
            opening_trivia: trivia,
            block_indent,
        }
    } else {
        i.rollback(checkpoint);
        BindingStyleBodyLayout::OuterBoundary
    }
}

/// AST half of the reusable Binding-style inline-or-indented body decision.
pub(super) fn parse_binding_style_body<'source, E, Body>(
    base_indent: usize,
    parse_inline: impl FnOnce(TriviaRun, &mut SynIn<'_, 'source, '_, E>) -> Option<Body>,
    parse_indented: impl FnOnce(TriviaRun, usize, &mut SynIn<'_, 'source, '_, E>) -> Body,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Body>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match classify_binding_style_body_layout(base_indent, i) {
        BindingStyleBodyLayout::Inline { trivia } => parse_inline(trivia, i),
        BindingStyleBodyLayout::Indented {
            opening_trivia,
            block_indent,
        } => Some(parse_indented(opening_trivia, block_indent, i)),
        BindingStyleBodyLayout::OuterBoundary => None,
    }
}

/// Direct-CST half of the reusable Binding-style inline-or-indented body
/// decision.  The owner supplies its body builders and recovery role while
/// this helper owns the exact trivia, indentation, retry, and boundary split.
pub(super) fn commit_binding_style_body<'parse, 'source, 'local, E, O, Body>(
    operators: &crate::operator::OperatorTable,
    base_indent: usize,
    body_role: GrammarRole,
    commit_inline: impl FnOnce(ParsedExpression<O::Checkpoint>) -> Body,
    commit_indented: impl FnOnce(
        TriviaRun,
        usize,
        &mut Committed<'parse, 'source, 'local, E, O>,
    ) -> Body,
    inline_error_retry: impl FnOnce(
        &mut Committed<'parse, 'source, 'local, E, O>,
    ) -> BindingStyleInlineRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Body>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match committed.probe(|probe| classify_binding_style_body_layout(base_indent, probe.input())) {
        BindingStyleBodyLayout::OuterBoundary => {
            emit_expression_missing_with_role(committed, body_role);
            Recovered::Incomplete
        }
        BindingStyleBodyLayout::Indented {
            opening_trivia,
            block_indent,
        } => Recovered::Complete(commit_indented(opening_trivia, block_indent, committed)),
        BindingStyleBodyLayout::Inline { trivia } => {
            let leading = if trivia.is_empty() {
                LeadingTrivia::None
            } else {
                LeadingTrivia::Present
            };
            committed.emit_trivia(&trivia);
            let mut recovery = BindingStyleInlineRecovery::None;
            let body = parse_direct_expression_with_operators(operators, leading, committed)
                .or_else(|| {
                    recovery = inline_error_retry(committed);
                    (recovery == BindingStyleInlineRecovery::Retry)
                        .then(|| {
                            parse_direct_expression_with_operators(
                                operators,
                                LeadingTrivia::None,
                                committed,
                            )
                        })
                        .flatten()
                });
            match body {
                Some(body) => Recovered::Complete(commit_inline(body)),
                None if recovery != BindingStyleInlineRecovery::TerminalError => {
                    emit_expression_missing_with_role(committed, body_role);
                    Recovered::Incomplete
                }
                None => Recovered::Incomplete,
            }
        }
    }
}
