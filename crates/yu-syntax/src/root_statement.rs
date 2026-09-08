//! Root-style statement progression and recovery; terminal exits retain their current Item.

use std::{ops::Range, sync::Arc};

use chasa_recover::In;
use reborrow_generic::Reborrow as _;

use crate::{
    recovery_record::{
        ExpectationSources, ExpectedSyntax, GrammarRole, KeywordEvidence, LayoutRole, RecoveryKind,
        RecoverySiteKey, RootUnexpected, RootUnexpectedHead, StatementKind, StatementRole,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    ambient_claim::AmbientClaimView,
    cst_output::{
        CstOutput, RecoveryDraft,
        emit::{emit_recovery_error_run, emit_recovery_missing, token_syntax_kind},
    },
    cursor::{Recover, SyntaxIn},
    declaration::{operator_header, use_decl},
    handoff::{Either, MlMode, NormalizedExit},
    header,
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, TokenKind},
        stops::STOP_SEMICOLON,
        yumark::FenceBoundary,
    },
    sequence::SequenceOwner,
    statement::{self, StatementLineHandoff},
};

#[cfg(test)]
use crate::lexical::item::PendingBoundary;

pub(crate) fn parse_root_statements(
    source_len: usize,
    remaining: &mut &str,
    recover: &mut Recover<'_>,
    output: &mut CstOutput,
) {
    let (mut terminal, _, _) = root_statement_sequence(
        source_len,
        remaining,
        recover,
        output,
        RootStatementState {
            origin: 0,
            line: LineEntry::PhysicalStart,
            pending: None,
            separated: false,
            leading_header: true,
            previous: StatementRole::Starter,
            ambient: Some(AmbientClaimView::root_statement(0)),
        },
        None,
    );
    assert!(
        terminal.payload_view().is_eof(),
        "an unfenced Root ends at EOF"
    );
    terminal.emit_eof_leading(output);
}

/// Consume one cell body in the host syntax environment and return its outer boundary.
#[cfg(test)]
pub(crate) fn parse_yulang_code_cell(
    source_len: usize,
    remaining: &mut &str,
    recover: &mut Recover<'_>,
    output: &mut CstOutput,
    origin: usize,
    line: LineEntry,
    fence: &FenceBoundary,
) -> (PendingBoundary, usize, LineEntry) {
    output.start_node(SyntaxKind::YmYulangCodeCell.into());
    let (terminal, origin, line) = root_statement_sequence(
        source_len,
        remaining,
        recover,
        output,
        RootStatementState::fenced(origin, line),
        Some(fence),
    );
    let boundary = terminal.emit_terminal_boundary(output);
    output.finish_node();
    (boundary, origin, line)
}

struct RootStatementState {
    origin: usize,
    line: LineEntry,
    pending: Option<Item>,
    separated: bool,
    leading_header: bool,
    previous: StatementRole,
    ambient: Option<AmbientClaimView<'static>>,
}

impl RootStatementState {
    #[cfg(test)]
    fn fenced(origin: usize, line: LineEntry) -> Self {
        Self {
            origin,
            line,
            pending: None,
            separated: false,
            leading_header: false,
            previous: StatementRole::Starter,
            ambient: None,
        }
    }
}

fn root_statement_sequence(
    source_len: usize,
    remaining: &mut &str,
    recover: &mut Recover<'_>,
    output: &mut CstOutput,
    state: RootStatementState,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let RootStatementState {
        mut origin,
        mut line,
        mut pending,
        mut separated,
        mut leading_header,
        mut previous,
        ambient,
    } = state;
    loop {
        let entered_at_start = line == LineEntry::PhysicalStart;
        let mut i: SyntaxIn = In::new(&mut *remaining, &mut *recover, &mut *output);
        let mut item = match pending.take() {
            Some(item) => item,
            None => {
                let scanned = statement::statement_item_normalized(
                    i.rb(),
                    origin,
                    line,
                    fence,
                    0,
                    STOP_SEMICOLON,
                );
                origin = scanned.1;
                line = scanned.2;
                scanned.0
            }
        };
        // Only the source wrapper or cell terminal adapter may emit
        // terminal leading. Root layout and recovery must not inspect it first.
        if item.payload_view().is_eof() || item.payload_view().is_boundary() {
            return (item, origin, line);
        }
        let root_line =
            crate::lexical::observation::indentation_after_newline(item.leading_view()) == Some(0);
        let physical_start = (entered_at_start || root_line)
            && crate::lexical::observation::indentation_after_newline(item.leading_view())
                .unwrap_or_else(|| usize::from(item.leading_view().has_ordinary_horizontal_gap()))
                == 0;
        if item.payload_view().token_kind() == Some(TokenKind::Semicolon) {
            item.emit_remaining(&mut *i.state, SyntaxKind::Semicolon);
            separated = true;
            leading_header = false;
            previous = StatementRole::Starter;
            continue;
        }
        if !separated && !physical_start {
            let next = root_error(i, item, origin, line, previous, fence);
            pending = Some(next.0);
            origin = next.1;
            line = next.2;
            continue;
        }
        let is_use = use_decl::use_declaration_selected_normalized(i.rb(), &item, origin, fence);
        let is_operator = !is_use
            && i.rb()
                .map(
                    |lex: crate::cursor::LexIn| {
                        Some(header::operator_selected(lex, &item, origin, fence))
                    },
                    |x| x,
                )
                .unwrap();
        let shared = leading_header && physical_start && (is_use || is_operator);
        if !shared {
            leading_header = false;
        }
        item.emit_all_remaining_leading(&mut *i.state);
        let exit = if is_operator {
            drop(i);
            let (next, next_origin, next_line, _) = if shared {
                let mut scope = output.header_reconciliation_scope();
                operator_header::operator_header_normalized(
                    In::new(&mut *remaining, &mut *recover, &mut *scope),
                    item,
                    origin,
                    line,
                    fence,
                )
            } else {
                operator_header::operator_header_normalized(
                    In::new(&mut *remaining, &mut *recover, &mut *output),
                    item,
                    origin,
                    line,
                    fence,
                )
            };
            origin = next_origin;
            line = next_line;
            let mut i: SyntaxIn = In::new(&mut *remaining, &mut *recover, &mut *output);
            let exit = match next {
                Some(item) => NormalizedExit::Complete(Err(Either::Left(item)), line),
                None => operator_body(i.rb(), origin, line, fence, ambient),
            };
            previous = StatementRole::TrailingInput {
                owner: StatementKind::OperatorDefinition,
            };
            exit
        } else if shared && is_use {
            drop(i);
            let (exit, _) = {
                let mut scope = output.header_reconciliation_scope();
                use_decl::use_declaration_header_normalized(
                    In::new(&mut *remaining, &mut *recover, &mut *scope),
                    item,
                    0,
                    STOP_SEMICOLON,
                    origin,
                    line,
                    fence,
                )
            };
            previous = StatementRole::TrailingInput {
                owner: StatementKind::UseDeclaration,
            };
            exit
        } else if let Some(admission) =
            statement::classify_statement_item_normalized(i.rb(), &item, 0, origin, fence)
        {
            previous = admission.root_trailing_role();
            statement::canonical_statement_contents_from_admission_normalized(
                i,
                item,
                admission,
                0,
                STOP_SEMICOLON,
                StatementLineHandoff::OrdinaryLayout,
                origin,
                line,
                fence,
                ambient.into(),
                Some(SequenceOwner::RootStatement),
            )
        } else {
            let next = root_error(i, item, origin, line, StatementRole::Starter, fence);
            pending = Some(next.0);
            origin = next.1;
            line = next.2;
            separated = false;
            continue;
        };
        origin = source_len - remaining.len();
        (pending, line) = match exit {
            NormalizedExit::Complete(Ok(()), line) => (None, line),
            NormalizedExit::Complete(Err(Either::Left(item)), line)
            | NormalizedExit::Deferred(item, line) => (Some(item), line),
            NormalizedExit::Complete(Err(Either::Right(end)), line) => (Some(end.item), line),
        };
        separated = false;
    }
}

fn operator_body(
    mut i: SyntaxIn,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: Option<AmbientClaimView<'_>>,
) -> NormalizedExit {
    let (mut item, mut origin, mut line) = crate::lexical::expression_item::expression_item(
        i.rb(),
        crate::lexical::operator_scan::OperatorSite::Nud,
        origin,
        line,
        fence,
        0,
        STOP_SEMICOLON,
    );
    if !item.payload_view().is_boundary() && item.leading_view().contains_line_break() {
        if let Some(after_newline) = item.leading_view().cut_after_first_ordinary_newline() {
            item.emit_leading_prefix_with(&mut *i.state, after_newline - 1, |_, _| {});
        }
        let role = GrammarRole::Statement(StatementRole::OperatorDefinitionBody);
        emit_recovery_missing(
            i,
            LeadingTrivia::default(),
            item.extent(origin).recovery_range().start,
            |range| {
                recovery_draft(
                    role,
                    RecoveryKind::Missing,
                    range,
                    Arc::from([]),
                    &[ExpectedSyntax::Expression],
                )
            },
        );
        return NormalizedExit::Complete(Err(Either::Left(item)), line);
    }
    if item.leading_view().is_grammar_empty() && crate::expression::is_nud_item(&item) {
        let role = GrammarRole::Layout(LayoutRole::InlineTrivia);
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            item.extent(origin).recovery_range().start,
            |range| {
                recovery_draft(
                    role,
                    RecoveryKind::Missing,
                    range,
                    Arc::from([]),
                    &[ExpectedSyntax::InlineTrivia],
                )
            },
        );
    }
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let role = GrammarRole::Statement(StatementRole::OperatorDefinitionBody);
    if !body_boundary(&item) && !crate::expression::is_nud_item(&item) {
        (item, origin, line) = emit_recovery_error_run(
            i.rb(),
            |run| {
                let start = item.extent(origin).recovery_range().start;
                loop {
                    let kind = item
                        .payload_view()
                        .token_kind()
                        .filter(|kind| *kind != TokenKind::Operator)
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                    (item, origin, line) = run.lexical(|lex| {
                        crate::lexical::expression_item::scan_expression_item_lexical(
                            lex,
                            crate::lexical::operator_scan::OperatorSite::Nud,
                            origin,
                            line,
                            fence,
                            0,
                            STOP_SEMICOLON,
                        )
                    });
                    if body_boundary(&item) || crate::expression::is_nud_item(&item) {
                        run.append_unexpected(UnexpectedSyntax::Token {
                            range: start..end,
                            category: UnexpectedCategory::OtherCharacter,
                        });
                        return (item, origin, line);
                    }
                }
            },
            |range, unexpected| {
                recovery_draft(
                    role,
                    RecoveryKind::Error,
                    range,
                    unexpected,
                    &[ExpectedSyntax::Expression],
                )
            },
        );
    }
    if body_boundary(&item) {
        let at = item.payload_view().pending_boundary().map_or_else(
            || item.extent(origin).recovery_range().start,
            |boundary| boundary.coordinate(),
        );
        emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
            recovery_draft(
                role,
                RecoveryKind::Missing,
                range,
                Arc::from([]),
                &[ExpectedSyntax::Expression],
            )
        });
        return NormalizedExit::Complete(Err(Either::Left(item)), line);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    crate::expression::expr_from_nud_normalized(
        i,
        item,
        None,
        0,
        STOP_SEMICOLON,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        fence,
        ambient.into(),
        Some(SequenceOwner::RootStatement),
    )
}

fn body_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || item.payload_view().is_boundary()
        || item.leading_view().contains_line_break()
        || matches!(
            item.payload_view().token_kind(),
            Some(
                TokenKind::Semicolon | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
            )
        )
        || (!crate::expression::is_nud_item(item)
            && matches!(
                item.payload_view().token_kind(),
                Some(TokenKind::LBracket | TokenKind::LBrace)
            ))
}

fn root_error(
    mut i: SyntaxIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    role: StatementRole,
    fence: Option<&crate::lexical::yumark::FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let source_tail = i.token(|lex| Some(lex.remainder())).unwrap();
    let source_origin = origin;
    item.emit_all_remaining_leading(&mut *i.state);
    let head = unexpected_head(
        item.payload_view()
            .spelling()
            .expect("a Root Error starts with a payload"),
    );
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            let mut closes = Vec::new();
            loop {
                let spelling = item.payload_view().spelling().unwrap();
                let opaque =
                    matches!(spelling, "~\"" | "'" | "'[" | "'{") || spelling.starts_with('"');
                let mut end = origin;
                let mut boundary = None;
                if opaque {
                    let region = run.lexical(|lex| {
                        crate::lexical::opaque_region::finish_opaque_opener(
                            lex, spelling, origin, fence,
                        )
                    });
                    let kind = item
                        .payload_view()
                        .token_kind()
                        .filter(|kind| *kind != TokenKind::Operator)
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    run.emit_item_as(item, origin, kind);
                    end += region.length;
                    let tail = &source_tail[origin - source_origin..end - source_origin];
                    region.visit_segments(tail, origin, |text, range, kind| {
                        run.emit_literal_segment(text, range, kind)
                    });
                    line = if fence.is_some() {
                        region.line
                    } else {
                        LineEntry::InLine
                    };
                    boundary = region.boundary;
                    origin = end;
                } else {
                    if let Some(c) = spelling.chars().next().filter(|_| spelling.len() == 1) {
                        if let Some(close) = header::matching_close(c) {
                            closes.push(close);
                        } else if closes.last() == Some(&c) {
                            closes.pop();
                        }
                    }
                    let kind = item
                        .payload_view()
                        .token_kind()
                        .filter(|kind| *kind != TokenKind::Operator)
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    run.emit_item_as(item, origin, kind);
                }
                (item, origin, line) = if let Some(boundary) = boundary {
                    (boundary, origin, line)
                } else {
                    run.lexical(|lex| {
                        statement::scan_statement_item_lexical(
                            lex,
                            origin,
                            line,
                            fence,
                            0,
                            STOP_SEMICOLON,
                        )
                    })
                };
                if item.payload_view().is_eof()
                    || item.payload_view().is_boundary()
                    || (closes.is_empty()
                        && (item.payload_view().token_kind() == Some(TokenKind::Semicolon)
                            || crate::lexical::observation::indentation_after_newline(
                                item.leading_view(),
                            ) == Some(0)))
                {
                    let range = start..end;
                    run.append_unexpected(match role {
                        StatementRole::Starter => {
                            UnexpectedSyntax::Root(RootUnexpected::UnrecognizedStarter {
                                range,
                                head,
                            })
                        }
                        StatementRole::TrailingInput { owner } => {
                            UnexpectedSyntax::Root(RootUnexpected::TrailingInput {
                                owner,
                                range,
                                head,
                            })
                        }
                        _ => UnexpectedSyntax::Token {
                            range,
                            category: UnexpectedCategory::OtherCharacter,
                        },
                    });
                    return (item, origin, line);
                }
            }
        },
        |range, unexpected| {
            let expected = if role == StatementRole::Separator {
                vec![ExpectedSyntax::StatementSeparator]
            } else {
                [
                    KeywordEvidence::Use,
                    KeywordEvidence::Lazy,
                    KeywordEvidence::Prefix,
                    KeywordEvidence::Infix,
                    KeywordEvidence::Suffix,
                    KeywordEvidence::Nullfix,
                ]
                .map(ExpectedSyntax::Keyword)
                .to_vec()
            };
            recovery_draft(
                GrammarRole::Statement(role),
                RecoveryKind::Error,
                range,
                unexpected,
                &expected,
            )
        },
    )
}

fn recovery_draft(
    role: GrammarRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
    expected: &[ExpectedSyntax],
) -> RecoveryDraft {
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expected
            .iter()
            .map(|&expected| SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect(),
        0,
    )
}

#[cfg(test)]
mod cell_tests {
    use super::*;
    use crate::{
        lexical::yumark::{FenceLineDecision, FenceOpener, FencePrefixPolicy, judge_fence_line},
        operator_table::OperatorTable,
        syntax_kind::SyntaxNode,
    };

    #[test]
    fn cell_stream_preserves_terminal_facts_body_leading_and_common_root_ranges() {
        for newline in ["\n", "\r\n"] {
            for quoted in [false, true] {
                let prefix = if quoted { "> " } else { "" };
                for body in ["", "値", "値; 終", "our x = 値", "値\n終"] {
                    for ending in ["close", "transition", "eof"] {
                        if !quoted && ending == "transition" {
                            continue;
                        }
                        let host = format!("host α{newline}");
                        let body = format!(
                            "{prefix}{} {newline}{prefix}{newline}",
                            body.replace('\n', &format!("{newline}{prefix}"))
                        );
                        let suffix = match ending {
                            "close" => format!("{prefix}``` \t{newline}rest"),
                            "transition" => format!(">> outer{newline}rest"),
                            _ => String::new(),
                        };
                        let source = format!("{host}{body}{suffix}");
                        let mut remaining = &source[host.len()..];
                        let operators = OperatorTable::empty();
                        let mut recover = Recover::new(&operators);
                        let mut output = CstOutput::new();
                        output.start_node(SyntaxKind::Root.into());
                        output.token(SyntaxKind::Unknown.into(), &host);
                        output.start_node(SyntaxKind::YmCodeFence.into());
                        let fence = FenceBoundary {
                            opener: FenceOpener {
                                line: 0,
                                marker: 0..3,
                                marker_width: 3,
                            },
                            prefix_policy: if quoted {
                                FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 }
                            } else {
                                FencePrefixPolicy::None
                            },
                            close_column: 0,
                        };
                        let (boundary, origin, line) = parse_yulang_code_cell(
                            source.len(),
                            &mut remaining,
                            &mut recover,
                            &mut output,
                            host.len(),
                            LineEntry::PhysicalStart,
                            &fence,
                        );
                        assert_eq!(remaining, suffix);
                        assert_eq!(origin, host.len() + body.len());
                        let FenceLineDecision::Boundary(expected) =
                            judge_fence_line(&suffix, origin, &fence)
                        else {
                            panic!("expected terminal: {source:?}")
                        };
                        assert_eq!(boundary, expected);
                        assert_eq!(boundary.coordinate(), origin);
                        if ending != "eof" {
                            assert_eq!(line, LineEntry::PhysicalStart);
                        }
                        output.finish_node();
                        output.finish_node();
                        let (green, records) = output.finish_with_recoveries();
                        assert!(records.is_empty(), "{source:?}: {records:?}");
                        assert_eq!(green.to_string(), format!("{host}{body}"));
                        let syntax = SyntaxNode::new_root(green);
                        let cell = syntax
                            .descendants()
                            .find(|n| n.kind() == SyntaxKind::YmYulangCodeCell)
                            .unwrap();
                        assert_eq!(cell.to_string(), body);
                        assert_eq!(cell.parent().unwrap().kind(), SyntaxKind::YmCodeFence);
                        assert!(!cell.descendants().any(|n| n.kind() == SyntaxKind::Root));
                        for token in cell
                            .descendants_with_tokens()
                            .filter_map(|e| e.into_token())
                        {
                            let range = usize::from(token.text_range().start())
                                ..usize::from(token.text_range().end());
                            assert_eq!(token.text(), &source[range]);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn cell_keeps_child_recovery_order_before_terminal_leading() {
        for newline in ["\n", "\r\n"] {
            for suffix in ["> ```\nrest", ">> outer\nrest", ""] {
                let body = format!("> ]{newline}> prefix (?) 70 ={newline}");
                let source = format!("{body}{suffix}");
                let mut remaining = source.as_str();
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = CstOutput::new();
                output.start_node(SyntaxKind::Root.into());
                let fence = FenceBoundary {
                    opener: FenceOpener {
                        line: 0,
                        marker: 0..3,
                        marker_width: 3,
                    },
                    prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
                    close_column: 0,
                };
                let (boundary, origin, _) = parse_yulang_code_cell(
                    source.len(),
                    &mut remaining,
                    &mut recover,
                    &mut output,
                    0,
                    LineEntry::PhysicalStart,
                    &fence,
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(remaining, suffix);
                assert_eq!(origin, body.len());
                assert_eq!(boundary.coordinate(), origin);
                assert_eq!(green.to_string(), body);
                assert_eq!(records.len(), 2);
                assert_eq!(records[0].id, crate::recovery_record::DiagnosticId(0));
                assert_eq!(records[0].kind, RecoveryKind::Error);
                assert_eq!(
                    records[0].site.role,
                    GrammarRole::Statement(StatementRole::Starter)
                );
                assert_eq!(records[0].site.range, 2..3);
                assert_eq!(records[1].id, crate::recovery_record::DiagnosticId(1));
                assert_eq!(records[1].kind, RecoveryKind::Missing);
                assert_eq!(
                    records[1].site.role,
                    GrammarRole::Statement(StatementRole::OperatorDefinitionBody)
                );
                assert_eq!(records[1].site.range, origin..origin);
                let syntax = SyntaxNode::new_root(green);
                let cell = syntax.children().next().unwrap();
                assert_eq!(cell.kind(), SyntaxKind::YmYulangCodeCell);
                assert_eq!(
                    cell.last_child_or_token().unwrap().kind(),
                    SyntaxKind::Newline
                );
                let missing = cell
                    .descendants()
                    .find(|n| n.kind() == SyntaxKind::Missing)
                    .unwrap();
                assert_eq!(
                    usize::from(missing.text_range().start()),
                    body.len() - newline.len()
                );
            }
        }
    }

    #[test]
    fn cell_uses_host_operators_without_activating_local_declarations() {
        let header = crate::header::discover_header("infix (<+>) 50 51 = value\n");
        let compilation = crate::operator_compilation::compile_full_parse_operators_recovering(
            &OperatorTable::empty(),
            &header.operators,
        )
        .unwrap();
        assert!(header.recoveries.is_empty());
        assert!(compilation.rejected_conflicts.is_empty());
        let operators = compilation.table;
        for source in [
            "a <+> b\n```",
            "prefix (?) 70 = 値\na <+> b\n```",
            "prefix (?) 70 = 値\n? value\n```",
        ] {
            let mut remaining = source;
            let mut recover = Recover::new(&operators);
            let mut output = CstOutput::new();
            output.start_node(SyntaxKind::Root.into());
            let fence = FenceBoundary {
                opener: FenceOpener {
                    line: 0,
                    marker: 0..3,
                    marker_width: 3,
                },
                prefix_policy: FencePrefixPolicy::None,
                close_column: 0,
            };
            parse_yulang_code_cell(
                source.len(),
                &mut remaining,
                &mut recover,
                &mut output,
                0,
                LineEntry::PhysicalStart,
                &fence,
            );
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(remaining, "```");
            assert_eq!(green.to_string(), source.strip_suffix("```").unwrap());
            let syntax = SyntaxNode::new_root(green);
            if source.contains("? value") {
                assert!(!records.is_empty());
                assert!(
                    !syntax
                        .descendants()
                        .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
                );
            } else {
                assert!(records.is_empty(), "{source:?}: {records:?}");
                assert_eq!(
                    syntax
                        .descendants()
                        .filter(|node| node.kind() == SyntaxKind::InfixOperatorUse)
                        .count(),
                    1
                );
            }
        }
    }
}

#[cfg(test)]
mod sequence_fence_tests {
    use super::*;
    use crate::lexical::{
        item::{BorrowedTarget, Boundary, StopKind},
        yumark::{FenceLineDecision, FenceOpener, FencePrefixPolicy, judge_fence_line},
    };
    use crate::operator_table::OperatorTable;

    fn fence() -> FenceBoundary {
        FenceBoundary {
            opener: FenceOpener {
                line: 0,
                marker: 0..3,
                marker_width: 3,
            },
            prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
            close_column: 0,
        }
    }

    #[test]
    fn sequence_returns_acquired_and_pending_terminals_before_any_root_effect() {
        for newline in ["\n", "\r\n"] {
            for suffix in ["> ```\nrest", "outer\nrest", ""] {
                for preacquired in [false, true] {
                    let leading = format!(" {newline}> {newline}");
                    let host = "host α\n";
                    let start = host.len();
                    let source = format!("{host}{leading}{suffix}");
                    let mut remaining = &source[start..];
                    let operators = OperatorTable::empty();
                    let mut recover = Recover::new(&operators);
                    let mut output = CstOutput::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
                    let mut state = RootStatementState::fenced(start, LineEntry::InLine);
                    // A pending terminal must also precede separator and header state.
                    state.separated = true;
                    let before = if preacquired {
                        let (item, origin, line) = statement::statement_item_normalized(
                            In::new(&mut remaining, &mut recover, &mut output),
                            start,
                            LineEntry::InLine,
                            Some(&fence),
                            0,
                            STOP_SEMICOLON,
                        );
                        let facts = item.payload_view().pending_boundary().unwrap().clone();
                        state.origin = origin;
                        state.line = line;
                        state.pending = Some(item);
                        Some(facts)
                    } else {
                        None
                    };
                    let (item, origin, line) = root_statement_sequence(
                        source.len(),
                        &mut remaining,
                        &mut recover,
                        &mut output,
                        state,
                        Some(&fence),
                    );
                    assert_eq!(remaining, suffix);
                    assert_eq!(origin, start + leading.len());
                    assert_eq!(
                        line,
                        if suffix.is_empty() {
                            LineEntry::InLine
                        } else {
                            LineEntry::PhysicalStart
                        }
                    );
                    assert_eq!(item.extent(origin).physical(), start..origin);
                    assert_eq!(item.extent(origin).remaining(), start..origin);
                    let boundary = item.payload_view().pending_boundary().unwrap();
                    assert_eq!(boundary.coordinate(), origin);
                    if let Some(before) = before {
                        assert_eq!(boundary, &before);
                    }
                    match suffix {
                        "" => assert_eq!(boundary.kind(), &Boundary::EofAfterTrivia),
                        "outer\nrest" => assert!(matches!(
                            boundary.kind(),
                            Boundary::Stop(StopKind::YumarkFence(_))
                        )),
                        _ => assert!(matches!(
                            boundary.kind(),
                            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
                        )),
                    }
                    output.finish_node();
                    let (green, records) = output.finish_with_recoveries();
                    assert_eq!(green.to_string(), "");
                    assert!(records.is_empty());
                }
            }
        }
    }

    #[test]
    fn sequence_statement_and_child_exits_retain_fenced_terminal_leading() {
        for newline in ["\n", "\r\n"] {
            for body in [
                "",
                "値",
                "my x = 値",
                "our x = 値",
                "値; 終",
                "値\n> 終",
                "prefix (?) 70 = 値",
                "my prefix (?) 70 = 値",
                "lazy prefix (?) 70 = 値",
            ] {
                let body = body.replace('\n', newline);
                for suffix in ["> ```\nrest", "outer\nrest", ""] {
                    let emitted = if body.is_empty() {
                        String::new()
                    } else {
                        format!("> {body}")
                    };
                    let terminal_leading = if body.is_empty() {
                        format!("> {newline}")
                    } else {
                        newline.to_owned()
                    };
                    let source = format!("{emitted}{terminal_leading}{suffix}");
                    let mut remaining = source.as_str();
                    let operators = OperatorTable::empty();
                    let mut recover = Recover::new(&operators);
                    let mut output = CstOutput::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
                    let (item, origin, _) = root_statement_sequence(
                        source.len(),
                        &mut remaining,
                        &mut recover,
                        &mut output,
                        RootStatementState::fenced(0, LineEntry::PhysicalStart),
                        Some(&fence),
                    );
                    assert_eq!(remaining, suffix, "{source:?}");
                    let FenceLineDecision::Boundary(expected_boundary) =
                        judge_fence_line(remaining, origin, &fence)
                    else {
                        panic!("expected terminal fence boundary: {source:?}");
                    };
                    assert_eq!(
                        item.payload_view().pending_boundary(),
                        Some(&expected_boundary),
                        "{source:?}"
                    );
                    assert_eq!(origin, emitted.len() + terminal_leading.len());
                    let extent = item.extent(origin);
                    assert_eq!(extent.physical(), emitted.len()..origin, "{source:?}");
                    assert_eq!(extent.remaining(), extent.physical(), "{source:?}");
                    assert_eq!(
                        item.payload_view().pending_boundary().unwrap().coordinate(),
                        origin
                    );
                    output.finish_node();
                    let (green, records) = output.finish_with_recoveries();
                    assert_eq!(green.to_string(), emitted, "{source:?}");
                    assert!(records.is_empty(), "{source:?}: {records:?}");
                    let syntax = crate::syntax_kind::SyntaxNode::new_root(green);
                    for token in syntax
                        .descendants_with_tokens()
                        .filter_map(|e| e.into_token())
                    {
                        let range = usize::from(token.text_range().start())
                            ..usize::from(token.text_range().end());
                        assert_eq!(token.text(), &source[range]);
                        if token.kind() == SyntaxKind::YmQuotePrefix {
                            assert_eq!(token.text(), "> ");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn operator_body_missing_returns_boundary_without_emitting_its_leading() {
        for newline in ["\n", "\r\n"] {
            for suffix in ["> ```\nrest", "outer\nrest", ""] {
                let emitted = "> prefix (?) 70 =";
                let source = format!("{emitted}{newline}{suffix}");
                let mut remaining = source.as_str();
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = CstOutput::new();
                output.start_node(SyntaxKind::Root.into());
                let fence = fence();
                let (item, origin, _) = root_statement_sequence(
                    source.len(),
                    &mut remaining,
                    &mut recover,
                    &mut output,
                    RootStatementState::fenced(0, LineEntry::PhysicalStart),
                    Some(&fence),
                );
                assert_eq!(remaining, suffix);
                assert_eq!(item.extent(origin).remaining(), emitted.len()..origin);
                let FenceLineDecision::Boundary(expected_boundary) =
                    judge_fence_line(remaining, origin, &fence)
                else {
                    panic!("expected terminal fence boundary: {source:?}");
                };
                assert_eq!(
                    item.payload_view().pending_boundary(),
                    Some(&expected_boundary),
                    "{source:?}"
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(green.to_string(), emitted);
                assert_eq!(records.len(), 1);
                assert_eq!(records[0].kind, RecoveryKind::Missing);
                assert_eq!(
                    records[0].site.role,
                    GrammarRole::Statement(StatementRole::OperatorDefinitionBody)
                );
                assert_eq!(records[0].site.range, origin..origin);
            }
        }
    }

    #[test]
    fn sequence_opaque_recovery_returns_child_boundary_and_keeps_committed_error() {
        for newline in ["\n", "\r\n"] {
            for suffix in ["> ```\nrest", "outer\nrest", ""] {
                let emitted = format!("> ] \"é{newline}> 💥{newline}");
                let source = format!("{emitted}{suffix}");
                let mut remaining = source.as_str();
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = CstOutput::new();
                output.start_node(SyntaxKind::Root.into());
                let fence = fence();
                let (item, origin, _) = root_statement_sequence(
                    source.len(),
                    &mut remaining,
                    &mut recover,
                    &mut output,
                    RootStatementState::fenced(0, LineEntry::PhysicalStart),
                    Some(&fence),
                );
                assert_eq!(remaining, suffix);
                assert_eq!(origin, emitted.len());
                assert_eq!(item.extent(origin).physical(), origin..origin);
                assert_eq!(item.extent(origin).remaining(), origin..origin);
                let FenceLineDecision::Boundary(expected_boundary) =
                    judge_fence_line(remaining, origin, &fence)
                else {
                    panic!("expected terminal fence boundary: {source:?}");
                };
                assert_eq!(
                    item.payload_view().pending_boundary(),
                    Some(&expected_boundary),
                    "{source:?}"
                );
                assert_eq!(
                    item.payload_view().pending_boundary().unwrap().coordinate(),
                    origin
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(green.to_string(), emitted);
                assert_eq!(records.len(), 1);
                assert_eq!(records[0].kind, RecoveryKind::Error);
                assert_eq!(
                    records[0].site.role,
                    GrammarRole::Statement(StatementRole::Starter)
                );
                assert_eq!(records[0].site.range, 2..origin);
            }
        }
    }

    #[test]
    fn operator_selection_lookahead_respects_fence_and_restores_the_live_suffix() {
        for newline in ["\n", "\r\n"] {
            for head in ["my", "lazy", "my lazy"] {
                for suffix in ["> ```\nrest", "outer\nrest", ""] {
                    let source = format!("{head} /* é{newline}{suffix}");
                    let mut remaining = source.as_str();
                    let operators = OperatorTable::empty();
                    let mut recover = Recover::new(&operators);
                    let mut output = CstOutput::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
                    let (item, origin, _) = statement::statement_item_normalized(
                        In::new(&mut remaining, &mut recover, &mut output),
                        0,
                        LineEntry::InLine,
                        Some(&fence),
                        0,
                        STOP_SEMICOLON,
                    );
                    let before = remaining;
                    let i: SyntaxIn = In::new(&mut remaining, &mut recover, &mut output);
                    let selected = i
                        .map(
                            |lex: crate::cursor::LexIn| {
                                Some(header::operator_selected(lex, &item, origin, Some(&fence)))
                            },
                            |x| x,
                        )
                        .unwrap();
                    assert!(!selected, "{source:?}");
                    assert_eq!(remaining, before);
                    assert_eq!(item.extent(origin).physical(), 0..origin);
                    output.finish_node();
                    let (green, records) = output.finish_with_recoveries();
                    assert_eq!(green.to_string(), "");
                    assert!(records.is_empty());
                }
            }
        }
    }

    #[test]
    fn unquoted_sequence_keeps_terminal_trivia_while_source_root_emits_eof_trivia() {
        for newline in ["\n", "\r\n"] {
            for suffix in ["```\nrest", ""] {
                let source = format!("値 {newline}{suffix}");
                let mut remaining = source.as_str();
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = CstOutput::new();
                output.start_node(SyntaxKind::Root.into());
                let mut fence = fence();
                fence.prefix_policy = FencePrefixPolicy::None;
                let (item, origin, _) = root_statement_sequence(
                    source.len(),
                    &mut remaining,
                    &mut recover,
                    &mut output,
                    RootStatementState::fenced(0, LineEntry::PhysicalStart),
                    Some(&fence),
                );
                assert_eq!(remaining, suffix);
                assert_eq!(item.extent(origin).remaining(), "値".len()..origin);
                let FenceLineDecision::Boundary(expected_boundary) =
                    judge_fence_line(remaining, origin, &fence)
                else {
                    panic!("expected terminal fence boundary: {source:?}");
                };
                assert_eq!(
                    item.payload_view().pending_boundary(),
                    Some(&expected_boundary),
                    "{source:?}"
                );
                assert_eq!(
                    item.extent(origin).physical(),
                    item.extent(origin).remaining()
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(green.to_string(), "値");
                assert!(records.is_empty());
            }
            let source = format!("値 {newline}");
            let root =
                crate::source_file::parse_root_candidate(&source, &OperatorTable::empty(), &[]);
            assert_eq!(root.green.to_string(), source);
            assert!(root.committed_recoveries.is_empty());
        }
    }
}

#[cfg(test)]
mod opaque_fence_tests {
    use super::*;
    use crate::{
        lexical::{
            item::{BorrowedTarget, Boundary},
            yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy},
        },
        operator_table::OperatorTable,
        recovery_record::{CommittedRecoveryRecord, Delimiter, DiagnosticId, PunctuationEvidence},
    };

    fn starter_error(end: usize) -> CommittedRecoveryRecord {
        let role = GrammarRole::Statement(StatementRole::Starter);
        CommittedRecoveryRecord {
            id: DiagnosticId(0),
            site: RecoverySiteKey {
                role,
                range: 0..end,
            },
            kind: RecoveryKind::Error,
            unexpected: Arc::from([UnexpectedSyntax::Root(
                RootUnexpected::UnrecognizedStarter {
                    range: 0..end,
                    head: RootUnexpectedHead::Punctuation(PunctuationEvidence::Close(
                        Delimiter::Bracket,
                    )),
                },
            )]),
            expectations: [
                KeywordEvidence::Use,
                KeywordEvidence::Lazy,
                KeywordEvidence::Prefix,
                KeywordEvidence::Infix,
                KeywordEvidence::Suffix,
                KeywordEvidence::Nullfix,
            ]
            .map(|keyword| SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Keyword(keyword),
                range: 0..end,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .into(),
            primary_expectation: 0,
        }
    }

    #[test]
    fn root_opaque_error_preserves_ordered_prefix_segments_and_exact_record() {
        for newline in ["\n", "\r\n"] {
            let parts = [
                format!("é{newline}"),
                "> ".to_owned(),
                format!("💥{newline}"),
                "  >\t".to_owned(),
                format!("終{newline}"),
            ];
            let body = format!("] \"{}", parts.concat());
            let closing = "> ```\nrest";
            let source = format!("{body}{closing}");
            let mut remaining = source.as_str();
            let operators = OperatorTable::empty();
            let mut recover = Recover::new(&operators);
            let mut output = CstOutput::new();
            output.start_node(SyntaxKind::Root.into());
            let fence = FenceBoundary {
                opener: FenceOpener {
                    line: 0,
                    marker: 0..3,
                    marker_width: 3,
                },
                prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
                close_column: 0,
            };
            let (item, origin, line) = statement::statement_item_normalized(
                In::new(&mut remaining, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                Some(&fence),
                0,
                STOP_SEMICOLON,
            );
            let (pending, origin, _) = root_error(
                In::new(&mut remaining, &mut recover, &mut output),
                item,
                origin,
                line,
                StatementRole::Starter,
                Some(&fence),
            );
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(green.to_string(), body);
            assert_eq!(records, [starter_error(body.len())]);
            assert_eq!(remaining, closing);
            assert_eq!(origin, body.len());
            assert!(matches!(
                pending.payload_view().pending_boundary().map(|b| b.kind()),
                Some(Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_)))
            ));
            let syntax = crate::syntax_kind::SyntaxNode::new_root(green);
            let actual: Vec<_> = syntax
                .descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .filter(|t| usize::from(t.text_range().start()) >= 3)
                .map(|t| {
                    (
                        t.kind(),
                        usize::from(t.text_range().start())..usize::from(t.text_range().end()),
                        t.text().to_owned(),
                    )
                })
                .collect();
            let mut start = 3;
            let expected: Vec<_> = parts
                .into_iter()
                .enumerate()
                .map(|(index, text)| {
                    let end = start + text.len();
                    let range = start..end;
                    start = end;
                    (
                        if index % 2 == 0 {
                            SyntaxKind::Unknown
                        } else {
                            SyntaxKind::YmQuotePrefix
                        },
                        range,
                        text,
                    )
                })
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn unfenced_root_opaque_error_keeps_exact_starter_record() {
        let source = "] \"é\r\n> 💥";
        let mut remaining = source;
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut output = CstOutput::new();
        output.start_node(SyntaxKind::Root.into());
        let (item, origin, line) = statement::statement_item_normalized(
            In::new(&mut remaining, &mut recover, &mut output),
            0,
            LineEntry::InLine,
            None,
            0,
            STOP_SEMICOLON,
        );
        let (pending, origin, line) = root_error(
            In::new(&mut remaining, &mut recover, &mut output),
            item,
            origin,
            line,
            StatementRole::Starter,
            None,
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), source);
        assert_eq!(records, [starter_error(source.len())]);
        assert_eq!(remaining, "");
        assert_eq!(origin, source.len());
        assert_eq!(line, LineEntry::InLine);
        assert!(pending.payload_view().is_eof());
    }

    #[test]
    fn root_opaque_error_returns_whole_fence_and_emits_foreign_prefixes() {
        for newline in ["\n", "\r\n"] {
            for opener in [
                "\"text",
                "\"\"\"text",
                "~\"text",
                "\"%{ /* text",
                "\"%{ // text",
                "\"%{ '[text",
                "'{text",
                "'{\n```text",
            ] {
                for closing in [
                    "> ```  \r\nrest",
                    ">> transition\nrest",
                    "plain\nrest",
                    ">>>\nrest",
                    "",
                ] {
                    let body = format!("] {opener}{newline}> 💥 body{newline}");
                    let source = format!("{body}{closing}");
                    let mut remaining = source.as_str();
                    let operators = OperatorTable::empty();
                    let mut recover = Recover::new(&operators);
                    let mut output = CstOutput::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = FenceBoundary {
                        opener: FenceOpener {
                            line: 0,
                            marker: 0..3,
                            marker_width: 3,
                        },
                        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
                        close_column: 0,
                    };
                    // The opener and first body line were already admitted by the containing owner.
                    let (item, origin, line) = statement::statement_item_normalized(
                        In::new(&mut remaining, &mut recover, &mut output),
                        0,
                        LineEntry::InLine,
                        Some(&fence),
                        0,
                        STOP_SEMICOLON,
                    );
                    let (pending, origin, line) = root_error(
                        In::new(&mut remaining, &mut recover, &mut output),
                        item,
                        origin,
                        line,
                        StatementRole::Starter,
                        Some(&fence),
                    );
                    output.finish_node();
                    let (green, records) = output.finish_with_recoveries();
                    // A newline inside the nested-fence opener itself can expose a transition first.
                    let accepted = if opener == "'{\n```text" {
                        "] '{\n"
                    } else {
                        body.as_str()
                    };
                    assert_eq!(green.to_string(), accepted, "{source:?}");
                    assert_eq!(origin, accepted.len(), "{source:?}");
                    assert_eq!(remaining, &source[accepted.len()..]);
                    let crate::lexical::yumark::FenceLineDecision::Boundary(expected) =
                        crate::lexical::yumark::judge_fence_line(remaining, origin, &fence)
                    else {
                        panic!("the root must return a judged boundary")
                    };
                    assert_eq!(pending.payload_view().pending_boundary(), Some(&expected));
                    assert_eq!(records.len(), 1, "{source:?}");
                    assert_eq!(records[0].site.range, 0..accepted.len());
                    assert_eq!(
                        pending.extent(origin).recovery_range().start,
                        accepted.len()
                    );
                    assert_eq!(
                        line,
                        if remaining.is_empty() {
                            LineEntry::InLine
                        } else {
                            LineEntry::PhysicalStart
                        }
                    );
                    if remaining.starts_with("> ```") {
                        assert!(matches!(
                            pending
                                .payload_view()
                                .pending_boundary()
                                .map(|boundary| boundary.kind()),
                            Some(Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_)))
                        ));
                    }
                    let syntax = crate::syntax_kind::SyntaxNode::new_root(green);
                    let prefixes: Vec<_> = syntax
                        .descendants_with_tokens()
                        .filter_map(|e| e.into_token())
                        .filter(|t| t.kind() == SyntaxKind::YmQuotePrefix)
                        .map(|t| t.text().to_owned())
                        .collect();
                    assert_eq!(
                        prefixes,
                        if accepted == body {
                            vec!["> ".to_owned()]
                        } else {
                            vec![]
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn root_opaque_nested_regions_stop_at_unquoted_fence() {
        for newline in ["\n", "\r\n"] {
            for opener in [
                "\"escape\\",
                "\"%{ /* outer /* inner",
                "'{\n```text\nraw",
                "'{\n```yulang\n\"nested",
                "~\"{ \"nested",
            ] {
                let body = format!("] {opener}{newline}");
                let closing = "````\t\r\nnext";
                let source = format!("{body}{closing}");
                let mut remaining = source.as_str();
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = CstOutput::new();
                output.start_node(SyntaxKind::Root.into());
                let fence = FenceBoundary {
                    opener: FenceOpener {
                        line: 0,
                        marker: 0..4,
                        marker_width: 4,
                    },
                    prefix_policy: FencePrefixPolicy::None,
                    close_column: 0,
                };
                let (item, origin, line) = statement::statement_item_normalized(
                    In::new(&mut remaining, &mut recover, &mut output),
                    0,
                    LineEntry::InLine,
                    Some(&fence),
                    0,
                    STOP_SEMICOLON,
                );
                let (pending, origin, line) = root_error(
                    In::new(&mut remaining, &mut recover, &mut output),
                    item,
                    origin,
                    line,
                    StatementRole::Starter,
                    Some(&fence),
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(green.to_string(), body, "{source:?}");
                assert_eq!(remaining, closing);
                assert_eq!(origin, body.len());
                assert_eq!(line, LineEntry::PhysicalStart);
                assert_eq!(records.len(), 1);
                assert_eq!(records[0].site.range, 0..body.len());
                let crate::lexical::yumark::FenceLineDecision::Boundary(expected) =
                    crate::lexical::yumark::judge_fence_line(remaining, origin, &fence)
                else {
                    panic!("expected close")
                };
                assert_eq!(pending.payload_view().pending_boundary(), Some(&expected));
            }
        }
    }
}

fn unexpected_head(text: &str) -> RootUnexpectedHead {
    use crate::recovery_record::Delimiter;
    use crate::recovery_record::PunctuationEvidence as P;
    let c = text.chars().next().unwrap();
    let punctuation = if text.starts_with("::") {
        Some(P::ColonColon)
    } else {
        match c {
            '(' => Some(P::Open(Delimiter::Parenthesis)),
            ')' => Some(P::Close(Delimiter::Parenthesis)),
            '[' => Some(P::Open(Delimiter::Bracket)),
            ']' => Some(P::Close(Delimiter::Bracket)),
            '{' => Some(P::Open(Delimiter::Brace)),
            '}' => Some(P::Close(Delimiter::Brace)),
            ',' => Some(P::Comma),
            ';' => Some(P::Semicolon),
            '.' => Some(P::Dot),
            '/' => Some(P::Slash),
            ':' => Some(P::Colon),
            '\\' => Some(P::Backslash),
            '\'' => Some(P::Apostrophe),
            '=' => Some(P::Equals),
            '*' => Some(P::Star),
            _ => None,
        }
    };
    if let Some(p) = punctuation {
        return RootUnexpectedHead::Punctuation(p);
    }
    if c == '_' || unicode_ident::is_xid_start(c) {
        RootUnexpectedHead::Word
    } else if c.is_ascii_digit() {
        RootUnexpectedHead::DecimalInteger
    } else if "+-!#$%&<>?@^|~".contains(c) {
        RootUnexpectedHead::OperatorLike
    } else {
        RootUnexpectedHead::OtherCharacter
    }
}
