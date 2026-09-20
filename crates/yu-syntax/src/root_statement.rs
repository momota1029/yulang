//! Root-style statement progression and recovery; terminal exits retain their current Item.

#[cfg(test)]
use std::ops::Range;

use rowan::GreenNodeBuilder;

use crate::syntax_kind::SyntaxKind;

use crate::{
    ambient_claim::AmbientClaimView,
    cursor::recovery::emit::{emit_recovery_error_run, emit_recovery_missing},
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
    output: &mut GreenNodeBuilder,
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
    output: &mut GreenNodeBuilder,
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
            ambient: None,
        }
    }
}

fn root_statement_sequence(
    source_len: usize,
    remaining: &mut &str,
    recover: &mut Recover<'_>,
    output: &mut GreenNodeBuilder,
    state: RootStatementState,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let RootStatementState {
        mut origin,
        mut line,
        mut pending,
        mut separated,
        mut leading_header,
        ambient,
    } = state;
    loop {
        let entered_at_start = line == LineEntry::PhysicalStart;
        let mut i: SyntaxIn =
            crate::cursor::SyntaxIn::new(&mut *remaining, &mut *recover, &mut *output);
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
            continue;
        }
        if !separated && !physical_start {
            let next = root_error(i, item, origin, line, fence);
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
            let (next, next_origin, next_line, _) = operator_header::operator_header_normalized(
                crate::cursor::SyntaxIn::new(&mut *remaining, &mut *recover, &mut *output),
                item,
                origin,
                line,
                fence,
            );
            origin = next_origin;
            line = next_line;
            let mut i: SyntaxIn =
                crate::cursor::SyntaxIn::new(&mut *remaining, &mut *recover, &mut *output);
            let exit = match next {
                Some(item) => NormalizedExit::Complete(Err(Either::Left(item)), line),
                None => operator_body(i.rb(), origin, line, fence, ambient),
            };
            exit
        } else if shared && is_use {
            drop(i);
            let (exit, _) = use_decl::use_declaration_header_normalized(
                crate::cursor::SyntaxIn::new(&mut *remaining, &mut *recover, &mut *output),
                item,
                0,
                STOP_SEMICOLON,
                origin,
                line,
                fence,
            );
            exit
        } else if let Some(admission) =
            statement::classify_statement_item_normalized(i.rb(), &item, 0, origin, fence)
        {
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
            let next = root_error(i, item, origin, line, fence);
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
        emit_recovery_missing(
            i,
            LeadingTrivia::default(),
            item.extent(origin).recovery_range().start,
        );
        return NormalizedExit::Complete(Err(Either::Left(item)), line);
    }
    if item.leading_view().is_grammar_empty() && crate::expression::is_nud_item(&item) {
        emit_recovery_missing(
            i.rb(),
            LeadingTrivia::default(),
            item.extent(origin).recovery_range().start,
        );
    }
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    if !body_boundary(&item) && !crate::expression::is_nud_item(&item) {
        (item, origin, line) = emit_recovery_error_run(i.rb(), |run| {
            loop {
                run.emit_item_as(item, origin);
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
                    return (item, origin, line);
                }
            }
        });
    }
    if body_boundary(&item) {
        let at = item.payload_view().pending_boundary().map_or_else(
            || item.extent(origin).recovery_range().start,
            |boundary| boundary.coordinate(),
        );
        emit_recovery_missing(i, LeadingTrivia::default(), at);
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
    fence: Option<&crate::lexical::yumark::FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let source_tail = i.token(|lex| Some(lex.remainder())).unwrap();
    let source_origin = origin;
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(i, |run| {
        let mut closes = Vec::new();
        loop {
            let spelling = item.payload_view().spelling().unwrap();
            let opaque = matches!(spelling, "~\"" | "'" | "'[" | "'{") || spelling.starts_with('"');
            let mut end = origin;
            let mut boundary = None;
            if opaque {
                let region = run.lexical(|lex| {
                    crate::lexical::opaque_region::finish_opaque_opener(
                        lex, spelling, origin, fence,
                    )
                });
                run.emit_item_as(item, origin);
                end += region.length;
                let tail = &source_tail[origin - source_origin..end - source_origin];
                region.visit_segments(tail, origin, |text, range| {
                    run.emit_literal_segment(text, range)
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
                run.emit_item_as(item, origin);
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
                return (item, origin, line);
            }
        }
    })
}

#[cfg(test)]
type StructuralFact = (crate::structural_diagnostic::StructuralKind, Range<usize>);

#[cfg(test)]
fn structural_facts(green: &rowan::GreenNode) -> Vec<StructuralFact> {
    crate::structural_diagnostic::collect(&crate::SyntaxNode::new_root(green.clone()))
        .into_iter()
        .map(|diagnostic| (diagnostic.kind(), diagnostic.range().clone()))
        .collect()
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
                        let mut recover = Recover::new_for_test(&operators);
                        let mut output = GreenNodeBuilder::new();
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
                        let green = output.finish();
                        assert!(
                            structural_facts(&green).is_empty(),
                            "{source:?}: {:?}",
                            structural_facts(&green)
                        );
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
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
                let green = output.finish();
                assert_eq!(remaining, suffix);
                assert_eq!(origin, body.len());
                assert_eq!(boundary.coordinate(), origin);
                assert_eq!(green.to_string(), body);
                assert_eq!(
                    structural_facts(&green),
                    [
                        (
                            crate::structural_diagnostic::StructuralKind::ErrorGroup,
                            2..3
                        ),
                        (
                            crate::structural_diagnostic::StructuralKind::Missing,
                            body.len() - newline.len()..body.len() - newline.len()
                        ),
                    ]
                );
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
        let header_source = "infix (<+>) 50 51 = value\n";
        let header_operators = OperatorTable::empty();
        let mut header_recover = Recover::new_for_test(&header_operators);
        let mut header_output = GreenNodeBuilder::new();
        let header = crate::header::discover_header_with_cursor(
            header_source,
            &mut header_recover,
            &mut header_output,
        );
        let header_green = header_output.finish();
        assert_eq!(header_green.to_string(), header_source);
        assert!(structural_facts(&header_green).is_empty());
        let operators = crate::operator_compilation::effective_full_parse_operators(
            &OperatorTable::empty(),
            &header.operators,
        )
        .unwrap();
        assert!(
            crate::operator_compilation::conflicting_local_operators(&operators, &header.operators)
                .is_empty()
        );
        for source in [
            "a <+> b\n```",
            "prefix (?) 70 = 値\na <+> b\n```",
            "prefix (?) 70 = 値\n? value\n```",
        ] {
            let mut remaining = source;
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
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
            let green = output.finish();
            assert_eq!(remaining, "```");
            assert_eq!(green.to_string(), source.strip_suffix("```").unwrap());
            let facts = structural_facts(&green);
            let syntax = SyntaxNode::new_root(green);
            if source.contains("? value") {
                assert!(!facts.is_empty());
                assert!(
                    !syntax
                        .descendants()
                        .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
                );
            } else {
                assert!(facts.is_empty(), "{source:?}: {facts:?}");
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
    use crate::syntax_kind::SyntaxNode;

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
    fn root_direct_error_catalog_hands_close_transition_and_eof_untouched() {
        struct Row {
            name: &'static str,
            prefix: &'static str,
            before_error: &'static str,
            malformed: &'static str,
            after_error: &'static str,
        }

        let mut rows = vec![
            Row {
                name: "starter",
                prefix: "",
                before_error: "",
                malformed: "]",
                after_error: "",
            },
            Row {
                name: "separator",
                prefix: "abc",
                before_error: "   ",
                malformed: "]",
                after_error: "",
            },
        ];
        for (name, prefix) in [
            ("use", "use a "),
            ("binding", "my x = value "),
            ("mod", "mod M {x} "),
            ("struct", "struct S {} "),
            ("enum", "enum E {A} "),
            ("error", "error E {A} "),
            ("type", "type T = A "),
            ("role", "role R {} "),
            ("impl", "impl T {} "),
            ("cast", "cast(x): A = value "),
            ("act", "act A {} "),
            ("for", "for x in xs: x "),
            ("operator", "prefix (?) 70 = value "),
        ] {
            rows.push(Row {
                name,
                prefix,
                before_error: "",
                malformed: "]",
                after_error: "",
            });
        }
        rows.push(Row {
            name: "operator-body",
            prefix: "prefix (?) 70 = ",
            before_error: "",
            malformed: "@@",
            after_error: "value",
        });

        for newline in ["\n", "\r\n"] {
            for terminal in ["close", "transition", "eof"] {
                let suffix = match terminal {
                    "close" => format!("> ``` \t{newline}rest"),
                    "transition" => format!(">> outer{newline}rest"),
                    "eof" => String::new(),
                    _ => unreachable!(),
                };
                for row in &rows {
                    let body = format!(
                        "> {}{}{}{}{}",
                        row.prefix, row.before_error, row.malformed, row.after_error, newline
                    );
                    let source = format!("{body}{suffix}");
                    let error_start = body.find(row.malformed).unwrap();
                    let error_end = error_start + row.malformed.len();
                    let mut remaining = source.as_str();
                    let operators = OperatorTable::empty();
                    let mut recover = Recover::new_for_test(&operators);
                    let mut output = GreenNodeBuilder::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
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
                    let green = output.finish();
                    let label = format!("{} / {terminal} / {newline:?}", row.name);

                    assert_eq!(remaining, suffix, "{label}");
                    assert_eq!(origin, body.len(), "{label}");
                    let FenceLineDecision::Boundary(expected) =
                        judge_fence_line(remaining, origin, &fence)
                    else {
                        panic!("expected terminal boundary: {label}");
                    };
                    assert_eq!(boundary, expected, "{label}");
                    assert_eq!(boundary.coordinate(), origin, "{label}");
                    assert_eq!(green.to_string(), body, "{label}");

                    let facts = structural_facts(&green);
                    let syntax = SyntaxNode::new_root(green);
                    let cell = syntax.children().next().unwrap();
                    assert_eq!(cell.kind(), SyntaxKind::YmYulangCodeCell, "{label}");
                    assert!(
                        !cell
                            .descendants()
                            .any(|node| node.kind() == SyntaxKind::Invalid),
                        "{label}"
                    );
                    let errors: Vec<_> = cell
                        .descendants_with_tokens()
                        .filter_map(|element| element.into_token())
                        .filter(|token| token.kind() == SyntaxKind::Error)
                        .map(|token| {
                            assert_eq!(token.parent().as_ref(), Some(&cell), "{label}");
                            (
                                usize::from(token.text_range().start())
                                    ..usize::from(token.text_range().end()),
                                token.text().to_owned(),
                            )
                        })
                        .collect();
                    assert!(!errors.is_empty(), "{label}");
                    assert_eq!(errors.first().unwrap().0.start, error_start, "{label}");
                    assert_eq!(errors.last().unwrap().0.end, error_end, "{label}");
                    assert_eq!(
                        errors
                            .iter()
                            .map(|(_, text)| text.as_str())
                            .collect::<String>(),
                        row.malformed,
                        "{label}"
                    );
                    assert!(
                        cell.children_with_tokens().any(|element| {
                            element.kind() != SyntaxKind::Error
                                && element.to_string() == newline
                                && usize::from(element.text_range().start())
                                    == body.len() - newline.len()
                        }),
                        "{label}"
                    );
                    if !suffix.is_empty() {
                        assert!(!cell.to_string().contains(&suffix), "{label}");
                    }
                    if row.name == "operator-body" {
                        assert_eq!(
                            facts,
                            [(
                                crate::structural_diagnostic::StructuralKind::ErrorGroup,
                                error_start..error_end
                            )],
                            "{label}"
                        );
                        let value = cell
                            .children()
                            .find(|node| {
                                node.kind() == SyntaxKind::OperatorChain
                                    && node.to_string() == row.after_error
                            })
                            .unwrap();
                        assert_eq!(value.parent().as_ref(), Some(&cell), "{label}");
                        assert_eq!(
                            usize::from(value.text_range().start()),
                            error_end,
                            "{label}"
                        );
                    }
                }
            }
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
                    let mut recover = Recover::new_for_test(&operators);
                    let mut output = GreenNodeBuilder::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
                    let mut state = RootStatementState::fenced(start, LineEntry::InLine);
                    // A pending terminal must also precede separator and header state.
                    state.separated = true;
                    let before = if preacquired {
                        let (item, origin, line) = statement::statement_item_normalized(
                            crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
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
                    let green = output.finish();
                    assert_eq!(green.to_string(), "");
                    assert!(structural_facts(&green).is_empty());
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
                    let mut recover = Recover::new_for_test(&operators);
                    let mut output = GreenNodeBuilder::new();
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
                    let green = output.finish();
                    assert_eq!(green.to_string(), emitted, "{source:?}");
                    assert!(
                        structural_facts(&green).is_empty(),
                        "{source:?}: {:?}",
                        structural_facts(&green)
                    );
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
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
                let green = output.finish();
                assert_eq!(green.to_string(), emitted);
                assert_eq!(
                    structural_facts(&green),
                    [(
                        crate::structural_diagnostic::StructuralKind::Missing,
                        emitted.len()..emitted.len()
                    )]
                );
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
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
                let green = output.finish();
                assert_eq!(green.to_string(), emitted);
                assert_eq!(
                    structural_facts(&green),
                    [(
                        crate::structural_diagnostic::StructuralKind::ErrorGroup,
                        2..origin
                    )]
                );
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
                    let mut recover = Recover::new_for_test(&operators);
                    let mut output = GreenNodeBuilder::new();
                    output.start_node(SyntaxKind::Root.into());
                    let fence = fence();
                    let (item, origin, _) = statement::statement_item_normalized(
                        crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                        0,
                        LineEntry::InLine,
                        Some(&fence),
                        0,
                        STOP_SEMICOLON,
                    );
                    let before = remaining;
                    let i: SyntaxIn =
                        crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output);
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
                    let green = output.finish();
                    assert_eq!(green.to_string(), "");
                    assert!(structural_facts(&green).is_empty());
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
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
                let green = output.finish();
                assert_eq!(green.to_string(), "値");
                assert!(structural_facts(&green).is_empty());
            }
            let source = format!("値 {newline}");
            let green = crate::cursor::parse_root(&source, &OperatorTable::empty());
            assert_eq!(green.to_string(), source);
            assert!(
                crate::structural_diagnostic::collect(&crate::SyntaxNode::new_root(green))
                    .is_empty()
            );
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
    };

    #[test]
    fn root_opaque_error_preserves_ordered_prefix_segments_and_exact_structural_fact() {
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
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
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
                crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                Some(&fence),
                0,
                STOP_SEMICOLON,
            );
            let (pending, origin, _) = root_error(
                crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                item,
                origin,
                line,
                Some(&fence),
            );
            output.finish_node();
            let green = output.finish();
            assert_eq!(green.to_string(), body);
            assert_eq!(
                structural_facts(&green),
                [(
                    crate::structural_diagnostic::StructuralKind::ErrorGroup,
                    0..body.len()
                )]
            );
            assert_eq!(remaining, closing);
            assert_eq!(origin, body.len());
            assert!(matches!(
                pending.payload_view().pending_boundary().map(|b| b.kind()),
                Some(Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_)))
            ));
            let syntax = crate::syntax_kind::SyntaxNode::new_root(green);
            assert!(syntax.children().next().is_none());
            assert!(
                syntax
                    .children_with_tokens()
                    .all(|leaf| leaf.kind() == SyntaxKind::Error)
            );
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
                .map(|text| {
                    let end = start + text.len();
                    let range = start..end;
                    start = end;
                    (SyntaxKind::Error, range, text)
                })
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn unfenced_root_opaque_error_keeps_exact_starter_structural_fact() {
        let source = "] \"é\r\n> 💥";
        let mut remaining = source;
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (item, origin, line) = statement::statement_item_normalized(
            crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
            0,
            LineEntry::InLine,
            None,
            0,
            STOP_SEMICOLON,
        );
        let (pending, origin, line) = root_error(
            crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
            item,
            origin,
            line,
            None,
        );
        output.finish_node();
        let green = output.finish();
        assert_eq!(green.to_string(), source);
        assert_eq!(
            structural_facts(&green),
            [(
                crate::structural_diagnostic::StructuralKind::ErrorGroup,
                0..source.len()
            )]
        );
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
                    let mut recover = Recover::new_for_test(&operators);
                    let mut output = GreenNodeBuilder::new();
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
                        crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                        0,
                        LineEntry::InLine,
                        Some(&fence),
                        0,
                        STOP_SEMICOLON,
                    );
                    let (pending, origin, line) = root_error(
                        crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                        item,
                        origin,
                        line,
                        Some(&fence),
                    );
                    output.finish_node();
                    let green = output.finish();
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
                    assert_eq!(
                        structural_facts(&green),
                        [(
                            crate::structural_diagnostic::StructuralKind::ErrorGroup,
                            0..accepted.len()
                        )],
                        "{source:?}"
                    );
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
                    assert!(syntax.children().next().is_none());
                    assert!(
                        syntax
                            .children_with_tokens()
                            .all(|leaf| leaf.kind() == SyntaxKind::Error)
                    );
                    let prefixes: Vec<_> = syntax
                        .descendants_with_tokens()
                        .filter_map(|e| e.into_token())
                        .filter(|t| t.kind() == SyntaxKind::Error && t.text() == "> ")
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
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
                    crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                    0,
                    LineEntry::InLine,
                    Some(&fence),
                    0,
                    STOP_SEMICOLON,
                );
                let (pending, origin, line) = root_error(
                    crate::cursor::SyntaxIn::new(&mut remaining, &mut recover, &mut output),
                    item,
                    origin,
                    line,
                    Some(&fence),
                );
                output.finish_node();
                let green = output.finish();
                assert_eq!(green.to_string(), body, "{source:?}");
                assert_eq!(remaining, closing);
                assert_eq!(origin, body.len());
                assert_eq!(line, LineEntry::PhysicalStart);
                assert_eq!(
                    structural_facts(&green),
                    [(
                        crate::structural_diagnostic::StructuralKind::ErrorGroup,
                        0..body.len()
                    )]
                );
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
