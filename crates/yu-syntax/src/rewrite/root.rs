//! Root owns statement progression; child exits retain their current Item.

use std::{ops::Range, sync::Arc};

use chasa_recover::In;
use reborrow_generic::Reborrow as _;

use crate::{
    OperatorTable,
    session::{
        CommittedRecoveryRecord, ExpectationSources, ExpectedSyntax, GrammarRole, KeywordEvidence,
        LayoutRole, RecoveryKind, RecoverySiteKey, RootUnexpected, RootUnexpectedHead,
        StatementKind, StatementRole, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    RewriteIn,
    ambient_claim::AmbientClaimView,
    current_item::LineEntry,
    driver::{self, Either, MlMode, NormalizedExit},
    emit::{emit_recovery_error_run, emit_recovery_missing, token_syntax_kind},
    header,
    item::{Item, LeadingTrivia, TokenKind},
    operator::STOP_SEMICOLON,
    operator_header,
    output::{RecoveryDraft, RewriteOutput},
    sequence::SequenceOwner,
    state::Recover,
    statement::{self, StatementLineHandoff},
    use_decl,
};

pub(crate) struct RootCandidate {
    pub(crate) green: rowan::GreenNode,
    pub(crate) committed_recoveries: Vec<CommittedRecoveryRecord>,
}

pub(crate) fn parse_root_candidate(
    source: &str,
    operators: &OperatorTable,
    frozen: &[CommittedRecoveryRecord],
) -> RootCandidate {
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    let mut output = RewriteOutput::reconcile_scoped(frozen);
    output.start_node(SyntaxKind::Root.into());
    let mut origin = 0;
    let mut line = LineEntry::PhysicalStart;
    let mut pending = None;
    let mut separated = false;
    let mut leading_header = true;
    let mut previous = StatementRole::Starter;
    loop {
        let entered_at_start = line == LineEntry::PhysicalStart;
        let mut i: RewriteIn = In::new(&mut remaining, &mut recover, &mut output);
        let mut item = match pending.take() {
            Some(item) => item,
            None => {
                let scanned = statement::statement_item_normalized(
                    i.rb(),
                    origin,
                    line,
                    None,
                    0,
                    STOP_SEMICOLON,
                );
                origin = scanned.1;
                line = scanned.2;
                scanned.0
            }
        };
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            break;
        }
        assert!(
            !item.payload_view().is_boundary(),
            "an unfenced Root cannot acquire an abstract fence"
        );
        let root_line = driver::indentation_after_newline(item.leading_view()) == Some(0);
        let physical_start = (entered_at_start || root_line)
            && driver::indentation_after_newline(item.leading_view())
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
            let next = root_error(i, item, origin, line, previous);
            pending = Some(next.0);
            origin = next.1;
            line = next.2;
            continue;
        }
        let is_use = use_decl::use_declaration_selected_normalized(i.rb(), &item, origin, None);
        let is_operator = !is_use
            && i.rb()
                .map(
                    |lex: super::LexIn| Some(header::operator_selected(lex, &item, origin)),
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
                    In::new(&mut remaining, &mut recover, &mut *scope),
                    item,
                    origin,
                    line,
                    None,
                )
            } else {
                operator_header::operator_header_normalized(
                    In::new(&mut remaining, &mut recover, &mut output),
                    item,
                    origin,
                    line,
                    None,
                )
            };
            origin = next_origin;
            line = next_line;
            let mut i: RewriteIn = In::new(&mut remaining, &mut recover, &mut output);
            let exit = match next {
                Some(item) => NormalizedExit::Complete(Err(Either::Left(item)), line),
                None => operator_body(i.rb(), origin, line),
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
                    In::new(&mut remaining, &mut recover, &mut *scope),
                    item,
                    0,
                    STOP_SEMICOLON,
                    origin,
                    line,
                    None,
                )
            };
            previous = StatementRole::TrailingInput {
                owner: StatementKind::UseDeclaration,
            };
            exit
        } else if let Some(admission) =
            statement::classify_statement_item_normalized(i.rb(), &item, 0, origin, None)
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
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                Some(SequenceOwner::RootStatement),
            )
        } else {
            let next = root_error(i, item, origin, line, StatementRole::Starter);
            pending = Some(next.0);
            origin = next.1;
            line = next.2;
            separated = false;
            continue;
        };
        origin = source.len() - remaining.len();
        (pending, line) = match exit {
            NormalizedExit::Complete(Ok(()), line) => (None, line),
            NormalizedExit::Complete(Err(Either::Left(item)), line)
            | NormalizedExit::Deferred(item, line) => (Some(item), line),
            NormalizedExit::Complete(Err(Either::Right(end)), line) => (Some(end.item), line),
        };
        separated = false;
    }
    output.finish_node();
    let (green, committed_recoveries) = output.finish_with_recoveries();
    RootCandidate {
        green,
        committed_recoveries,
    }
}

fn operator_body(mut i: RewriteIn, origin: usize, line: LineEntry) -> NormalizedExit {
    let (mut item, mut origin, mut line) = driver::expression_item(
        i.rb(),
        crate::scan::operator::OperatorSite::Nud,
        origin,
        line,
        None,
        0,
        STOP_SEMICOLON,
    );
    if item.leading_view().contains_line_break() {
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
    if item.leading_view().is_grammar_empty() && driver::is_nud_item(&item) {
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
    item.emit_all_remaining_leading(&mut *i.state);
    let role = GrammarRole::Statement(StatementRole::OperatorDefinitionBody);
    if !body_boundary(&item) && !driver::is_nud_item(&item) {
        (item, origin, line) = emit_recovery_error_run(
            i.rb(),
            |run| {
                let start = item.extent(origin).recovery_range().start;
                loop {
                    let kind = item
                        .payload_view()
                        .token_kind()
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                    (item, origin, line) = run.lexical(|lex| {
                        driver::scan_expression_item_lexical(
                            lex,
                            crate::scan::operator::OperatorSite::Nud,
                            origin,
                            line,
                            None,
                            0,
                            STOP_SEMICOLON,
                        )
                    });
                    if body_boundary(&item) || driver::is_nud_item(&item) {
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
    driver::expr_from_nud_normalized(
        i,
        item,
        None,
        0,
        STOP_SEMICOLON,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
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
        || (!driver::is_nud_item(item)
            && matches!(
                item.payload_view().token_kind(),
                Some(TokenKind::LBracket | TokenKind::LBrace)
            ))
}

fn root_error(
    i: RewriteIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    role: StatementRole,
) -> (Item, usize, LineEntry) {
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
                if opaque {
                    let tail: Box<str> = run.lexical(|mut lex| {
                        let (_, text) = lex
                            .rb()
                            .with_str(|lex| header::finish_opaque_opener(lex, spelling));
                        text.into()
                    });
                    let kind = item
                        .payload_view()
                        .token_kind()
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    run.emit_item_as(item, origin, kind);
                    end += tail.len();
                    if !tail.is_empty() {
                        run.emit_literal_segment(&tail, origin..end, SyntaxKind::Unknown);
                    }
                    origin = end;
                    line = LineEntry::InLine;
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
                        .map(token_syntax_kind)
                        .unwrap_or(SyntaxKind::Operator);
                    run.emit_item_as(item, origin, kind);
                }
                (item, origin, line) = run.lexical(|lex| {
                    statement::scan_statement_item_lexical(
                        lex,
                        origin,
                        line,
                        None,
                        0,
                        STOP_SEMICOLON,
                    )
                });
                if item.payload_view().is_eof()
                    || item.payload_view().is_boundary()
                    || (closes.is_empty()
                        && (item.payload_view().token_kind() == Some(TokenKind::Semicolon)
                            || driver::indentation_after_newline(item.leading_view()) == Some(0)))
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

fn unexpected_head(text: &str) -> RootUnexpectedHead {
    use crate::session::Delimiter;
    use crate::session::PunctuationEvidence as P;
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
