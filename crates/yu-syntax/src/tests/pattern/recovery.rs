use crate::tests::pattern::*;
use crate::{
    ambient_claim::AmbientClaimView,
    cst_output::{RecoveryDraft, emit::emit_recovery_missing},
    lexical::{
        item::LeadingTrivia,
        lexer::{scan_identifier, scan_pattern_payload},
    },
    pattern::PATTERN_STOP_IN,
    recovery_record::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, PatternRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, TypeRole, UnexpectedCategory, UnexpectedSyntax,
    },
};
use chasa_recover::Recoverable as _;
use std::{ops::Range, sync::Arc};

mod default_expression;
mod delimited;
mod sequence;

#[derive(Clone, Copy)]
struct Context<'fence> {
    origin: usize,
    stops: PatternStops,
    policy: PatternMandatorySlotPolicy,
    closes: PatternCallerCloses,
    line: LineEntry,
    fence: Option<&'fence FenceBoundary>,
    emit_leading: bool,
}

impl Default for Context<'_> {
    fn default() -> Self {
        Self {
            origin: 0,
            stops: PATTERN_DEFAULT_STOPS,
            policy: PatternMandatorySlotPolicy::default(),
            closes: PatternCallerCloses::NONE,
            line: LineEntry::InLine,
            fence: None,
            emit_leading: false,
        }
    }
}

struct PatternRun<'source> {
    green: GreenNode,
    exit: NormalizedExit,
    completion: PatternCompletion,
    remainder: &'source str,
    successor: usize,
    records: Vec<CommittedRecoveryRecord>,
    slots: usize,
    diagnostics: (Option<u32>, usize),
}

fn record(id: u32, role: PatternRole, range: Range<usize>, error: bool) -> CommittedRecoveryRecord {
    let expected = match role {
        PatternRole::Primary
        | PatternRole::AlternationRhs
        | PatternRole::ParenthesizedElement
        | PatternRole::ListItem
        | PatternRole::ListSpreadRhs
        | PatternRole::RecordNestedPattern
        | PatternRole::RecordSpreadRhs => ExpectedSyntax::Pattern,
        PatternRole::SymbolName | PatternRole::AliasBinding | PatternRole::RecordItem => {
            ExpectedSyntax::Identifier
        }
        PatternRole::ParenthesizedSeparator
        | PatternRole::ListSeparator
        | PatternRole::RecordSeparator => ExpectedSyntax::DelimitedSequenceSeparator,
        PatternRole::TypeAnnotation => ExpectedSyntax::TypeExpression,
        PatternRole::RecordDefaultExpression => ExpectedSyntax::Expression,
        _ => panic!("explicit primary/tail-slot test role"),
    };
    let role = GrammarRole::Pattern(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if error {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: if error {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        } else {
            Arc::from([])
        },
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn seed_record(origin: usize) -> CommittedRecoveryRecord {
    let mut seed = record(0, PatternRole::TypeAnnotation, origin..origin, false);
    seed.site.role = GrammarRole::Type(TypeRole::ArrowRhs);
    Arc::make_mut(&mut seed.expectations)[0].role = seed.site.role;
    seed
}

fn publish_seed(output: &mut GreenNodeBuilder, origin: usize) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let seed = seed_record(origin);
    emit_recovery_missing(
        In::new(&mut input, &mut recover, output),
        LeadingTrivia::default(),
        origin,
        |range| {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: seed.site.role,
                    range,
                },
                seed.kind,
                seed.unexpected,
                seed.expectations,
                seed.primary_expectation,
            )
        },
    );
}

fn run<'source>(
    source: &'source str,
    context: Context<'_>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> PatternRun<'source> {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mark = recover.mark();
    let mut input = source;
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    publish_seed(&mut output, context.origin);
    let CurrentItem {
        mut item,
        next_line_entry,
    } = current_item(
        In::new(&mut input, &mut recover, ()),
        context.origin,
        context.line,
        context.fence,
        |mut lex, leading, origin, fence, _| {
            scan_pattern_literal_payload(lex.rb())
                .or_else(|| scan_pattern_nud_payload(lex, leading, origin, fence, context.stops))
        },
    )
    .unwrap();
    if context.emit_leading {
        item.emit_all_remaining_leading(&mut output);
    }
    let next = context.origin + source.len() - input.len();
    let (exit, completion) = required_pattern_from_entry_item_with_policy_normalized(
        In::new(&mut input, &mut recover, &mut output),
        item,
        0,
        context.stops,
        StatementLineHandoff::OrdinaryLayout,
        context.policy,
        context.closes,
        next,
        next_line_entry,
        context.fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    assert_eq!(recover.mark(), mark);
    assert!(std::ptr::eq(recover.operators(), &operators));
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    PatternRun {
        green,
        exit,
        completion,
        remainder: input,
        successor: context.origin + source.len() - input.len(),
        records,
        slots,
        diagnostics,
    }
}

fn assert_same_exit(left: &NormalizedExit, right: &NormalizedExit) {
    match (left, right) {
        (
            NormalizedExit::Complete(Err(Either::Left(a)), la),
            NormalizedExit::Complete(Err(Either::Left(b)), lb),
        ) => {
            assert_eq!(a, b);
            assert_eq!(la, lb);
        }
        (
            NormalizedExit::Complete(Err(Either::Right(a)), la),
            NormalizedExit::Complete(Err(Either::Right(b)), lb),
        ) => {
            assert_eq!(a, b);
            assert_eq!(la, lb);
        }
        _ => panic!("Pattern must return the same full current Item/EOF"),
    }
}

fn checked<'source>(
    source: &'source str,
    context: Context<'_>,
    expected: &[CommittedRecoveryRecord],
    emitted: &str,
    completion: PatternCompletion,
) -> PatternRun<'source> {
    let mut all = vec![seed_record(context.origin)];
    all.extend_from_slice(expected);
    let fresh = run(source, context, None);
    assert_eq!(
        fresh.green.to_string(),
        format!("sentinel{emitted}"),
        "{source:?}"
    );
    assert_eq!(fresh.records, all, "{source:?}");
    assert_eq!(fresh.completion, completion, "{source:?}");
    assert_eq!(fresh.slots, all.len());
    assert_eq!(fresh.diagnostics, (Some(all.len() as u32), 0));
    let root = SyntaxNode::new_root(fresh.green.clone());
    for (node_kind, record_kind) in [
        (SyntaxKind::Missing, RecoveryKind::Missing),
        (SyntaxKind::Error, RecoveryKind::Error),
    ] {
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == node_kind)
                .count(),
            all.iter()
                .filter(|record| record.kind == record_kind)
                .count(),
            "{source:?}\n{root:#?}"
        );
    }
    for (index, record) in all.iter_mut().enumerate() {
        record.id = DiagnosticId(7 + index as u32);
    }
    let replay = run(source, context, Some(&all));
    assert_eq!(replay.green, fresh.green);
    assert_eq!(replay.records, all);
    assert_same_exit(&replay.exit, &fresh.exit);
    assert_eq!(replay.completion, fresh.completion);
    assert_eq!(replay.remainder, fresh.remainder);
    assert_eq!(replay.successor, fresh.successor);
    assert_eq!(replay.slots, all.len());
    assert_eq!(replay.diagnostics, (Some(7 + all.len() as u32), all.len()));
    fresh
}

#[test]
fn primary_missing_records_name_the_immediate_slot_without_remapping_children() {
    use PatternRole::{AliasBinding as A, AlternationRhs as R, Primary as P, SymbolName as S};
    for origin in [0, 41] {
        for (source, role, at, emitted, complete) in [
            ("", P, 0, "", false),
            (" ", P, 0, "", false),
            ("A as", A, 4, "A as", false),
            (":", S, 1, ":", false),
            (": x", S, 1, ":", false),
            ("A |", R, 3, "A |", false),
            ("A | | B", R, 4, "A | | B", true),
            ("A | :", S, 5, "A | :", false),
            ("A as | B", A, 4, "A as | B", true),
        ] {
            checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[record(1, role, origin + at..origin + at, false)],
                emitted,
                if complete {
                    PatternCompletion::Complete
                } else {
                    PatternCompletion::Incomplete
                },
            );
        }
        let source = "A | @ :";
        checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[
                record(1, R, origin + 4..origin + 5, true),
                record(
                    2,
                    PatternRole::TypeAnnotation,
                    origin + 7..origin + 7,
                    false,
                ),
            ],
            source,
            PatternCompletion::Complete,
        );
    }
}

#[test]
fn primary_error_runs_exclude_retry_leading_and_keep_native_payloads() {
    for origin in [0, 41] {
        for (source, role, start, malformed, owner) in [
            ("@ x", PatternRole::Primary, 0, "@", SyntaxKind::Pattern),
            (
                "@ ? /*é*/ x",
                PatternRole::Primary,
                0,
                "@ ?",
                SyntaxKind::Pattern,
            ),
            (
                " /*é*/ @ x",
                PatternRole::Primary,
                0,
                " /*é*/ @",
                SyntaxKind::Pattern,
            ),
            (
                "A as @ x",
                PatternRole::AliasBinding,
                5,
                "@",
                SyntaxKind::PatternAliasTail,
            ),
            (
                "A as $x 1 @ x",
                PatternRole::AliasBinding,
                5,
                "$x 1 @",
                SyntaxKind::PatternAliasTail,
            ),
            (
                "A | @ ? x",
                PatternRole::AlternationRhs,
                4,
                "@ ?",
                SyntaxKind::Pattern,
            ),
            (
                "A as @\r\n  x",
                PatternRole::AliasBinding,
                5,
                "@",
                SyntaxKind::PatternAliasTail,
            ),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[record(
                    1,
                    role,
                    origin + start..origin + start + malformed.len(),
                    true,
                )],
                source,
                PatternCompletion::Complete,
            );
            assert_eq!(fresh.remainder, "");
            let root = SyntaxNode::new_root(fresh.green);
            let error = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .unwrap();
            assert_eq!(error.to_string(), malformed);
            assert_eq!(error.parent().unwrap().kind(), owner);
            let retry_gap = error.next_sibling_or_token().unwrap();
            assert!(matches!(
                retry_gap.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline
            ));
            assert_eq!(retry_gap.parent().unwrap().kind(), owner);
            if malformed == "$x 1 @" {
                assert_eq!(
                    error
                        .children_with_tokens()
                        .map(|element| element.kind())
                        .collect::<Vec<_>>(),
                    [
                        SyntaxKind::SigilIdentifier,
                        SyntaxKind::Whitespace,
                        SyntaxKind::Integer,
                        SyntaxKind::Whitespace,
                        SyntaxKind::Unknown
                    ]
                );
            }
        }
    }
}

fn assert_pending_control(run: &PatternRun<'_>, suffix: &str, origin: usize, context: Context<'_>) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = suffix;
    let current = current_item(
        In::new(&mut input, &mut recover, ()),
        origin,
        LineEntry::InLine,
        context.fence,
        |lex, leading, at, fence, _| scan_pattern_payload(lex, leading, at, fence, context.stops),
    )
    .unwrap();
    let expected = crate::handoff::complete(
        crate::handoff::handoff(current.item),
        current.next_line_entry,
    );
    assert_same_exit(&run.exit, &expected);
    assert_eq!(run.remainder, input);
    assert_eq!(run.successor, origin + suffix.len() - input.len());
}

#[test]
fn primary_and_alias_recovery_preserve_complete_caller_items_and_remaining_start() {
    for origin in [0, 41] {
        for (prefix, role, range, error) in [
            ("", PatternRole::Primary, 0..0, false),
            ("@", PatternRole::Primary, 0..1, true),
            ("A as", PatternRole::AliasBinding, 4..4, false),
            ("A as @", PatternRole::AliasBinding, 5..6, true),
            ("A |", PatternRole::AlternationRhs, 3..3, false),
            ("A | @", PatternRole::AlternationRhs, 4..5, true),
        ] {
            for suffix in [" /*é*/ )tail", "\r\n]tail", " }tail"] {
                let source = format!("{prefix}{suffix}");
                let context = Context {
                    origin,
                    closes: PatternCallerCloses::RPAREN
                        .union(PatternCallerCloses::RBRACKET)
                        .union(PatternCallerCloses::RBRACE),
                    ..Context::default()
                };
                let fresh = checked(
                    &source,
                    context,
                    &[record(
                        1,
                        role,
                        origin + range.start..origin + range.end,
                        error,
                    )],
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
            }
        }
        for emit_leading in [false, true] {
            let source = " /*é*/ =tail";
            let at = if emit_leading {
                source.find('=').unwrap()
            } else {
                0
            };
            let context = Context {
                origin,
                emit_leading,
                ..Context::default()
            };
            let fresh = checked(
                source,
                context,
                &[record(
                    1,
                    PatternRole::Primary,
                    origin + at..origin + at,
                    false,
                )],
                &source[..at],
                PatternCompletion::Incomplete,
            );
            let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = fresh.exit else {
                panic!("pending Equals")
            };
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Equals));
            assert_eq!(
                emit_pending_leading_text(&mut item),
                if emit_leading { "" } else { " /*é*/ " }
            );
        }
    }
}

#[test]
fn alias_error_retry_checks_layout_and_in_before_accepting_a_name() {
    for suffix in ["\nx", "\r\nx", " /*é*/ in tail"] {
        let source = format!("A as @{suffix}");
        let context = Context {
            stops: PATTERN_DEFAULT_STOPS | PATTERN_STOP_IN,
            ..Context::default()
        };
        let fresh = checked(
            &source,
            context,
            &[record(1, PatternRole::AliasBinding, 5..6, true)],
            "A as @",
            PatternCompletion::Incomplete,
        );
        assert_pending_control(&fresh, suffix, 6, context);
    }
    // A fresh binding and a retried same-line `as` are ordinary identifiers.
    for source in ["A as\nx", "A as\r\nx", "A as as"] {
        checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
    }
    checked(
        "A as @ as",
        Context::default(),
        &[record(1, PatternRole::AliasBinding, 5..6, true)],
        "A as @ as",
        PatternCompletion::Complete,
    );
}

#[test]
fn primary_tail_slots_preserve_quoted_fence_coordinates_before_and_after_error() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 8_000] {
        for (prefix, role, error_range) in [
            ("", PatternRole::Primary, None),
            ("@", PatternRole::Primary, Some(0..1)),
            ("A as", PatternRole::AliasBinding, None),
            ("A as @", PatternRole::AliasBinding, Some(5..6)),
            ("A |", PatternRole::AlternationRhs, None),
            ("A | @", PatternRole::AlternationRhs, Some(4..5)),
        ] {
            let suffix = "\r\n> > ```\r\nouter";
            let source = format!("{prefix}{suffix}");
            let context = Context {
                origin,
                fence: Some(&fence),
                ..Context::default()
            };
            let error = error_range.is_some();
            let range = error_range.unwrap_or(prefix.len() + 2..prefix.len() + 2);
            let fresh = checked(
                &source,
                context,
                &[record(
                    1,
                    role,
                    origin + range.start..origin + range.end,
                    error,
                )],
                prefix,
                PatternCompletion::Incomplete,
            );
            assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
            let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
                fresh.exit
            else {
                panic!("quoted fence pending")
            };
            assert_eq!(
                item.payload_view().pending_boundary().unwrap().coordinate(),
                origin + prefix.len() + 2
            );
        }
    }
}

#[test]
fn symbol_name_probe_rejection_preserves_seeded_frozen_output_and_cursor() {
    for source in ["", " x", "$x", "1", "@", "\r\n> > ```"] {
        for frozen_mode in [false, true] {
            let mut frozen = [seed_record(41)];
            frozen[0].id = DiagnosticId(7);
            let operators = OperatorTable::empty();
            let mut recover = Recover::new(&operators);
            let mut input = source;
            let mut output = if frozen_mode {
                GreenNodeBuilder::reconcile(&frozen)
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            output.token(SyntaxKind::Identifier.into(), "sentinel");
            publish_seed(&mut output, 41);
            let before = (
                output.recovery_slot_count(),
                output.diagnostic_position(),
                recover.mark(),
            );
            let mut probe: SyntaxIn = In::new(&mut input, &mut recover, &mut output);
            let name = probe.token(scan_identifier);
            assert!(name.is_none(), "{source:?}");
            assert_eq!(input.as_ptr(), source.as_ptr());
            assert_eq!(input, source);
            assert_eq!(
                (
                    output.recovery_slot_count(),
                    output.diagnostic_position(),
                    recover.mark()
                ),
                before
            );
            assert!(std::ptr::eq(recover.operators(), &operators));
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(green.to_string(), "sentinel");
            assert_eq!(
                records,
                if frozen_mode {
                    frozen.to_vec()
                } else {
                    vec![seed_record(41)]
                }
            );
            assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
        }
    }
}

#[test]
fn accepted_primary_and_tail_controls_have_no_new_recovery() {
    // Authority: Pattern primary/symbol/fixed-tail grammar and its current
    // delimiter and Type-annotation addenda, not parser success as an oracle.
    for source in [
        "x",
        "$x",
        "1",
        ":x",
        "as",
        "A as x",
        "A | B as c",
        "A as x | B",
        "()",
        "(a,b,)",
        "[a,..b]",
        "{a:b}",
        "x: T",
    ] {
        let fresh = checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
        assert_eq!(fresh.successor, source.len());
        assert!(matches!(
            fresh.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
    }
    for source in [":x", "as", "x"] {
        checked(
            source,
            Context {
                stops: PATTERN_STOP_COLON,
                ..Context::default()
            },
            &[],
            source,
            PatternCompletion::Complete,
        );
    }
}
