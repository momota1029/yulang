use super::*;
use crate::rewrite::operator_header::{next_item, operator_header_normalized};
use crate::{OperatorFixity, Visibility};
use std::sync::Arc;

#[test]
fn complete_operator_header_projects_without_reading_its_body() {
    let operators = OperatorTable::empty();
    for (source, fixity, lazy, visibility, end) in [
        (
            "infix (<+>) 50 51 = \"body\"",
            OperatorFixity::Infix,
            false,
            Visibility::Private,
            19,
        ),
        (
            "pub lazy prefix (!) 70.2 = body",
            OperatorFixity::Prefix,
            true,
            Visibility::Public,
            26,
        ),
        (
            "nullfix (?) = body",
            OperatorFixity::Nullfix,
            false,
            Visibility::Private,
            13,
        ),
    ] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let mut i = In::new(&mut input, &mut recover, &mut output);
        let (item, origin, line) = i
            .token(|lex| Some(next_item(lex, 0, LineEntry::InLine, None)))
            .unwrap();
        let (pending, origin, _, fact) = operator_header_normalized(i, item, origin, line, None);
        assert!(pending.is_none());
        let fact = fact.unwrap();
        assert_eq!(fact.fixity(), fixity);
        assert_eq!(fact.is_lazy(), lazy);
        assert_eq!(fact.visibility(), visibility);
        assert_eq!(fact.range(), &(0..end));
        assert_eq!(origin, end);
        assert_eq!(input, &source[end..]);
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), source[..end]);
        assert!(records.is_empty());
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.text() == "=")
                .unwrap()
                .kind(),
            SyntaxKind::Equals
        );
    }
}

fn header_record(
    id: u32,
    role: crate::session::OperatorHeaderRole,
    kind: crate::session::RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::session::*;
    let expected = match role {
        OperatorHeaderRole::Name => ExpectedSyntax::OperatorName,
        OperatorHeaderRole::DefinitionIntroducer => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Equals)
        }
        _ => ExpectedSyntax::BindingPower,
    };
    let role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected: if kind == RecoveryKind::Error {
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

#[test]
fn structural_safe_points_and_equals_keep_exact_frozen_records_and_body_suffix() {
    use crate::session::{OperatorHeaderRole as R, RecoveryKind as K};
    for (source, owned, pending_text, pending_range, rest, expected) in [
        (
            "prefix (!) 128 = body",
            "prefix (!) 128 =",
            None,
            None,
            " body",
            vec![header_record(0, R::RightBindingPower, K::Error, 111..114)],
        ),
        (
            "suffix (!) 128 body + tail",
            "suffix (!) 128",
            Some("body"),
            Some(114..119),
            " + tail",
            vec![
                header_record(0, R::LeftBindingPower, K::Error, 111..114),
                header_record(1, R::DefinitionIntroducer, K::Missing, 114..114),
            ],
        ),
        (
            "suffix (!) body + tail",
            "suffix (!)",
            Some("body"),
            Some(110..115),
            " + tail",
            vec![
                header_record(0, R::LeftBindingPower, K::Missing, 110..110),
                header_record(1, R::DefinitionIntroducer, K::Missing, 110..110),
            ],
        ),
        (
            "prefix (!) (body) + tail",
            "prefix (!)",
            Some("("),
            Some(110..112),
            "body) + tail",
            vec![
                header_record(0, R::RightBindingPower, K::Missing, 110..110),
                header_record(1, R::DefinitionIntroducer, K::Missing, 110..110),
            ],
        ),
        (
            "prefix (!) @ \"body\" + tail",
            "prefix (!) @",
            Some("\""),
            Some(112..114),
            "body\" + tail",
            vec![
                header_record(0, R::RightBindingPower, K::Error, 111..112),
                header_record(1, R::DefinitionIntroducer, K::Missing, 112..112),
            ],
        ),
        (
            "prefix 70 = body",
            "prefix 70 =",
            None,
            None,
            " body",
            vec![header_record(0, R::Name, K::Missing, 106..106)],
        ),
        (
            "prefix = body",
            "prefix =",
            None,
            None,
            " body",
            vec![
                header_record(0, R::Name, K::Missing, 106..106),
                header_record(1, R::RightBindingPower, K::Missing, 106..106),
            ],
        ),
        (
            "prefix (!) body + tail",
            "prefix (!)",
            Some("body"),
            Some(110..115),
            " + tail",
            vec![
                header_record(0, R::RightBindingPower, K::Missing, 110..110),
                header_record(1, R::DefinitionIntroducer, K::Missing, 110..110),
            ],
        ),
        (
            "prefix (!)70 = body",
            "prefix (!)70 =",
            None,
            None,
            " body",
            vec![header_record(0, R::RightBindingPower, K::Error, 110..112)],
        ),
        (
            "nullfix (?) == body + tail",
            "nullfix (?) ==",
            Some("body"),
            Some(114..119),
            " + tail",
            vec![header_record(
                0,
                R::DefinitionIntroducer,
                K::Error,
                112..114,
            )],
        ),
        (
            "prefix (⊕) 70 身体 + tail",
            "prefix (⊕) 70",
            Some("身体"),
            Some(115..122),
            " + tail",
            vec![header_record(
                0,
                R::DefinitionIntroducer,
                K::Missing,
                115..115,
            )],
        ),
        (
            "prefix (!)\r\nbody + tail",
            "prefix (!)",
            Some("body"),
            Some(110..116),
            " + tail",
            vec![
                header_record(0, R::RightBindingPower, K::Missing, 110..110),
                header_record(1, R::DefinitionIntroducer, K::Missing, 110..110),
            ],
        ),
    ] {
        for replay in [false, true] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new(&operators);
            let mut input = source;
            let mut output = if replay {
                GreenNodeBuilder::reconcile_scoped(&expected)
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            let (pending, origin, line, fact) = {
                let mut scope = output.header_reconciliation_scope();
                let mut i = In::new(&mut input, &mut recover, &mut *scope);
                let (item, origin, line) = i
                    .token(|lex| Some(next_item(lex, 100, LineEntry::InLine, None)))
                    .unwrap();
                operator_header_normalized(i, item, origin, line, None)
            };
            assert!(fact.is_none(), "{source}");
            assert_eq!(
                pending
                    .as_ref()
                    .and_then(|item| item.payload_view().spelling()),
                pending_text,
                "{source}"
            );
            assert_eq!(
                pending
                    .as_ref()
                    .map(|item| item.extent(origin).recovery_range()),
                pending_range,
                "{source}"
            );
            assert_eq!(line, LineEntry::InLine);
            assert_eq!(input, rest, "{source}");
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(green.to_string(), owned, "{source}");
            assert_eq!(records, expected, "{source}");
        }
    }
}

#[test]
fn malformed_fixity_retry_keeps_typed_record_and_frozen_identity() {
    let source = "lazy @ infix (<+>) 50 51 = body";
    let operators = OperatorTable::empty();
    let mut frozen = Vec::new();
    for replay in [false, true] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = if replay {
            GreenNodeBuilder::reconcile_scoped(&frozen)
        } else {
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        let result = {
            let mut scope = output.header_reconciliation_scope();
            let mut i = In::new(&mut input, &mut recover, &mut *scope);
            let (item, origin, line) = i
                .token(|lex| Some(next_item(lex, 0, LineEntry::InLine, None)))
                .unwrap();
            operator_header_normalized(i, item, origin, line, None)
        };
        assert!(result.3.is_some());
        assert_eq!(input, " body");
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), "lazy @ infix (<+>) 50 51 =");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].site.range, 5..6);
        assert_eq!(records[0].expectations.len(), 4);
        use crate::session::{ExpectedSyntax, KeywordEvidence};
        assert_eq!(
            records[0]
                .expectations
                .iter()
                .map(|entry| entry.expected.clone())
                .collect::<Vec<_>>(),
            [
                KeywordEvidence::Prefix,
                KeywordEvidence::Infix,
                KeywordEvidence::Suffix,
                KeywordEvidence::Nullfix
            ]
            .map(ExpectedSyntax::Keyword)
        );
        assert_eq!(records[0].primary_expectation, 0);
        if replay {
            assert_eq!(records, frozen);
        } else {
            frozen = records;
        }
    }
}

#[test]
fn missing_header_slots_preserve_the_next_crlf_statement() {
    let operators = OperatorTable::empty();
    let source = "prefix (!)\r\nuse std::io";
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut input, &mut recover, &mut output);
    let (item, origin, line) = i
        .token(|lex| Some(next_item(lex, 0, LineEntry::InLine, None)))
        .unwrap();
    let (pending, origin, _, fact) = operator_header_normalized(i, item, origin, line, None);
    assert!(fact.is_none());
    let pending = pending.unwrap();
    assert_eq!(pending.payload_view().spelling(), Some("use"));
    assert_eq!(pending.extent(origin).recovery_range(), 10..15);
    assert_eq!(input, " std::io");
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "prefix (!)");
    assert_eq!(records.len(), 2);
    assert!(records.iter().all(|record| record.site.range == (10..10)));
}

#[test]
fn quoted_fence_keeps_pending_crlf_and_anchors_at_abstract_coordinate() {
    use crate::rewrite::yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy};
    use crate::session::{OperatorHeaderRole as R, RecoveryKind as K};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (owned, expected) in [
        (
            "prefix (!)",
            vec![
                header_record(0, R::RightBindingPower, K::Missing, 112..112),
                header_record(1, R::DefinitionIntroducer, K::Missing, 112..112),
            ],
        ),
        (
            "prefix (!) @",
            vec![
                header_record(0, R::RightBindingPower, K::Error, 111..112),
                header_record(1, R::DefinitionIntroducer, K::Missing, 114..114),
            ],
        ),
    ] {
        let source = format!("{owned}\r\n> > ```\r\nouter");
        for replay in [false, true] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new(&operators);
            let mut input = source.as_str();
            let mut output = if replay {
                GreenNodeBuilder::reconcile_scoped(&expected)
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            let (pending, _, line, fact) = {
                let mut scope = output.header_reconciliation_scope();
                let mut i = In::new(&mut input, &mut recover, &mut *scope);
                let (item, origin, line) = i
                    .token(|lex| Some(next_item(lex, 100, LineEntry::InLine, Some(&fence))))
                    .unwrap();
                operator_header_normalized(i, item, origin, line, Some(&fence))
            };
            assert!(fact.is_none());
            assert_eq!(line, LineEntry::PhysicalStart);
            assert_eq!(input, "> > ```\r\nouter");
            let (leading, boundary) = emit_terminal_leading_text(pending.unwrap());
            assert_eq!(leading, "\r\n");
            assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(green.to_string(), owned);
            assert_eq!(records, expected);
        }
    }
}
