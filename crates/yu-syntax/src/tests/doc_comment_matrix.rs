//! Gate-7 public doc-comment/Yumark matrix.
//!
//! Every parser invocation in this module enters through `parse_file`; the
//! isolated Yumark adapters are never called directly. Form rows compare the
//! exact direct children of every doc/Yumark/recovery node in preorder.

use std::sync::Arc;

use crate::{
    SourceText, StructuralRecoveryKind, SyntaxEnvironment, SyntaxKind, SyntaxNode,
    yumark::adapter::{public_byte_visits, reset_public_byte_visits},
};

#[derive(Debug, Eq, PartialEq)]
struct DirectTopology {
    owner: SyntaxKind,
    children: Vec<SyntaxKind>,
}

#[derive(Clone, Copy)]
struct ExpectedTopology {
    owner: SyntaxKind,
    children: &'static [SyntaxKind],
}

#[derive(Clone, Copy)]
struct RecoveryFact {
    kind: StructuralRecoveryKind,
    range: RangeSpec,
}

#[derive(Clone, Copy)]
enum RangeSpec {
    Eof,
    At(usize),
    Span(usize, usize),
    Before(&'static str),
}

fn parse(source: &str) -> crate::ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    crate::parse_file(
        Arc::clone(&source),
        Arc::new(crate::scan_header(Arc::clone(&source))),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn is_designed_owner(kind: SyntaxKind) -> bool {
    let name = format!("{kind:?}");
    matches!(
        kind,
        SyntaxKind::DocCommentDeclaration
            | SyntaxKind::Missing
            | SyntaxKind::Error
            | SyntaxKind::Invalid
    ) || name.starts_with("Ym")
}

fn direct_topology(root: &SyntaxNode) -> Vec<DirectTopology> {
    root.descendants()
        .filter(|node| is_designed_owner(node.kind()))
        .map(|node| DirectTopology {
            owner: node.kind(),
            children: node
                .children_with_tokens()
                .map(|child| child.kind())
                .collect(),
        })
        .collect()
}

fn assert_public_form(
    name: &str,
    source: &str,
    expected: &[ExpectedTopology],
    expected_recoveries: &[RecoveryFact],
) -> crate::ParsedFile {
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source, "{name}: lossless");
    let root = SyntaxNode::new_root(parsed.green().clone());
    let expected = expected
        .iter()
        .map(|row| DirectTopology {
            owner: row.owner,
            children: row.children.to_vec(),
        })
        .collect::<Vec<_>>();
    assert_eq!(direct_topology(&root), expected, "{name}: direct topology");
    assert_recoveries(name, source, &parsed, expected_recoveries);
    parsed
}

fn assert_recoveries(
    name: &str,
    source: &str,
    parsed: &crate::ParsedFile,
    expected: &[RecoveryFact],
) {
    let expected = expected
        .iter()
        .map(|fact| {
            let range = match fact.range {
                RangeSpec::Eof => source.len()..source.len(),
                RangeSpec::At(at) => at..at,
                RangeSpec::Span(start, end) => start..end,
                RangeSpec::Before(spelling) => {
                    let at = source.find(spelling).expect("range locator");
                    at..at
                }
            };
            (fact.kind, range)
        })
        .collect::<Vec<_>>();
    let actual = parsed
        .structural_recoveries()
        .into_iter()
        .map(|fact| {
            assert_eq!(fact.path().first(), Some(&SyntaxKind::Root), "{name}");
            assert!(
                fact.path().contains(&SyntaxKind::DocCommentDeclaration),
                "{name}: recovery escaped the doc declaration: {:?}",
                fact.path()
            );
            (fact.kind(), fact.range().clone())
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected, "{name}: recovery facts");
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

macro_rules! t {
    ($owner:ident => [$($child:ident),* $(,)?]) => {
        ExpectedTopology {
            owner: SyntaxKind::$owner,
            children: &[$(SyntaxKind::$child),*],
        }
    };
}

macro_rules! missing {
    (eof) => {
        RecoveryFact {
            kind: StructuralRecoveryKind::Missing,
            range: RangeSpec::Eof,
        }
    };
    ($at:expr) => {
        RecoveryFact {
            kind: StructuralRecoveryKind::Missing,
            range: RangeSpec::At($at),
        }
    };
}

macro_rules! error {
    ($start:expr, $end:expr) => {
        RecoveryFact {
            kind: StructuralRecoveryKind::RawError,
            range: RangeSpec::Span($start, $end),
        }
    };
}

macro_rules! missing_before {
    ($spelling:expr) => {
        RecoveryFact {
            kind: StructuralRecoveryKind::Missing,
            range: RangeSpec::Before($spelling),
        }
    };
}

#[test]
fn public_line_doc_matrix_has_exact_direct_topology() {
    let empty = [
        t!(DocCommentDeclaration => [DocLinePrefix, YmDoc]),
        t!(YmDoc => []),
    ];
    for (name, source) in [
        ("empty-lf", "--\n"),
        ("empty-crlf", "--\r\n"),
        ("empty-eof", "--"),
    ] {
        assert_public_form(name, source, &empty, &[]);
    }

    let text = [
        t!(DocCommentDeclaration => [DocLinePrefix, YmDoc]),
        t!(YmDoc => [YmText]),
    ];
    for (name, source) in [
        ("text-eof", "--text"),
        ("text-lf", "--text\n"),
        ("text-crlf", "--text\r\n"),
    ] {
        assert_public_form(name, source, &text, &[]);
    }

    let inline = [
        t!(DocCommentDeclaration => [DocLinePrefix, YmDoc]),
        t!(YmDoc => [YmEmphasis, YmText, YmStrong, YmText, YmInlineGroup, YmText, YmInlineLink, YmText, YmInlineImage, YmText, YmInlineApply, YmText, YmInlineRef]),
        t!(YmEmphasis => [YmEmphasisMarker, YmDoc, YmEmphasisMarker]),
        t!(YmDoc => [YmText]),
        t!(YmStrong => [YmStrongMarker, YmDoc, YmStrongMarker]),
        t!(YmDoc => [YmText]),
        t!(YmInlineGroup => [LBracket, YmDoc, RBracket]),
        t!(YmDoc => [YmText]),
        t!(YmInlineLink => [LBracket, YmDoc, RBracket, LParen, YmText, RParen]),
        t!(YmDoc => [YmText]),
        t!(YmInlineImage => [YmBangLBracket, YmDoc, RBracket, LParen, YmText, RParen]),
        t!(YmDoc => [YmText]),
        t!(YmInlineApply => [LBracket, YmDoc, RBracket, Colon, YmInlineApplyHead]),
        t!(YmDoc => [YmText]),
        t!(YmInlineApplyHead => [Identifier]),
        t!(YmInlineRef => [YmBackslash, Identifier, Semicolon]),
    ];
    assert_public_form(
        "all-inline-forms",
        "--*e* **s** [g] [l](d) ![i](s) [a]:op \\ref;\n",
        &inline,
        &[],
    );
}

#[test]
fn public_block_form_matrix_has_exact_direct_topology() {
    assert_public_form(
        "empty-block",
        "---\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => []),
        ],
        &[],
    );
    assert_public_form(
        "implicit-section",
        "---\n# H\nbody\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmSection]),
            t!(YmSection => [YmImplicitSection]),
            t!(YmImplicitSection => [YmHeading, Newline, YmDoc]),
            t!(YmHeading => [YmHeadingMarker, Whitespace, YmText]),
            t!(YmDoc => [YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "explicit-section",
        "---\n# H:\n  body\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmSection]),
            t!(YmSection => [YmExplicitSection]),
            t!(YmExplicitSection => [YmHeading, Newline, YmDoc]),
            t!(YmHeading => [YmHeadingMarker, Whitespace, YmText, Colon]),
            t!(YmDoc => [Whitespace, YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "valid-empty-heading",
        "---\n# \n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmSection]),
            t!(YmSection => [YmImplicitSection]),
            t!(YmImplicitSection => [YmHeading, Newline, YmDoc]),
            t!(YmHeading => [YmHeadingMarker, Whitespace]),
            t!(YmDoc => []),
        ],
        &[],
    );
    assert_public_form(
        "list-siblings",
        "---\n- one\n- two\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmList]),
            t!(YmList => [YmListItem, YmListItem]),
            t!(YmListItem => [YmListMarker, YmListItemBody]),
            t!(YmListItemBody => [YmDoc]),
            t!(YmDoc => [YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
            t!(YmListItem => [YmListMarker, YmListItemBody]),
            t!(YmListItemBody => [YmDoc]),
            t!(YmDoc => [YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "prefix-quote",
        "---\n> one\n> two\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmQuoteBlock]),
            t!(YmQuoteBlock => [YmDoc]),
            t!(YmDoc => [YmQuotePrefix, YmParagraph, Newline, YmQuotePrefix, YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "explicit-quote",
        "---\n>>>\nbody\n>>>\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmQuoteBlock, Newline]),
            t!(YmQuoteBlock => [YmQuoteFenceMarker, YmDoc, YmQuoteFenceMarker]),
            t!(YmDoc => [Newline, YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "paragraph-and-blank-line",
        "---\none\n\ntwo\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmParagraph, Newline, YmBlankLine, YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
            t!(YmBlankLine => [Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "raw-fence",
        "---\n```rust\nraw\n```\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmCodeFence, Newline]),
            t!(YmCodeFence => [YmFenceMarker, YmCodeFenceInfo, Newline, YmCodeFenceText, YmFenceMarker]),
            t!(YmCodeFenceInfo => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "selected-yulang-boundary-only",
        "---\n```yulang\n```\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmCodeFence, Newline]),
            t!(YmCodeFence => [YmFenceMarker, YmCodeFenceInfo, Newline, YmFenceMarker]),
            t!(YmCodeFenceInfo => [YmText]),
        ],
        &[],
    );

    let source = "---\n  - item\n next\nparent\n---\n";
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert_recoveries("list-middle-indentation-return", source, &parsed, &[]);
    let root = SyntaxNode::new_root(parsed.green().clone());
    let returned = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::YmText && token.text() == "next")
        .expect("middle-indented line returns to the parent document");
    assert!(
        !returned
            .parent()
            .expect("Yumark text has a parent")
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmList)
    );
}

#[test]
fn public_command_and_special_form_matrix_has_exact_direct_topology() {
    assert_public_form(
        "general-command-all-arguments",
        "---\n\\cmd(x)[doc]{body}\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmCommand]),
            t!(YmCommand => [YmBackslash, Identifier, YmCommandArgs, YmCommandBody, Newline]),
            t!(YmCommandArgs => [YmYulangArgs, YmDocArg]),
            t!(YmYulangArgs => [LParen, OperatorChain, RParen]),
            t!(YmDocArg => [LBracket, YmDoc, RBracket]),
            t!(YmDoc => [YmText]),
            t!(YmCommandBody => [LBrace, YmDoc, RBrace]),
            t!(YmDoc => [YmParagraph]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "my-bare-inline-expression",
        "---\n\\my f x = value;\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmMy]),
            t!(YmMy => [YmBackslash, Identifier, YmMyBindingHead, YmMyExpressionBody]),
            t!(YmMyBindingHead => [Whitespace, Pattern, Whitespace]),
            t!(YmMyExpressionBody => [Equals, Whitespace, OperatorChain, Semicolon, Newline]),
        ],
        &[],
    );
    assert_public_form(
        "use-bare",
        "---\n\\use std::io;\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmUse, Newline]),
            t!(YmUse => [YmBackslash, Identifier, Whitespace, UseTree, Semicolon]),
        ],
        &[],
    );
    assert_public_form(
        "blank-tolerant-if-chain",
        "---\n\\if(a){one}\n\n\\elsif(b){two}\n\\else{three}\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmIfChain]),
            t!(YmIfChain => [YmBackslash, Identifier, YmIf, YmBlankLine, YmBackslash, Identifier, YmElsif, YmBackslash, Identifier, YmElse]),
            t!(YmIf => [YmIfCondition, YmCommandBody, Newline]),
            t!(YmIfCondition => [LParen, OperatorChain, RParen]),
            t!(YmCommandBody => [LBrace, YmDoc, RBrace]),
            t!(YmDoc => [YmParagraph]),
            t!(YmParagraph => [YmText]),
            t!(YmBlankLine => [Newline]),
            t!(YmElsif => [YmElsifCondition, YmCommandBody, Newline]),
            t!(YmElsifCondition => [LParen, OperatorChain, RParen]),
            t!(YmCommandBody => [LBrace, YmDoc, RBrace]),
            t!(YmDoc => [YmParagraph]),
            t!(YmParagraph => [YmText]),
            t!(YmElse => [YmCommandBody, Newline]),
            t!(YmCommandBody => [LBrace, YmDoc, RBrace]),
            t!(YmDoc => [YmParagraph]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );
    assert_public_form(
        "sole-do-capture",
        "---\n\\wrap(do)\nafter\n---\n",
        &[
            t!(DocCommentDeclaration => [DocBlockOpen, Newline, YmDoc, DocBlockClose]),
            t!(YmDoc => [YmCommand]),
            t!(YmCommand => [YmBackslash, Identifier, YmCommandArgs, Newline, YmDoCapture]),
            t!(YmCommandArgs => [LParen, Identifier, RParen]),
            t!(YmDoCapture => [YmDoc]),
            t!(YmDoc => [YmParagraph, Newline]),
            t!(YmParagraph => [YmText]),
        ],
        &[],
    );

    for (name, source, required) in [
        (
            "inline-reference-arguments",
            "--\\ref((x));",
            &[SyntaxKind::YmInlineRef, SyntaxKind::YmYulangArgs][..],
        ),
        (
            "inline-apply-arguments",
            "--[d]:f(g(x))",
            &[SyntaxKind::YmInlineApply, SyntaxKind::YmInlineApplyArgs][..],
        ),
        (
            "general-immediate-doc",
            "---\n\\cmd[doc]\n---",
            &[SyntaxKind::YmCommand, SyntaxKind::YmDocArg][..],
        ),
        (
            "general-indented-body",
            "---\n\\cmd:\n  body\n---",
            &[SyntaxKind::YmCommand, SyntaxKind::YmCommandBody][..],
        ),
        (
            "my-parenthesized-braced",
            "---\n\\my(f x){body}\n---",
            &[SyntaxKind::YmMyBindingHead, SyntaxKind::YmCommandBody][..],
        ),
        (
            "my-indented-expression",
            "---\n\\my f =\n  value\n---",
            &[SyntaxKind::YmMyExpressionBody, SyntaxKind::OperatorChain][..],
        ),
        (
            "my-indented-doc",
            "---\n\\my f:\n  body\n---",
            &[SyntaxKind::YmMyBindingHead, SyntaxKind::YmCommandBody][..],
        ),
        (
            "use-parenthesized",
            "---\n\\use(std::io)\n---",
            &[SyntaxKind::YmUse, SyntaxKind::UseTree][..],
        ),
        (
            "do-with-local-body",
            "---\n\\wrap(do){local}\nafter\n---",
            &[SyntaxKind::YmCommandBody, SyntaxKind::YmDoCapture][..],
        ),
        (
            "nested-do",
            "---\n\\outer(do)\n\\inner(do)\nafter\n---",
            &[SyntaxKind::YmDoCapture, SyntaxKind::YmCommand][..],
        ),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{name}");
        assert_recoveries(name, source, &parsed, &[]);
        let root = SyntaxNode::new_root(parsed.green().clone());
        for kind in required {
            assert!(count(&root, *kind) > 0, "{name}: missing {kind:?}");
        }
        assert_eq!(
            count(&root, SyntaxKind::Root),
            1,
            "{name}: nested public Root"
        );
    }
}

#[test]
fn public_recovery_matrix_covers_every_yumark_recovery_class() {
    let rows: &[(&str, &str, &[RecoveryFact])] = &[
        ("block-doc-eof", "---\nbody", &[missing!(eof)]),
        (
            "raw-fence-and-doc-eof",
            "---\n```txt\nbody",
            &[missing!(eof), missing!(eof)],
        ),
        ("emphasis-close", "--*open", &[missing!(eof)]),
        ("strong-close", "--**open", &[missing!(eof)]),
        ("group-close", "--[open", &[missing!(eof)]),
        ("link-close", "--[x](dest", &[missing!(eof)]),
        ("image-close", "--![x](dest", &[missing!(eof)]),
        ("image-destination", "--![x]tail", &[missing!(6)]),
        ("section-body", "---\n# H:\nnext\n---", &[missing!(9)]),
        (
            "command-indented-body",
            "---\n\\cmd:\nnext\n---",
            &[missing!(10)],
        ),
        (
            "command-braced-close",
            "---\n\\cmd{body\n---",
            &[missing!(14)],
        ),
        (
            "my-indented-body",
            "---\n\\my f:\nnext\n---",
            &[missing_before!("next")],
        ),
        (
            "if-indented-body",
            "---\n\\if(x):\nnext\n---",
            &[missing_before!("next")],
        ),
        (
            "elsif-indented-body",
            "---\n\\if(x){ok}\n\\elsif(y):\nnext\n---",
            &[missing_before!("next")],
        ),
        (
            "else-indented-body",
            "---\n\\if(x){ok}\n\\else:\nnext\n---",
            &[missing_before!("next")],
        ),
        ("my-braced-close", "---\n\\my f {body\n---", &[missing!(16)]),
        ("if-braced-close", "---\n\\if(x){body\n---", &[missing!(16)]),
        (
            "elsif-braced-close",
            "---\n\\if(x){ok}\n\\elsif(y){body\n---",
            &[missing!(30)],
        ),
        (
            "else-braced-close",
            "---\n\\if(x){ok}\n\\else{body\n---",
            &[missing!(26)],
        ),
        ("reference-arguments-close", "--\\ref(x", &[missing!(eof)]),
        ("apply-arguments-close", "--[d]:f(x", &[missing!(eof)]),
        ("doc-argument-close", "---\n\\cmd[doc\n---", &[missing!(12)]),
        ("embedded-index-item", "--\\ref(x[,a])", &[missing!(9)]),
        (
            "my-head-and-expression",
            "---\n\\my =\n---",
            &[missing!(8), missing!(10)],
        ),
        ("my-body-introducer", "---\n\\my f\n---", &[missing!(9)]),
        ("my-expression-body", "---\n\\my f =;\n---", &[missing!(11)]),
        ("my-terminator", "---\n\\my f = x\n---", &[missing!(13)]),
        (
            "my-parenthesized-head-close",
            "---\n\\my(f = value;\n---",
            &[missing_before!("=")],
        ),
        ("use-empty-route", "---\n\\use()\n---", &[missing!(9)]),
        (
            "use-empty-open",
            "---\n\\use(\n---",
            &[missing!(9), missing!(9)],
        ),
        (
            "use-missing-close",
            "---\n\\use(route\n---",
            &[missing!(14)],
        ),
        ("use-bare-empty", "---\n\\use ;\n---", &[missing!(9)]),
        ("use-at-boundary", "---\n\\use\n---", &[missing!(8)]),
        ("use-terminator", "---\n\\use route\n---", &[missing!(14)]),
        ("if-empty-condition", "---\n\\if(){x}\n---", &[missing!(8)]),
        ("if-condition-close", "---\n\\if(x{x}\n---", &[missing!(9)]),
        (
            "else-condition-and-orphan",
            "---\n\\else(x){body}\n---",
            &[error!(4, 9), error!(9, 12)],
        ),
        ("do-close", "---\n\\wrap(do\n---", &[missing!(12)]),
        (
            "do-trailing-horizontal",
            "---\n\\wrap(do )\n---",
            &[error!(12, 13)],
        ),
        (
            "do-trailing-horizontal-open",
            "---\n\\wrap(do \n---",
            &[error!(12, 13), missing!(13)],
        ),
        ("do-mixed", "---\n\\wrap(do x)\n---", &[error!(12, 14)]),
        (
            "do-mixed-open",
            "---\n\\wrap(do x\n---",
            &[error!(12, 14), missing!(14)],
        ),
        (
            "orphan-elsif",
            "---\n\\elsif(x){body}\n---",
            &[error!(4, 10)],
        ),
        ("orphan-else", "---\n\\else{body}\n---", &[error!(4, 9)]),
        (
            "explicit-quote-eof",
            "---\n>>>\nbody",
            &[missing!(eof), missing!(eof)],
        ),
        (
            "mixed-quote-form",
            "---\n>>>\n> mixed\n>>>\n---",
            &[error!(8, 10)],
        ),
    ];

    for (name, source, expected) in rows {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), *source, "{name}: lossless");
        assert_recoveries(name, source, &parsed, expected);
        let root = SyntaxNode::new_root(parsed.green().clone());
        let recovery_nodes = root
            .descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .collect::<Vec<_>>();
        assert_eq!(recovery_nodes.len(), expected.len(), "{name}: direct nodes");
        for (node, fact) in recovery_nodes.into_iter().zip(*expected) {
            let expected_kind = match fact.kind {
                StructuralRecoveryKind::Missing => SyntaxKind::Missing,
                StructuralRecoveryKind::RawError => SyntaxKind::Error,
                StructuralRecoveryKind::Invalid => SyntaxKind::Invalid,
            };
            assert_eq!(node.kind(), expected_kind, "{name}: recovery topology");
            assert!(node.parent().is_some(), "{name}: detached recovery node");
        }
    }
}

#[test]
fn public_marker_text_remainder_and_statement_topology_matrix() {
    for source in ["---x\n", "----\n", "  ---\n", "value; -- same line\n"] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source);
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            0,
            "{source:?}"
        );
    }

    let source = "---\n---x\n----\n  ---\n---\n";
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert_recoveries("close-like markers stay text", source, &parsed, &[]);
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::DocBlockClose)
            .count(),
        1
    );
    let text = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::YmText)
        .map(|token| token.text().to_owned())
        .collect::<String>();
    assert!(text.contains("---x"));
    assert!(text.contains("----"));
    assert!(text.contains("---"));

    let source = "---\nbody\n---  \r\nmy after = 1\n";
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert_recoveries("close suffix remainder", source, &parsed, &[]);
    let root = SyntaxNode::new_root(parsed.green().clone());
    let doc = root
        .children()
        .find(|node| node.kind() == SyntaxKind::DocCommentDeclaration)
        .expect("root doc");
    assert_eq!(doc.to_string(), "---\nbody\n---");
    assert!(
        root.children()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );

    for (name, source, ancestor) in [
        ("root", "-- root\n", SyntaxKind::Root),
        (
            "braced",
            "{ -- braced\nvalue }",
            SyntaxKind::BracedStatementBlockExpression,
        ),
        (
            "indented",
            "if condition:\n  -- indented\n  value\n",
            SyntaxKind::IndentedStatementBlock,
        ),
        ("inline", "mod M: -- inline\n", SyntaxKind::ModDeclaration),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{name}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        let doc = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::DocCommentDeclaration)
            .expect("doc declaration");
        assert!(
            doc.ancestors().any(|node| node.kind() == ancestor),
            "{name}: missing {ancestor:?} ancestor"
        );
    }
}

fn parse_deep(name: &str, body: String, expected_kind: SyntaxKind, expected_count: usize) {
    let source = format!("---\n{body}---\n");
    reset_public_byte_visits();
    let parsed = parse(&source);
    let public_root = parsed.source_root();
    drop(parsed);
    let root = public_root.syntax();
    let lossless = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| token.text().to_owned())
        .collect::<String>();
    assert_eq!(lossless, source, "{name}: lossless token walk");
    assert_eq!(
        root.descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .count(),
        0,
        "{name}: recovery-free"
    );
    assert_eq!(
        public_byte_visits(),
        body.len(),
        "{name}: one visit per Yumark body byte"
    );
    assert_eq!(count(root, expected_kind), expected_count, "{name}");
}

#[test]
fn public_deep_frame_matrix_is_iterative_and_linear() {
    const DEPTH: usize = 10_000;

    let mut sections = String::new();
    for level in 1..=DEPTH {
        sections.extend(std::iter::repeat_n('#', level));
        sections.push_str(" h\n");
    }
    parse_deep("sections", sections, SyntaxKind::YmSection, DEPTH);

    let mut lists = String::new();
    for depth in 0..DEPTH {
        lists.extend(std::iter::repeat_n(' ', depth * 2));
        lists.push_str("- x\n");
    }
    parse_deep("lists", lists, SyntaxKind::YmList, DEPTH);

    let mut quotes = String::new();
    for depth in 1..=DEPTH {
        quotes.extend(std::iter::repeat_n('>', depth));
        quotes.push_str(" x\n");
    }
    parse_deep("quotes", quotes, SyntaxKind::YmQuoteBlock, DEPTH);

    parse_deep(
        "groups",
        format!("{}x{}\n", "[".repeat(DEPTH), "]".repeat(DEPTH)),
        SyntaxKind::YmInlineGroup,
        DEPTH,
    );
    parse_deep(
        "commands",
        format!("{}x{}\n", "\\c{".repeat(DEPTH), "}".repeat(DEPTH)),
        SyntaxKind::YmCommand,
        DEPTH,
    );
}
