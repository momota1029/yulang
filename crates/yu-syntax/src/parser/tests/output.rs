use chasa_recover::In;
use rowan::GreenNode;

use crate::{SyntaxKind, SyntaxNode, operator::OperatorTable};

use crate::parser::tests::pattern::pattern_literal_witness;
use crate::parser::tests::support::{
    run_act_declaration, run_cast_declaration, run_declaration_companion, run_declaration_variant,
    run_enum_declaration, run_error_declaration, run_impl_declaration, run_normalized,
    run_role_declaration, run_type_normalized,
};
use crate::parser::{
    context::state::Recover,
    declaration::declaration_variant::VariantSequenceForm,
    expression::expr,
    input::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, Payload, Token, TokenKind},
        yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy},
    },
    output::ParserOutput,
    statement::classify_statement_item_normalized,
    type_expr::type_expr,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OptionEntryEvidence {
    FocusedRejection,
    SourceOnlyOrLexicallyTransactional,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OptionEntryAudit {
    source: &'static str,
    procedure: &'static str,
    evidence: OptionEntryEvidence,
}

const OPTION_PARSER_IN_AUDIT: [OptionEntryAudit; 23] = [
    OptionEntryAudit {
        source: "declaration/declaration_companion.rs",
        procedure: "declaration_companion_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "statement.rs",
        procedure: "classify_statement_item_normalized",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/declaration_variant.rs",
        procedure: "declaration_variant_sequence_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/cast_decl.rs",
        procedure: "cast_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/enum_decl.rs",
        procedure: "enum_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/enum_decl.rs",
        procedure: "parameter_item_normalized",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "declaration/impl_decl.rs",
        procedure: "impl_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/act_decl.rs",
        procedure: "act_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/role_decl.rs",
        procedure: "role_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "expression/if_expr.rs",
        procedure: "arm_keyword",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "expression/if_expr.rs",
        procedure: "active_statement_companion",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "expression/mod.rs",
        procedure: "expr",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "expression/mod.rs",
        procedure: "expr_normalized",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "expression/mod.rs",
        procedure: "optional_nud_item",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "declaration/type_decl.rs",
        procedure: "parameter_item_normalized",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "type_expr.rs",
        procedure: "type_expr",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "type_expr.rs",
        procedure: "type_expr_normalized",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "pattern/literal.rs",
        procedure: "pattern_literal_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/error_decl.rs",
        procedure: "error_declaration_witness",
        evidence: OptionEntryEvidence::FocusedRejection,
    },
    OptionEntryAudit {
        source: "declaration/error_decl.rs",
        procedure: "parameter_item_normalized",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "input/lexer.rs",
        procedure: "introduced_body_indentation",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "input/lexer.rs",
        procedure: "introduced_body_indentation_normalized",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
    OptionEntryAudit {
        source: "expression/case_like.rs",
        procedure: "guard_kind",
        evidence: OptionEntryEvidence::SourceOnlyOrLexicallyTransactional,
    },
];

fn empty_root() -> GreenNode {
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    output.finish_node();
    output.finish()
}

fn seeded_root() -> GreenNode {
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
    output.finish_node();
    output.finish()
}

#[test]
fn parser_output_forwards_the_complete_o1_builder_surface() {
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let checkpoint = output.checkpoint();
    output.token(SyntaxKind::Identifier.into(), "value");
    output.start_node_at(checkpoint, SyntaxKind::IdentifierExpression.into());
    output.finish_node();
    output.finish_node();

    let root = SyntaxNode::new_root(output.finish());
    assert_eq!(root.to_string(), "value");
    let expression = root.first_child().expect("wrapped checkpoint token");
    assert_eq!(expression.kind(), SyntaxKind::IdentifierExpression);
    assert_eq!(
        expression.first_token().unwrap().kind(),
        SyntaxKind::Identifier
    );
}

#[test]
fn rejected_expression_and_type_entries_are_output_effect_free() {
    let operators = OperatorTable::empty();
    let mut input = ")";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());

    assert!(expr(In::new(&mut input, &mut recover, &mut output)).is_none());
    assert!(type_expr(In::new(&mut input, &mut recover, &mut output)).is_none());
    assert_eq!(input, ")");

    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
    output.finish_node();
    let candidate = output.finish();
    let control = seeded_root();
    assert_eq!(candidate, control);
}

#[test]
fn option_parser_in_audit_has_exactly_the_reviewed_procedures() {
    assert_eq!(OPTION_PARSER_IN_AUDIT.len(), 23);
    for (index, entry) in OPTION_PARSER_IN_AUDIT.iter().enumerate() {
        assert!(!entry.source.is_empty());
        assert!(!entry.procedure.is_empty());
        assert!(
            !OPTION_PARSER_IN_AUDIT[..index].iter().any(|prior| {
                prior.source == entry.source && prior.procedure == entry.procedure
            }),
            "duplicate Option<...> ParserIn audit entry: {entry:?}"
        );
    }
    assert_eq!(
        OPTION_PARSER_IN_AUDIT
            .iter()
            .filter(|entry| entry.evidence == OptionEntryEvidence::FocusedRejection)
            .count(),
        14
    );
    assert_eq!(
        OPTION_PARSER_IN_AUDIT
            .iter()
            .filter(|entry| {
                entry.evidence == OptionEntryEvidence::SourceOnlyOrLexicallyTransactional
            })
            .count(),
        9
    );
}

#[test]
fn nontrivial_option_entries_reject_without_output_effects() {
    let control = empty_root();

    let (green, exit, remainder) =
        run_normalized(")", &OperatorTable::empty(), 0, LineEntry::InLine, None);
    assert!(exit.is_none());
    assert_eq!(remainder, ")");
    assert_eq!(green, control);

    let (green, exit, remainder) = run_type_normalized(")", 0, LineEntry::InLine, None);
    assert!(exit.is_none());
    assert_eq!(remainder, ")");
    assert_eq!(green, control);

    let rejection_cases = [
        run_declaration_companion("within {}", 0, 0, 0, LineEntry::InLine, None),
        run_cast_declaration("casting(x): T;", 0, 0, LineEntry::InLine, None),
        run_enum_declaration("enumeration E;", 0, 0, LineEntry::InLine, None),
        run_error_declaration("errors E;", 0, 0, LineEntry::InLine, None),
        run_impl_declaration("implement T;", 0, 0, LineEntry::InLine, None),
        run_act_declaration("acting T;", 0, 0, LineEntry::InLine, None),
        run_role_declaration("roles R;", 0, 0, LineEntry::InLine, None),
    ];
    for (green, exit, remainder) in rejection_cases {
        assert!(exit.is_none());
        assert!(!remainder.is_empty());
        assert_eq!(green, control);
    }

    let (green, exit, _) = run_declaration_variant(
        ":",
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert!(exit.is_none());
    assert_eq!(green, control);

    let operators = OperatorTable::empty();
    let mut input = "@";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..0,
            marker_width: 0,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    assert!(
        pattern_literal_witness(In::new(&mut input, &mut recover, &mut output), 0, &fence,)
            .is_none()
    );
    output.finish_node();
    assert_eq!(input, "@");
    assert_eq!(output.finish(), control);

    let mut input = "@";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let rejected = Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: "@".into(),
        }),
    );
    let admission = classify_statement_item_normalized(
        In::new(&mut input, &mut recover, &mut output),
        &rejected,
        0,
        0,
        None,
    );
    assert!(admission.is_none());
    output.finish_node();
    assert_eq!(output.finish(), control);
}
