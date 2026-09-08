use std::sync::Arc;

use rowan::GreenNode;

use crate::{
    HeaderInfo, SourceText,
    operator_compilation::compile_full_parse_operators_recovering,
    source_file::parse_root_candidate,
    syntax_diagnostic::SyntaxDiagnostic,
    syntax_environment::{SourceRevision, SyntaxEnvironment, SyntaxEnvironmentKey},
};

#[cfg(test)]
use crate::{
    OperatorFixity,
    operator_table::{OperatorOrigin, OperatorTable},
    syntax_diagnostic::SyntaxDiagnosticCause,
};

/// Immutable full-parse product for one source revision.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    source: Arc<SourceText>,
    revision: SourceRevision,
    header: Arc<HeaderInfo>,
    syntax_environment: SyntaxEnvironmentKey,
    green: GreenNode,
    diagnostics: Arc<[SyntaxDiagnostic]>,
}

impl ParsedFile {
    pub fn source(&self) -> &SourceText {
        &self.source
    }

    pub fn revision(&self) -> SourceRevision {
        self.revision
    }

    pub fn header(&self) -> &HeaderInfo {
        &self.header
    }

    pub fn syntax_environment(&self) -> SyntaxEnvironmentKey {
        self.syntax_environment
    }

    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    pub fn diagnostics(&self) -> &[SyntaxDiagnostic] {
        &self.diagnostics
    }
}

/// Parse a source with its discovered header and selected syntax environment.
pub fn parse_file(
    source: Arc<SourceText>,
    header: Arc<HeaderInfo>,
    syntax: Arc<SyntaxEnvironment>,
) -> ParsedFile {
    assert!(
        Arc::ptr_eq(&source, &header.source),
        "HeaderInfo must originate from the supplied source allocation"
    );
    // The accepted table is prepared once before the direct root loop. Duplicate
    // capabilities produce construction diagnostics without replacing this
    // parser authority or mutating the table while parsing.
    let operator_compilation =
        compile_full_parse_operators_recovering(syntax.operators(), header.operators())
            .expect("complete header operators and validated imports never have empty spellings");
    let candidate = parse_root_candidate(
        source.as_ref(),
        &operator_compilation.table,
        &header.recoveries,
    );
    let green = candidate.green;
    let recoveries = candidate.committed_recoveries;
    let next_construction_event = recoveries
        .iter()
        .map(|record| record.id.0)
        .max()
        .map_or(0, |id| {
            id.checked_add(1).expect("diagnostic ID space exhausted")
        });
    let diagnostics = recoveries
        .into_iter()
        .map(SyntaxDiagnostic::recovery)
        .chain(
            operator_compilation
                .rejected_conflicts
                .into_iter()
                .enumerate()
                .map(|(event, conflict)| {
                    let event = u32::try_from(event).expect("diagnostic ID space exhausted");
                    let id = next_construction_event
                        .checked_add(event)
                        .expect("diagnostic ID space exhausted");
                    SyntaxDiagnostic::conflicting_operator_fixity(id, conflict)
                }),
        )
        .collect();

    ParsedFile {
        source,
        revision: SourceRevision::UNTRACKED,
        header,
        syntax_environment: syntax.key(),
        green,
        diagnostics,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        SyntaxDependencyProvenance, SyntaxDependencySlot,
        operator_table::{BindingPower, OperatorDeclaration, OperatorFixities},
    };

    #[test]
    fn public_parser_pair_preserves_headers_and_multiple_statements() {
        let source: Arc<SourceText> =
            Arc::from("use std::io\r\nprefix (?) 70 = 値\r\nmy x = 1; my y = 2\r\nx\r\n");
        let header = Arc::new(crate::scan_header(source.clone()));
        assert_eq!(header.imports().len(), 1);
        assert_eq!(header.operators().len(), 1);
        let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
        assert_eq!(parsed.green().to_string(), source.as_ref());
        assert!(
            parsed.diagnostics().is_empty(),
            "{:?}",
            parsed.diagnostics()
        );
        let syntax = crate::SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            syntax
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [
                crate::SyntaxKind::UseDeclaration,
                crate::SyntaxKind::OperatorHeader,
                crate::SyntaxKind::OperatorChain,
                crate::SyntaxKind::BindingStatement,
                crate::SyntaxKind::BindingStatement,
                crate::SyntaxKind::OperatorChain
            ]
        );
    }

    #[test]
    fn public_parser_pair_preserves_imported_local_conflict_provenance_after_recovery() {
        let source: Arc<SourceText> =
            Arc::from("use a as\r\nprefix (?) 71 = value\r\nmy x = 1\r\n");
        let header = Arc::new(crate::scan_header(source.clone()));
        assert_eq!(header.operators().len(), 1);
        assert_eq!(header.recoveries.len(), 1);
        let dependency = SyntaxDependencySlot::from_index(0).unwrap();
        let provenance = SyntaxDependencyProvenance::new(
            Arc::from("dependency/operators"),
            SourceRevision::UNTRACKED,
        );
        let syntax = Arc::new(
            SyntaxEnvironment::from_imported(
                SyntaxEnvironmentKey::from_raw(7),
                Arc::new(
                    OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                        "?",
                        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                        dependency,
                        4..20,
                    )])
                    .unwrap(),
                ),
                Arc::from([provenance.clone()]),
            )
            .unwrap(),
        );
        let parsed = parse_file(source.clone(), header.clone(), syntax.clone());
        assert_eq!(parsed.green().to_string(), source.as_ref());
        assert_eq!(parsed.syntax_environment(), syntax.key());
        let [recovery, construction] = parsed.diagnostics() else {
            panic!(
                "recovery followed by imported/local conflict: {:?}",
                parsed.diagnostics()
            );
        };
        let SyntaxDiagnosticCause::Recovery(recovery_record) = recovery.cause() else {
            panic!("header recovery precedes construction");
        };
        assert_eq!(recovery_record.record(), &header.recoveries[0]);
        let SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = construction.cause()
        else {
            panic!("imported/local conflict");
        };
        assert_eq!(conflict.spelling(), "?");
        assert_eq!(conflict.fixity(), OperatorFixity::Prefix);
        assert_eq!(
            conflict.first_origin(),
            OperatorOrigin::Imported(dependency)
        );
        assert_eq!(syntax.dependency(dependency), Some(&provenance));
        assert_eq!(conflict.first_range(), &(4..20));
        assert_eq!(conflict.second_origin(), OperatorOrigin::Local);
        assert_eq!(conflict.second_range(), header.operators()[0].range());
        assert!(recovery.id() < construction.id());
    }

    #[test]
    fn public_parser_pair_keeps_header_fences_opaque_and_continues_after_body_recovery() {
        for body in [
            "'{\n```raw\n}\nuse hidden\n```\n}",
            "'{\n> ```yulang\n> \"```\"\n> ```\n}",
        ] {
            let source: Arc<SourceText> = Arc::from(format!(
                "prefix (!) 70 = {body}\nuse visible\nmy value = 1\n\"following\""
            ));
            let header = Arc::new(crate::scan_header(source.clone()));
            assert_eq!(header.operators().len(), 1, "{source}");
            assert_eq!(header.imports().len(), 1, "{source}");
            assert_eq!(header.imports()[0].path(), ["visible"], "{source}");
            let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
            assert_eq!(parsed.green().to_string(), source.as_ref());
            assert!(parsed.diagnostics().iter().any(|diagnostic| matches!(
                diagnostic.cause(),
                SyntaxDiagnosticCause::Recovery(recovery)
                    if recovery.record().site.role == crate::recovery_record::GrammarRole::Statement(
                        crate::recovery_record::StatementRole::OperatorDefinitionBody
                    )
            )));
            let syntax = crate::SyntaxNode::new_root(parsed.green().clone());
            assert!(
                syntax
                    .children()
                    .any(|node| node.kind() == crate::SyntaxKind::UseDeclaration
                        && node.to_string() == "use visible"),
                "{source}"
            );
            assert!(
                syntax
                    .children()
                    .any(|node| node.kind() == crate::SyntaxKind::BindingStatement
                        && node.to_string() == "my value = 1"),
                "{source}"
            );
            assert_eq!(
                syntax.children().last().unwrap().to_string(),
                "\"following\""
            );
        }
    }

    #[test]
    fn public_parser_pair_reconciles_frozen_header_after_full_only_recovery() {
        let source: Arc<SourceText> = Arc::from(
            "prefix (?) 70 =\r\nuse a as\r\nuse good\r\nprefix (?) 71 = value\r\nmy x = 1\r\n",
        );
        let header = Arc::new(crate::scan_header(source.clone()));
        assert_eq!(header.recoveries.len(), 1);
        assert_eq!(header.imports().len(), 1);
        assert_eq!(header.imports()[0].path(), ["good"]);
        let parsed = parse_file(
            source.clone(),
            header.clone(),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source.as_ref());
        let [body, alias, conflict] = parsed.diagnostics() else {
            panic!(
                "body, frozen alias, then construction conflict: {:?}",
                parsed.diagnostics()
            );
        };
        let SyntaxDiagnosticCause::Recovery(body) = body.cause() else {
            panic!("body recovery")
        };
        assert_eq!(
            body.record().site.role,
            crate::recovery_record::GrammarRole::Statement(
                crate::recovery_record::StatementRole::OperatorDefinitionBody
            )
        );
        let SyntaxDiagnosticCause::Recovery(alias) = alias.cause() else {
            panic!("alias recovery")
        };
        assert_eq!(alias.record(), &header.recoveries[0]);
        assert!(body.record().id.0 > alias.record().id.0);
        assert!(matches!(
            conflict.cause(),
            SyntaxDiagnosticCause::ConflictingOperatorFixity(_)
        ));
        assert!(conflict.id() > body.record().id.0);
    }

    #[test]
    fn public_parser_pair_retains_binding_selector_and_initial_layout() {
        for word in ["use", "prefix", "infix", "suffix", "nullfix", "lazy"] {
            let source: Arc<SourceText> = Arc::from(format!("my {word} = 値\r\nuse later"));
            let header = Arc::new(crate::scan_header(source.clone()));
            assert!(header.imports().is_empty());
            assert!(header.operators().is_empty());
            let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
            assert_eq!(parsed.green().to_string(), source.as_ref());
            assert!(
                parsed.diagnostics().is_empty(),
                "{:?}",
                parsed.diagnostics()
            );
        }
        let source: Arc<SourceText> = Arc::from("  use a");
        let header = Arc::new(crate::scan_header(source.clone()));
        assert!(header.imports().is_empty());
        let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
        assert_eq!(parsed.green().to_string(), source.as_ref());
        assert_eq!(parsed.diagnostics().len(), 1);
        let SyntaxDiagnosticCause::Recovery(record) = parsed.diagnostics()[0].cause() else {
            panic!("initial layout recovery")
        };
        assert_eq!(
            record.record().site.role,
            crate::recovery_record::GrammarRole::Statement(
                crate::recovery_record::StatementRole::Starter
            )
        );
    }

    #[test]
    fn header_source_identity_accepts_shared_allocation_and_cloned_header() {
        let source: Arc<SourceText> = Arc::from("let x = 1");
        let header = crate::scan_header(source.clone());
        for header in [header.clone(), header] {
            let parsed = parse_file(
                source.clone(),
                Arc::new(header),
                Arc::new(SyntaxEnvironment::default()),
            );
            assert_eq!(parsed.source.as_ref(), source.as_ref());
        }
    }

    #[test]
    fn header_source_identity_rejects_distinct_snapshots() {
        let source: Arc<SourceText> = Arc::from("let x = 1");
        let header = Arc::new(crate::scan_header(source.clone()));
        for text in ["let x = 1", "let y = 2"] {
            let other: Arc<SourceText> = Arc::from(text);
            assert!(!Arc::ptr_eq(&source, &other));
            assert_eq!(*header, crate::scan_header(other.clone()));
            assert!(
                std::panic::catch_unwind(|| {
                    parse_file(
                        other,
                        header.clone(),
                        Arc::new(SyntaxEnvironment::default()),
                    )
                })
                .is_err()
            );
        }
    }

    #[test]
    fn parse_file_keeps_the_first_local_fixity_and_reports_the_rejected_site() {
        let source: Arc<SourceText> =
            Arc::from("infix (<+>) 40 41 = left\ninfix (<+>) 42 43 = right\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));

        assert_eq!(header.operators().len(), 2);
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );

        assert_eq!(parsed.green().to_string(), source.as_ref());
        let [diagnostic] = parsed.diagnostics() else {
            panic!("the duplicate fixity must be diagnosed");
        };
        assert_eq!(diagnostic.primary(), header.operators()[1].range());
        let SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = diagnostic.cause() else {
            panic!("operator construction must not masquerade as CST recovery");
        };
        assert_eq!(conflict.spelling(), "<+>");
        assert_eq!(conflict.fixity(), OperatorFixity::Infix);
        assert_eq!(conflict.first_origin(), OperatorOrigin::Local);
        assert_eq!(conflict.second_origin(), OperatorOrigin::Local);
        assert_eq!(conflict.first_range(), header.operators()[0].range());
        assert_eq!(conflict.second_range(), header.operators()[1].range());
    }

    #[test]
    fn parse_file_preserves_recovery_diagnostics_before_construction_diagnostics() {
        // Root expressions are admitted by the public-cutover amendment;
        // an unclaimed close exercises a genuine root recovery.
        let source: Arc<SourceText> =
            Arc::from("infix (<+>) 40 41 = left\ninfix (<+>) 42 43 = right\n]\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        let parsed = parse_file(
            Arc::clone(&source),
            header,
            Arc::new(SyntaxEnvironment::empty()),
        );

        assert_eq!(parsed.green().to_string(), source.as_ref());
        let [recovery, conflict] = parsed.diagnostics() else {
            panic!("the root recovery and duplicate fixity must both be diagnosed");
        };
        assert!(matches!(
            recovery.cause(),
            SyntaxDiagnosticCause::Recovery(_)
        ));
        assert!(matches!(
            conflict.cause(),
            SyntaxDiagnosticCause::ConflictingOperatorFixity(_)
        ));
        assert_ne!(recovery.id(), conflict.id());
        assert!(recovery.id() < conflict.id());
    }
}
