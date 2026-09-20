use std::{cell::RefCell, collections::BTreeMap, sync::Arc};

use rowan::GreenNode;

use crate::{
    HeaderInfo, SourceText, SyntaxDiagnosticIdentity, SyntaxDiagnosticKind,
    operator_compilation::{conflicting_local_operators, effective_full_parse_operators},
    operator_table::OperatorTable,
    structural_diagnostic,
    syntax_diagnostic::SyntaxDiagnostic,
    syntax_environment::{SourceRevision, SyntaxEnvironment, SyntaxEnvironmentKey},
};

/// One recovery occurrence derived from the immutable CST.
///
/// This intentionally exposes only the facts needed by later compiler phases;
/// parser recovery records and CST mutation remain syntax-internal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralRecovery {
    kind: StructuralRecoveryKind,
    range: std::ops::Range<usize>,
    ordinal: u32,
    path: Box<[crate::SyntaxKind]>,
    direct_root_ordinal: Option<u32>,
}

impl StructuralRecovery {
    pub fn kind(&self) -> StructuralRecoveryKind {
        self.kind
    }

    pub fn range(&self) -> &std::ops::Range<usize> {
        &self.range
    }

    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }

    pub fn path(&self) -> &[crate::SyntaxKind] {
        &self.path
    }

    pub fn direct_root_ordinal(&self) -> Option<u32> {
        self.direct_root_ordinal
    }
}

/// The CST-derived recovery class of a [`StructuralRecovery`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralRecoveryKind {
    Missing,
    RawError,
    Invalid,
}

/// Immutable full-parse product for one source revision.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    source: Arc<SourceText>,
    revision: SourceRevision,
    header: Arc<HeaderInfo>,
    syntax: Arc<SyntaxEnvironment>,
    operators: Arc<OperatorTable>,
    green: GreenNode,
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
        self.syntax.key()
    }

    /// The selected environment whose exact operator inputs parsed this tree.
    pub fn selected_syntax_environment(&self) -> &Arc<SyntaxEnvironment> {
        &self.syntax
    }

    /// The one effective operator table the parser used, retained for analysis.
    pub fn operators(&self) -> &OperatorTable {
        &self.operators
    }

    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Collects final diagnostics from the retained CST and selected environment.
    /// Nothing is stored by the parser: each call walks this snapshot in preorder.
    pub fn syntax_diagnostics(&self) -> Result<Vec<SyntaxDiagnostic>, SyntaxDiagnosticError> {
        collect_syntax_diagnostics(self)
    }

    /// Projects recovery structure from the retained CST in interpreter order.
    ///
    /// Each call performs one interpreter walk. Consumers needing the facts for
    /// a phase should retain this returned projection instead of walking the CST.
    pub fn structural_recoveries(&self) -> Vec<StructuralRecovery> {
        self.try_structural_recoveries()
            .expect("structural recovery adapter preserves the legacy total contract")
    }

    /// Fallibly projects recovery structure for availability-aware compiler phases.
    pub fn try_structural_recoveries(
        &self,
    ) -> Result<Vec<StructuralRecovery>, StructuralProjectionError> {
        let root = crate::SyntaxNode::new_root(self.green.clone());
        let occurrences = structural_diagnostic::try_collect(&root)
            .map_err(|error| match error {
                structural_diagnostic::StructuralProjectionError::OrdinalExhausted => {
                    StructuralProjectionError::OrdinalExhausted
                }
                structural_diagnostic::StructuralProjectionError::StructuralInvariant => {
                    StructuralProjectionError::StructuralInvariant
                }
            })?
            .into_iter()
            .map(|occurrence| StructuralRecovery {
                kind: match occurrence.kind() {
                    structural_diagnostic::StructuralKind::Missing => {
                        StructuralRecoveryKind::Missing
                    }
                    structural_diagnostic::StructuralKind::ErrorGroup => {
                        StructuralRecoveryKind::RawError
                    }
                    structural_diagnostic::StructuralKind::Invalid => {
                        StructuralRecoveryKind::Invalid
                    }
                },
                range: occurrence.range().clone(),
                ordinal: occurrence.ordinal(),
                path: occurrence.path().into(),
                direct_root_ordinal: occurrence.direct_root_ordinal(),
            })
            .collect();
        Ok(occurrences)
    }
}

/// A structural recovery projection could not preserve its dense ordinal invariant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralProjectionError {
    OrdinalExhausted,
    StructuralInvariant,
}

/// CST/environment analysis could not prove that every selected header fact
/// refers to exactly one complete full-CST `OperatorHeader` occurrence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SyntaxDiagnosticError {
    Structural(StructuralProjectionError),
    HeaderOperatorWithoutAcceptedSite,
    ConflictingHeaderMapping,
}

fn collect_syntax_diagnostics(
    parsed: &ParsedFile,
) -> Result<Vec<SyntaxDiagnostic>, SyntaxDiagnosticError> {
    let mut conflicts = BTreeMap::new();
    for header in parsed.header.operators() {
        if parsed
            .operators
            .fixity_sites(header.name())
            .and_then(|sites| sites.site(header.fixity()))
            .is_none()
        {
            return Err(SyntaxDiagnosticError::HeaderOperatorWithoutAcceptedSite);
        }
    }
    for conflict in conflicting_local_operators(&parsed.operators, parsed.header.operators()) {
        let key = (conflict.second_range.start, conflict.second_range.end);
        if conflicts.insert(key, (conflict, 0u32)).is_some() {
            return Err(SyntaxDiagnosticError::ConflictingHeaderMapping);
        }
    }

    let root = crate::SyntaxNode::new_root(parsed.green.clone());
    let diagnostics = RefCell::new(Vec::new());
    let conflicts = RefCell::new(conflicts);
    structural_diagnostic::walk_with_node_entry(
        &root,
        &mut |node, occurrence_path, ordinal| {
            if node.kind() == crate::SyntaxKind::OperatorHeader {
                let range = (
                    usize::from(node.text_range().start()),
                    usize::from(node.text_range().end()),
                );
                if let Some((conflict, matches)) = conflicts.borrow_mut().get_mut(&range) {
                    *matches = matches
                        .checked_add(1)
                        .ok_or(())
                        .expect("header occurrence count exhausted");
                    diagnostics
                        .borrow_mut()
                        .push(SyntaxDiagnostic::conflicting_operator_fixity(
                            SyntaxDiagnosticIdentity::new(
                                occurrence_path.into(),
                                None,
                                SyntaxDiagnosticKind::ConflictingOperatorFixity,
                                ordinal,
                            ),
                            conflict.clone(),
                        ));
                    return true;
                }
            }
            false
        },
        &mut |occurrence| {
            diagnostics
                .borrow_mut()
                .push(SyntaxDiagnostic::structural(occurrence))
        },
    )
    .map_err(|error| match error {
        structural_diagnostic::StructuralProjectionError::OrdinalExhausted => {
            StructuralProjectionError::OrdinalExhausted
        }
        structural_diagnostic::StructuralProjectionError::StructuralInvariant => {
            StructuralProjectionError::StructuralInvariant
        }
    })
    .map_err(SyntaxDiagnosticError::Structural)?;
    if conflicts
        .into_inner()
        .into_values()
        .any(|(_, matches)| matches != 1)
    {
        return Err(SyntaxDiagnosticError::ConflictingHeaderMapping);
    }
    Ok(diagnostics.into_inner())
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
    // capabilities keep the first accepted site without replacing this parser
    // authority or mutating the table while parsing.
    let operators = effective_full_parse_operators(syntax.operators(), header.operators())
        .expect("complete header operators and validated imports never have empty spellings");
    let green = crate::cursor::parse_root(source.as_ref(), &operators);

    ParsedFile {
        source,
        revision: SourceRevision::UNTRACKED,
        header,
        syntax,
        operators: Arc::new(operators),
        green,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        OperatorFixity, OperatorOrigin, SyntaxDependencyProvenance, SyntaxDependencySlot,
        operator_table::{BindingPower, OperatorDeclaration, OperatorFixities},
        structural_diagnostic::StructuralKind,
        syntax_diagnostic::SyntaxDiagnosticCause,
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
            parsed.syntax_diagnostics().unwrap().is_empty(),
            "{:?}",
            parsed.syntax_diagnostics()
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
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [recovery, construction] = diagnostics.as_slice() else {
            panic!(
                "recovery followed by imported/local conflict: {:?}",
                diagnostics
            );
        };
        let SyntaxDiagnosticCause::Structural(recovery_record) = recovery.cause() else {
            panic!("header recovery precedes construction");
        };
        assert_eq!(recovery_record.kind(), StructuralKind::Missing);
        assert_eq!(recovery_record.range(), &(8..8));
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
        assert!(recovery_record.ordinal() < 1);
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
            let diagnostics = parsed.syntax_diagnostics().unwrap();
            assert!(
                diagnostics.iter().any(|diagnostic| matches!(
                    diagnostic.cause(),
                    SyntaxDiagnosticCause::Structural(recovery)
                        if recovery.kind() == StructuralKind::ErrorGroup
                            && recovery.parent()
                                == crate::SyntaxKind::BracedStatementBlockExpression
                )),
                "{source}: {diagnostics:?}"
            );
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
    fn public_parser_pair_derives_header_and_body_recoveries_from_the_cst() {
        let source: Arc<SourceText> = Arc::from(
            "prefix (?) 70 =\r\nuse a as\r\nuse good\r\nprefix (?) 71 = value\r\nmy x = 1\r\n",
        );
        let header = Arc::new(crate::scan_header(source.clone()));
        assert_eq!(header.imports().len(), 1);
        assert_eq!(header.imports()[0].path(), ["good"]);
        let parsed = parse_file(
            source.clone(),
            header.clone(),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source.as_ref());
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [body, alias, conflict] = diagnostics.as_slice() else {
            panic!("body, alias, then construction conflict: {:?}", diagnostics);
        };
        let SyntaxDiagnosticCause::Structural(body) = body.cause() else {
            panic!("body recovery")
        };
        assert_eq!(body.kind(), StructuralKind::Missing);
        let SyntaxDiagnosticCause::Structural(alias) = alias.cause() else {
            panic!("alias recovery")
        };
        assert_eq!(alias.kind(), StructuralKind::Missing);
        assert!(body.ordinal() < alias.ordinal());
        assert!(matches!(
            conflict.cause(),
            SyntaxDiagnosticCause::ConflictingOperatorFixity(_)
        ));
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
                parsed.syntax_diagnostics().unwrap().is_empty(),
                "{:?}",
                parsed.syntax_diagnostics()
            );
        }
        let source: Arc<SourceText> = Arc::from("  use a");
        let header = Arc::new(crate::scan_header(source.clone()));
        assert!(header.imports().is_empty());
        let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
        assert_eq!(parsed.green().to_string(), source.as_ref());
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        assert_eq!(diagnostics.len(), 1);
        let SyntaxDiagnosticCause::Structural(record) = diagnostics[0].cause() else {
            panic!("initial layout recovery")
        };
        assert_eq!(record.kind(), StructuralKind::ErrorGroup);
        assert_eq!(record.range(), &(2..7));
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
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
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
    fn parse_file_emits_construction_and_recovery_in_cst_preorder() {
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
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [conflict, recovery] = diagnostics.as_slice() else {
            panic!("the duplicate fixity and root recovery must both be diagnosed");
        };
        assert!(matches!(
            conflict.cause(),
            SyntaxDiagnosticCause::ConflictingOperatorFixity(_)
        ));
        let SyntaxDiagnosticCause::Structural(recovery) = recovery.cause() else {
            panic!("root raw CST Error follows the enclosing conflicting header");
        };
        assert_eq!(recovery.kind(), StructuralKind::ErrorGroup);
        assert_eq!(recovery.range(), &(source.len() - 2..source.len() - 1));
    }

    #[test]
    fn conflicting_operator_header_precedes_its_nested_recovery() {
        let source: Arc<SourceText> = Arc::from("prefix (!) 70 = left\nprefix @ (!) 71 = right\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert_eq!(header.operators().len(), 2);
        let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));

        assert_eq!(parsed.green().to_string(), source.as_ref());
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [conflict, recovery] = diagnostics.as_slice() else {
            panic!("complete conflicting header and its child recovery: {diagnostics:?}");
        };
        assert!(matches!(
            conflict.cause(),
            SyntaxDiagnosticCause::ConflictingOperatorFixity(_)
        ));
        let SyntaxDiagnosticCause::Structural(recovery) = recovery.cause() else {
            panic!("the child Error follows its enclosing header conflict");
        };
        assert_eq!(recovery.kind(), StructuralKind::ErrorGroup);
        assert!(conflict.identity().ordinal() < recovery.identity().ordinal());
        assert!(
            recovery
                .identity()
                .occurrence_path()
                .starts_with(conflict.identity().occurrence_path()),
            "the recovery belongs to the conflicting OperatorHeader"
        );
    }

    #[test]
    fn retained_operator_table_is_the_one_analysis_reads() {
        // Equal binding powers do not admit a second declaration, so the first
        // local site wins and the retained table keeps exactly that site.
        let source: Arc<SourceText> =
            Arc::from("infix (<+>) 40 41 = left\ninfix (<+>) 40 41 = right\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert_eq!(header.operators().len(), 2);
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );

        let site = parsed
            .operators()
            .fixity_sites("<+>")
            .and_then(|sites| sites.site(OperatorFixity::Infix))
            .expect("accepted infix site");
        assert_eq!(site.origin(), OperatorOrigin::Local);
        assert_eq!(site.range(), header.operators()[0].range());

        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("one rejected duplicate: {:?}", diagnostics);
        };
        let SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = diagnostic.cause() else {
            panic!("duplicate fixity must not masquerade as CST recovery");
        };
        assert_eq!(conflict.first_range(), site.range());
        assert_eq!(conflict.first_range(), header.operators()[0].range());
        assert_eq!(conflict.second_range(), header.operators()[1].range());
    }

    #[test]
    fn retained_operator_table_keeps_the_imported_site_for_a_local_duplicate() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let source: Arc<SourceText> = Arc::from("prefix (?) 71 = value\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert_eq!(header.operators().len(), 1);
        let syntax = Arc::new(
            SyntaxEnvironment::from_imported(
                SyntaxEnvironmentKey::from_raw(9),
                Arc::new(
                    OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                        "?",
                        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                        dependency,
                        4..20,
                    )])
                    .unwrap(),
                ),
                Arc::from([SyntaxDependencyProvenance::new(
                    Arc::from("dependency/operators"),
                    SourceRevision::UNTRACKED,
                )]),
            )
            .expect("validated imported environment"),
        );
        let parsed = parse_file(Arc::clone(&source), Arc::clone(&header), syntax);

        let site = parsed
            .operators()
            .fixity_sites("?")
            .and_then(|sites| sites.site(OperatorFixity::Prefix))
            .expect("accepted prefix site");
        assert_eq!(site.origin(), OperatorOrigin::Imported(dependency));
        assert_eq!(site.range(), &(4..20));

        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("one rejected local duplicate: {:?}", diagnostics);
        };
        let SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = diagnostic.cause() else {
            panic!("imported/local duplicate must not masquerade as CST recovery");
        };
        assert_eq!(conflict.first_range(), site.range());
        assert_eq!(conflict.second_range(), header.operators()[0].range());
    }

    #[test]
    fn retained_operator_table_keeps_mixed_fixities_for_one_spelling() {
        let source: Arc<SourceText> = Arc::from("prefix (?) 70 = a\nsuffix (?) 71 = b\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert_eq!(header.operators().len(), 2, "{:?}", header.operators());
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );

        let sites = parsed
            .operators()
            .fixity_sites("?")
            .expect("accepted spelling");
        assert_eq!(
            sites
                .site(OperatorFixity::Prefix)
                .map(|site| site.range().clone()),
            Some(header.operators()[0].range().clone())
        );
        assert_eq!(
            sites
                .site(OperatorFixity::Suffix)
                .map(|site| site.range().clone()),
            Some(header.operators()[1].range().clone())
        );
        assert!(
            parsed.syntax_diagnostics().unwrap().is_empty(),
            "{:?}",
            parsed.syntax_diagnostics()
        );
    }

    #[test]
    fn retained_operator_table_reports_every_rejected_duplicate_in_source_order() {
        let source: Arc<SourceText> =
            Arc::from("infix (<+>) 40 41 = a\ninfix (<+>) 41 42 = b\ninfix (<+>) 43 44 = c\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert_eq!(header.operators().len(), 3);
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );

        let conflicts = parsed
            .syntax_diagnostics()
            .unwrap()
            .iter()
            .map(|diagnostic| match diagnostic.cause() {
                SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) => conflict.clone(),
                other => panic!("unexpected cause: {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(conflicts.len(), 2);
        assert_eq!(conflicts[0].first_range(), header.operators()[0].range());
        assert_eq!(conflicts[0].second_range(), header.operators()[1].range());
        assert_eq!(conflicts[1].first_range(), header.operators()[0].range());
        assert_eq!(conflicts[1].second_range(), header.operators()[2].range());
        assert!(
            parsed
                .syntax_diagnostics()
                .unwrap()
                .windows(2)
                .all(|pair| pair[0].primary().start <= pair[1].primary().start),
            "conflicts preserve CST/source order"
        );
    }

    #[test]
    fn retained_operator_table_excludes_operators_after_the_header_cutoff() {
        let source: Arc<SourceText> = Arc::from("my x = 1\nprefix (?) 70 = value\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        assert!(header.operators().is_empty());
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.operators().fixity_sites("?").is_none());
        assert!(
            parsed.syntax_diagnostics().unwrap().is_empty(),
            "{:?}",
            parsed.syntax_diagnostics()
        );
    }
}
