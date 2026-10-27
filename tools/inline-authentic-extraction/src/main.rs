use std::{fmt::Write as _, ops::Range, sync::Arc};

use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, HirParameterId,
    LocalSource, LocalSourceExpr, LocalSourceForm, LocalSourceIndex, LocalSourceParameter,
    LocalSourceResolution, LocalSourceScope, LocalSourceStatement, ModuleIdentity,
    SemanticImports, SourceRootId,
    shadow::{
        ParameterSourceOrigin, ShadowArtifact, SourceIdentityError,
        lower_module_with_local_source,
    },
};
use yu_syntax::{
    ParsedFile, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header,
};

const INPUT: &str = r"my value = \x -> { (\x -> x) x; x }";
const OUTPUT: &str =
    "notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean";
const MODULE: &str = "inline-authentic-extraction";
const FILE: &str = "inline_authentic_extraction.yu";

#[derive(Clone)]
struct SourcePositionEvidence {
    label: String,
    position_kind: &'static str,
    position: usize,
    range: Range<usize>,
}

#[derive(Clone)]
struct BodyEntryEvidence {
    kind: &'static str,
    source_order: usize,
    local_index: Option<u32>,
    binding_ordinal: Option<u32>,
    occurrence_ordinal: Option<u32>,
    range: Option<Range<usize>>,
    source_position: Option<usize>,
    source_position_kind: Option<&'static str>,
    source_position_range: Option<Range<usize>>,
    index_value: Option<LocalSourceIndex>,
}

#[derive(Clone)]
struct GroupProjectionEvidence {
    group_index: u32,
    inner_index: u32,
    group_occurrence: u32,
    inner_occurrence: u32,
    group_range: Range<usize>,
    inner_range: Range<usize>,
}

struct NameUseEvidence {
    label: &'static str,
    index: u32,
    occurrence: u32,
    spelling: String,
    parameter: u32,
    range: Range<usize>,
    source_position: usize,
}

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn lower(parsed: &ParsedFile) -> Result<HirModule, HirAvailabilityError> {
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(MODULE, FILE))),
        parsed,
        SemanticImports::empty(),
    )
}

fn expression<'a>(source: &'a LocalSource, root: &SourceRootId, index: &LocalSourceIndex)
    -> &'a LocalSourceExpr
{
    assert_eq!(index.source_root(), root, "LocalSourceIndex must carry the selected root");
    source.expression(index).expect("index must belong to the selected LocalSource")
}

fn position_for_key(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    key: &yu_hir::shadow::SourceNodeKey,
    label: impl Into<String>,
) -> SourcePositionEvidence {
    assert!(parsed.owns_source_key(key), "SourceNodeKey must belong to the selected parse");
    assert!(artifact.parsed().owns_source_key(key), "ShadowArtifact must use the selected parse");
    let position = artifact.source_position(key).expect("same-parse source position");
    let value = artifact.position(&position).expect("position belongs to this ShadowArtifact");
    SourcePositionEvidence {
        label: label.into(),
        position_kind: if value.is_node() { "node" } else { "token" },
        position: position.ordinal(),
        range: value.range().clone(),
    }
}

fn authenticate_expressions(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    root: &SourceRootId,
    source: &LocalSource,
) -> Vec<SourcePositionEvidence> {
    assert!(hir.owns_source_root(root), "selected root must belong to this HIR artifact");
    assert_eq!(source.source_root(), root, "LocalSource must retain the exact selected root");
    let mut positions = Vec::with_capacity(source.expressions().len());
    for (ordinal, expr) in source.expressions().iter().enumerate() {
        assert!(parsed.owns_source_key(&expr.source), "expression key must belong to selected parse");
        assert!(artifact.parsed().owns_source_key(&expr.source), "ShadowArtifact must share selected parse");
        assert!(hir.owns_occurrence(&expr.occurrence), "occurrence must belong to selected HIR");
        assert_eq!(
            hir.occurrence_source_key(&expr.occurrence).expect("same-HIR occurrence"),
            Some(&expr.source),
            "occurrence must retain this exact parse-owned SourceNodeKey",
        );
        let evidence = position_for_key(parsed, artifact, &expr.source, format!("local-expression-{ordinal}"));
        assert_eq!(evidence.position_kind, "node", "LocalSource expression keys denote source nodes");
        assert_eq!(evidence.range, expr.range, "LocalSource range must equal its exact CST node range");
        positions.push(evidence);
    }
    positions
}

fn inline_parameter_positions(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    root: &SourceRootId,
    parameter: &LocalSourceParameter,
    label: &str,
) -> (SourcePositionEvidence, SourcePositionEvidence) {
    assert_eq!(parameter.id.source_root(), root, "parameter identity must carry selected root");
    assert!(hir.owns_source_root(parameter.id.source_root()), "parameter root must belong to selected HIR");
    let lambda_key = position_for_key(
        parsed,
        artifact,
        &parameter.source,
        format!("{label}-parameter-lambda-key"),
    );
    let lambda_position = artifact.source_position(&parameter.source).expect("parameter Lambda source key");
    let origin = artifact
        .parameter_source_origin(hir, &parameter.id)
        .expect("registered inline parameter origin from selected HIR and parse");
    let ParameterSourceOrigin::InlineLambda { lambda, binder } = origin else {
        panic!("fixture parameter must have the registered InlineLambda origin");
    };
    assert_eq!(lambda, lambda_position, "registered Lambda origin must equal parameter SourceNodeKey position");
    let lambda_value = artifact.position(&lambda).expect("registered Lambda position");
    assert_eq!(lambda_value.kind(), SyntaxKind::LambdaExpression);
    assert!(lambda_value.is_node());

    let binder_value = artifact.position(&binder).expect("registered binder token position");
    assert_eq!(binder_value.kind(), SyntaxKind::Identifier, "registered binder must be an Identifier token");
    assert!(!binder_value.is_node(), "registered binder origin must be a token position");
    let binder_range = binder_value.range().clone();
    assert_eq!(
        binder_range, parameter.range,
        "exact registered Identifier token range must equal LocalSourceParameter.range",
    );
    let binder_evidence = SourcePositionEvidence {
        label: format!("{label}-binder-token"),
        position_kind: "token",
        position: binder.ordinal(),
        range: binder_range,
    };
    assert_eq!(lambda_key.range, lambda_value.range().clone());
    (lambda_key, binder_evidence)
}

fn project_groups<'a>(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    source: &'a LocalSource,
    root: &SourceRootId,
    raw_callee: &'a LocalSourceIndex,
) -> (Vec<GroupProjectionEvidence>, &'a LocalSourceIndex) {
    let mut path = Vec::new();
    let mut current = raw_callee;
    loop {
        let group = expression(source, root, current);
        let LocalSourceForm::Group { inner } = &group.form else { return (path, current); };
        let inner_expr = expression(source, root, inner);
        for key in [&group.source, &inner_expr.source] {
            assert!(parsed.owns_source_key(key), "Group projection source must belong to selected parse");
            assert!(artifact.parsed().owns_source_key(key), "Group projection must use selected ShadowArtifact");
        }
        assert!(hir.owns_occurrence(&group.occurrence), "Group occurrence must belong to selected HIR");
        assert!(hir.owns_occurrence(&inner_expr.occurrence), "projected occurrence must belong to selected HIR");
        let group_position = artifact.source_position(&group.source).expect("raw Group key position");
        let inner_position = artifact.source_position(&inner_expr.source).expect("Group inner key position");
        let group_range = artifact.position(&group_position).expect("raw Group position").range().clone();
        let inner_range = artifact.position(&inner_position).expect("projected inner position").range().clone();
        assert_eq!(group_range, group.range, "Group range must match its keyed source node");
        assert_eq!(inner_range, inner_expr.range, "projected child range must match its keyed source node");
        path.push(GroupProjectionEvidence {
            group_index: current.ordinal(),
            inner_index: inner.ordinal(),
            group_occurrence: group.occurrence.ordinal(),
            inner_occurrence: inner_expr.occurrence.ordinal(),
            group_range,
            inner_range,
        });
        current = inner;
    }
}

fn body_entries(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    source: &LocalSource,
    root: &SourceRootId,
    body: &LocalSourceExpr,
) -> Vec<BodyEntryEvidence> {
    match &body.form {
        LocalSourceForm::Sequence { items } => items
            .iter()
            .enumerate()
            .map(|(order, index)| {
                let expr = expression(source, root, index);
                let position = position_for_key(parsed, artifact, &expr.source, format!("outer-body-item-{order}"));
                assert!(hir.owns_occurrence(&expr.occurrence));
                assert_eq!(hir.occurrence_source_key(&expr.occurrence).expect("Sequence item occurrence"), Some(&expr.source));
                assert_eq!(position.range, expr.range);
                BodyEntryEvidence {
                    kind: "sequence-item",
                    source_order: order,
                    local_index: Some(index.ordinal()),
                    binding_ordinal: None,
                    occurrence_ordinal: Some(expr.occurrence.ordinal()),
                    range: Some(expr.range.clone()),
                    source_position: Some(position.position),
                    source_position_kind: Some(position.position_kind),
                    source_position_range: Some(position.range),
                    index_value: Some(index.clone()),
                }
            })
            .collect(),
        LocalSourceForm::StatementBlock { statements, final_expression } => {
            let mut entries = Vec::with_capacity(statements.len() + 1);
            for (order, statement) in statements.iter().enumerate() {
                match statement {
                    LocalSourceStatement::Expression(index) => {
                        let expr = expression(source, root, index);
                        let position = position_for_key(parsed, artifact, &expr.source, format!("outer-body-statement-expression-{order}"));
                        assert!(hir.owns_occurrence(&expr.occurrence));
                        assert_eq!(hir.occurrence_source_key(&expr.occurrence).expect("statement expression occurrence"), Some(&expr.source));
                        assert_eq!(position.range, expr.range);
                        entries.push(BodyEntryEvidence {
                            kind: "statement-expression",
                            source_order: order,
                            local_index: Some(index.ordinal()),
                            binding_ordinal: None,
                            occurrence_ordinal: Some(expr.occurrence.ordinal()),
                            range: Some(expr.range.clone()),
                            source_position: Some(position.position),
                            source_position_kind: Some(position.position_kind),
                            source_position_range: Some(position.range),
                            index_value: Some(index.clone()),
                        });
                    }
                    LocalSourceStatement::Binding(binding_ordinal) => {
                        let binding = source.bindings().get(*binding_ordinal as usize)
                            .expect("StatementBlock binding ordinal belongs to LocalSource bindings");
                        assert_eq!(binding.id.ordinal(), *binding_ordinal, "statement binding ordinal must select that exact binding");
                        assert_eq!(binding.id.source_root(), root, "statement binding must carry selected root");
                        assert!(hir.owns_source_root(binding.id.source_root()));
                        let position = position_for_key(
                            parsed,
                            artifact,
                            &binding.binder_source,
                            format!("outer-body-statement-binding-{order}"),
                        );
                        entries.push(BodyEntryEvidence {
                            kind: "statement-binding",
                            source_order: order,
                            local_index: None,
                            binding_ordinal: Some(binding.id.ordinal()),
                            occurrence_ordinal: None,
                            range: Some(binding.range.clone()),
                            source_position: Some(position.position),
                            source_position_kind: Some(position.position_kind),
                            source_position_range: Some(position.range),
                            index_value: None,
                        });
                    }
                }
            }
            let expr = expression(source, root, final_expression);
            let position = position_for_key(parsed, artifact, &expr.source, "outer-body-final-expression");
            assert!(hir.owns_occurrence(&expr.occurrence));
            assert_eq!(hir.occurrence_source_key(&expr.occurrence).expect("final expression occurrence"), Some(&expr.source));
            assert_eq!(position.range, expr.range);
            entries.push(BodyEntryEvidence {
                kind: "final-expression",
                source_order: statements.len(),
                local_index: Some(final_expression.ordinal()),
                binding_ordinal: None,
                occurrence_ordinal: Some(expr.occurrence.ordinal()),
                range: Some(expr.range.clone()),
                source_position: Some(position.position),
                source_position_kind: Some(position.position_kind),
                source_position_range: Some(position.range),
                index_value: Some(final_expression.clone()),
            });
            entries
        }
        _ => panic!("outer Lambda body must retain its Sequence or StatementBlock constructor"),
    }
}

fn name_use(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    source: &LocalSource,
    root: &SourceRootId,
    label: &'static str,
    index: &LocalSourceIndex,
    expected_parameter: &HirParameterId,
) -> NameUseEvidence {
    let expr = expression(source, root, index);
    let LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(parameter) } = &expr.form else {
        panic!("{label} must be an actual source Name resolving to a Parameter");
    };
    assert_eq!(parameter, expected_parameter, "{label} must resolve to the exact selected parameter identity");
    assert_eq!(parameter.source_root(), root, "resolved parameter must carry selected source root");
    assert!(hir.owns_source_root(parameter.source_root()));
    assert!(parsed.owns_source_key(&expr.source));
    assert!(artifact.parsed().owns_source_key(&expr.source));
    assert!(hir.owns_occurrence(&expr.occurrence));
    assert_eq!(hir.occurrence_source_key(&expr.occurrence).expect("Name occurrence source"), Some(&expr.source));
    let position = artifact.source_position(&expr.source).expect("Name source position");
    let source_position = artifact.position(&position).expect("Name position belongs to selected artifact");
    assert_eq!(source_position.range(), &expr.range);
    NameUseEvidence {
        label,
        index: index.ordinal(),
        occurrence: expr.occurrence.ordinal(),
        spelling: spelling.to_string(),
        parameter: parameter.ordinal(),
        range: expr.range.clone(),
        source_position: position.ordinal(),
    }
}

fn range_literal(range: &Range<usize>) -> String {
    format!("({}, {})", range.start, range.end)
}

fn lean_option(value: Option<usize>) -> String {
    value.map_or_else(|| "none".to_string(), |n| format!("some {n}"))
}

fn emit(
    parsed: &ParsedFile,
    definition_position: &SourcePositionEvidence,
    source_positions: &[SourcePositionEvidence],
    outer: &LocalSourceExpr,
    outer_index: &LocalSourceIndex,
    outer_parameter: &LocalSourceParameter,
    outer_binder: &SourcePositionEvidence,
    outer_body: &LocalSourceExpr,
    outer_body_index: &LocalSourceIndex,
    body_entries: &[BodyEntryEvidence],
    apply: &LocalSourceExpr,
    apply_index: &LocalSourceIndex,
    raw_callee_expr: &LocalSourceExpr,
    raw_callee_index: &LocalSourceIndex,
    raw_argument_index: &LocalSourceIndex,
    projections: &[GroupProjectionEvidence],
    inner_index: &LocalSourceIndex,
    inner: &LocalSourceExpr,
    inner_parameter: &LocalSourceParameter,
    inner_binder: &SourcePositionEvidence,
    inner_body_index: &LocalSourceIndex,
    argument: &NameUseEvidence,
    inner_body: &NameUseEvidence,
    sibling: &NameUseEvidence,
) -> String {
    let mut out = String::new();
    writeln!(out, "-- Generated only by the authenticated Rust owner path in tools/inline-authentic-extraction/src/main.rs.").unwrap();
    writeln!(out, "-- This is a finite source/HIR trace, not an allocation law or a parent theorem.").unwrap();
    writeln!(out, "namespace YulangClosure.OriginalAuthenticInlineExtractionTraceR2").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "structure TraceSourcePosition where").unwrap();
    writeln!(out, "  label : String").unwrap();
    writeln!(out, "  kind : String").unwrap();
    writeln!(out, "  positionOrdinal : Nat").unwrap();
    writeln!(out, "  byteRange : Nat × Nat").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "structure TraceBodyEntry where").unwrap();
    writeln!(out, "  kind : String").unwrap();
    writeln!(out, "  sourceOrder : Nat").unwrap();
    writeln!(out, "  localSourceIndex : Option Nat").unwrap();
    writeln!(out, "  bindingOrdinal : Option Nat").unwrap();
    writeln!(out, "  occurrenceOrdinal : Option Nat").unwrap();
    writeln!(out, "  byteRange : Option (Nat × Nat)").unwrap();
    writeln!(out, "  sourcePositionOrdinal : Option Nat").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "structure TraceGroupProjection where").unwrap();
    writeln!(out, "  groupIndex : Nat").unwrap();
    writeln!(out, "  innerIndex : Nat").unwrap();
    writeln!(out, "  groupOccurrence : Nat").unwrap();
    writeln!(out, "  innerOccurrence : Nat").unwrap();
    writeln!(out, "  groupRange : Nat × Nat").unwrap();
    writeln!(out, "  innerRange : Nat × Nat").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "structure TraceNameResolution where").unwrap();
    writeln!(out, "  label : String").unwrap();
    writeln!(out, "  sourceIndex : Nat").unwrap();
    writeln!(out, "  occurrenceOrdinal : Nat").unwrap();
    writeln!(out, "  spelling : String").unwrap();
    writeln!(out, "  resolutionKind : String").unwrap();
    writeln!(out, "  parameterOrdinal : Nat").unwrap();
    writeln!(out, "  sourcePositionOrdinal : Nat").unwrap();
    writeln!(out, "  byteRange : Nat × Nat").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "def traceSchemaVersion : Nat := 1").unwrap();
    writeln!(out, "def inputUtf8 : String := {:?}", parsed.source()).unwrap();
    writeln!(out, "def inputByteLength : Nat := {}", parsed.source().len()).unwrap();
    writeln!(out, "def sourceModule : String := {:?}", MODULE).unwrap();
    writeln!(out, "def sourceFile : String := {:?}", FILE).unwrap();
    writeln!(out, "def sourceRootKind : String := \"Definition\"").unwrap();
    writeln!(out, "def definitionSourcePositionOrdinal : Nat := {}", definition_position.position).unwrap();
    writeln!(out, "def definitionSourceRange : Nat × Nat := {}", range_literal(&definition_position.range)).unwrap();
    writeln!(out, "def outerLambdaRange : Nat × Nat := {}", range_literal(&outer.range)).unwrap();
    writeln!(out, "def outerLambdaOccurrenceOrdinal : Nat := {}", outer.occurrence.ordinal()).unwrap();
    writeln!(out, "def outerParameterOrdinal : Nat := {}", outer_parameter.id.ordinal()).unwrap();
    writeln!(out, "def outerParameterSpelling : String := {:?}", outer_parameter.spelling).unwrap();
    writeln!(out, "def outerBinderTokenRange : Nat × Nat := {}", range_literal(&outer_binder.range)).unwrap();
    writeln!(out, "def outerBinderEqualsRegisteredRange : Bool := true").unwrap();
    writeln!(out, "def outerLambdaIndexOrdinal : Nat := {}", outer_index.ordinal()).unwrap();
    writeln!(out, "def outerBodyForm : String := {:?}", match &outer.form {
        LocalSourceForm::Lambda { .. } => match &outer_body.form {
            LocalSourceForm::Sequence { .. } => "Sequence",
            LocalSourceForm::StatementBlock { .. } => "StatementBlock",
            _ => "unsupported",
        },
        _ => "unsupported",
    }).unwrap();
    writeln!(out, "def outerBodyRange : Nat × Nat := {}", range_literal(&outer_body.range)).unwrap();
    writeln!(out, "def outerBodyOccurrenceOrdinal : Nat := {}", outer_body.occurrence.ordinal()).unwrap();
    writeln!(out, "def outerBodyIndexOrdinal : Nat := {}", outer_body_index.ordinal()).unwrap();
    writeln!(out, "def applyIndexOrdinal : Nat := {}", apply_index.ordinal()).unwrap();
    writeln!(out, "def applyOccurrenceOrdinal : Nat := {}", apply.occurrence.ordinal()).unwrap();
    writeln!(out, "def applyRange : Nat × Nat := {}", range_literal(&apply.range)).unwrap();
    let apply_source_form = match &apply.form {
        LocalSourceForm::Apply { source_form, .. } => source_form,
        _ => unreachable!(),
    };
    writeln!(out, "def applySourceForm : String := {:?}", format!("{apply_source_form:?}")).unwrap();
    writeln!(out, "def rawApplyCalleeIndexOrdinal : Nat := {}", raw_callee_index.ordinal()).unwrap();
    writeln!(out, "def rawApplyCalleeOccurrenceOrdinal : Nat := {}", raw_callee_expr.occurrence.ordinal()).unwrap();
    writeln!(out, "def rawApplyCalleeForm : String := \"Group\"").unwrap();
    writeln!(out, "def rawApplyCalleeRange : Nat × Nat := {}", range_literal(&raw_callee_expr.range)).unwrap();
    writeln!(out, "def rawApplyArgumentIndexOrdinal : Nat := {}", raw_argument_index.ordinal()).unwrap();
    writeln!(out, "def rawApplyArgumentOccurrenceOrdinal : Nat := {}", argument.occurrence).unwrap();
    writeln!(out, "def rawApplyArgumentForm : String := \"Name\"").unwrap();
    writeln!(out, "def rawApplyArgumentRange : Nat × Nat := {}", range_literal(&argument.range)).unwrap();
    writeln!(out, "def projectedInnerLambdaIndexOrdinal : Nat := {}", inner_index.ordinal()).unwrap();
    writeln!(out, "def projectedCalleeForm : String := \"Lambda\"").unwrap();
    writeln!(out, "def innerLambdaRange : Nat × Nat := {}", range_literal(&inner.range)).unwrap();
    writeln!(out, "def innerLambdaOccurrenceOrdinal : Nat := {}", inner.occurrence.ordinal()).unwrap();
    writeln!(out, "def innerParameterOrdinal : Nat := {}", inner_parameter.id.ordinal()).unwrap();
    writeln!(out, "def innerParameterSpelling : String := {:?}", inner_parameter.spelling).unwrap();
    writeln!(out, "def innerBinderTokenRange : Nat × Nat := {}", range_literal(&inner_binder.range)).unwrap();
    writeln!(out, "def innerBinderEqualsRegisteredRange : Bool := true").unwrap();
    writeln!(out, "def innerBodyIndexOrdinal : Nat := {}", inner_body_index.ordinal()).unwrap();
    writeln!(out, "def innerBodyOccurrenceOrdinal : Nat := {}", inner_body.occurrence).unwrap();
    writeln!(out, "def sameSpellingNestedParametersAreDistinct : Bool := true").unwrap();
    writeln!(out, "def originalAllocationStatus : String := \"open_not_established_by_this_trace\"").unwrap();
    writeln!(out, "def sourcePositions : List TraceSourcePosition := [").unwrap();
    for evidence in source_positions {
        writeln!(out, "  {{ label := {:?}, kind := {:?}, positionOrdinal := {}, byteRange := {} }},",
            evidence.label, evidence.position_kind, evidence.position, range_literal(&evidence.range)).unwrap();
    }
    writeln!(out, "]").unwrap();
    writeln!(out, "def outerBodyIncidence : List TraceBodyEntry := [").unwrap();
    for entry in body_entries {
        let range = entry.range.as_ref().map(range_literal);
        writeln!(out, "  {{ kind := {:?}, sourceOrder := {}, localSourceIndex := {}, bindingOrdinal := {}, occurrenceOrdinal := {}, byteRange := {}, sourcePositionOrdinal := {} }},",
            entry.kind,
            entry.source_order,
            lean_option(entry.local_index.map(|n| n as usize)),
            lean_option(entry.binding_ordinal.map(|n| n as usize)),
            lean_option(entry.occurrence_ordinal.map(|n| n as usize)),
            range.map_or_else(|| "none".to_string(), |r| format!("some {r}")),
            lean_option(entry.source_position),
        ).unwrap();
    }
    writeln!(out, "]").unwrap();
    writeln!(out, "def groupProjectionPath : List TraceGroupProjection := [").unwrap();
    for projection in projections {
        writeln!(out, "  {{ groupIndex := {}, innerIndex := {}, groupOccurrence := {}, innerOccurrence := {}, groupRange := {}, innerRange := {} }},",
            projection.group_index, projection.inner_index, projection.group_occurrence,
            projection.inner_occurrence, range_literal(&projection.group_range), range_literal(&projection.inner_range)).unwrap();
    }
    writeln!(out, "]").unwrap();
    writeln!(out, "def nameResolutions : List TraceNameResolution := [").unwrap();
    for name in [argument, inner_body, sibling] {
        writeln!(out, "  {{ label := {:?}, sourceIndex := {}, occurrenceOrdinal := {}, spelling := {:?}, resolutionKind := \"Parameter\", parameterOrdinal := {}, sourcePositionOrdinal := {}, byteRange := {} }},",
            name.label, name.index, name.occurrence, name.spelling, name.parameter,
            name.source_position, range_literal(&name.range)).unwrap();
    }
    writeln!(out, "]").unwrap();
    writeln!(out, "def rawCalleeIsNotProjectedIdentity : Bool := true").unwrap();
    writeln!(out, "def foreignOwnerChecks : List String := [\"equal-text foreign SourceNodeKey rejected as ForeignParse\", \"foreign parameter identity rejected as ForeignHirArtifact\", \"foreign parse artifact rejected selected parameter origin as ForeignParse\", \"foreign HIR occurrence rejected by selected HIR\"]").unwrap();
    writeln!(out, "def originalSiteNameContextEventAllocation : String := \"not supplied; no Rust ordinal is interpreted as an original coordinate\"").unwrap();
    writeln!(out, "end YulangClosure.OriginalAuthenticInlineExtractionTraceR2").unwrap();
    out
}

fn authenticate_foreign_rejection(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    inner_parameter: &LocalSourceParameter,
    selected_inner_occurrence: &yu_hir::HirOccurrenceId,
) -> Result<(), Box<dyn std::error::Error>> {
    let foreign_parse = parse(INPUT);
    assert_eq!(foreign_parse.source(), parsed.source(), "foreign parse has identical bytes");
    let foreign_key = foreign_parse.source_root().key();
    assert!(!parsed.owns_source_key(&foreign_key), "equal bytes must not authenticate a foreign SourceNodeKey");
    assert!(matches!(artifact.source_position(&foreign_key), Err(SourceIdentityError::ForeignParse)));

    let foreign_hir = lower(&foreign_parse)?;
    let foreign_artifact = ShadowArtifact::from_parsed(foreign_parse.clone()).expect("foreign parse artifact");
    let foreign_binding = foreign_hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "value" => Some(binding),
        _ => None,
    }).expect("foreign fixture binding");
    let foreign_root = SourceRootId::Definition(foreign_binding.definition_root().clone());
    assert!(!hir.owns_source_root(&foreign_root), "foreign definition root must be rejected by selected HIR");
    assert!(foreign_hir.owns_source_root(&foreign_root));
    let foreign_definition_key = foreign_hir.definition_source_key(foreign_binding.definition_root())?
        .expect("foreign definition retains its own SourceNodeKey");
    assert!(!parsed.owns_source_key(foreign_definition_key), "foreign HIR definition key must be rejected by selected parse");
    assert!(matches!(artifact.source_position(foreign_definition_key), Err(SourceIdentityError::ForeignParse)));
    let foreign_source = foreign_hir.local_source_for(&foreign_root)?.expect("foreign LocalSource");
    let foreign_inner_parameters: Vec<_> = foreign_source.expressions().iter().filter_map(|expr| match &expr.form {
        LocalSourceForm::Lambda { parameter, .. }
            if parameter.spelling.as_ref() == "x" && matches!(&parameter.scope, LocalSourceScope::Expression(_)) => Some(parameter),
        _ => None,
    }).collect();
    assert_eq!(foreign_inner_parameters.len(), 1, "foreign fixture has one nested x Lambda");
    let foreign_inner = foreign_inner_parameters[0];
    assert!(matches!(
        artifact.parameter_source_origin(&hir, &foreign_inner.id),
        Err(SourceIdentityError::ForeignHirArtifact),
    ), "selected artifact/HIR must reject foreign parameter identity");
    assert!(matches!(
        foreign_artifact.parameter_source_origin(&hir, &inner_parameter.id),
        Err(SourceIdentityError::ForeignParse),
    ), "foreign parse artifact must reject selected HIR source identity");

    assert!(hir.owns_occurrence(selected_inner_occurrence));
    assert!(hir.occurrence_source_key(selected_inner_occurrence)?.is_some());
    let foreign_occurrence = foreign_source.expressions().iter().find_map(|expr| match &expr.form {
        LocalSourceForm::Lambda { parameter, .. } if parameter.id == foreign_inner.id => Some(&expr.occurrence),
        _ => None,
    }).expect("foreign inner Lambda occurrence");
    assert!(!hir.owns_occurrence(foreign_occurrence), "selected HIR rejects foreign occurrence brand");
    assert!(foreign_hir.owns_occurrence(foreign_occurrence));
    assert!(hir.occurrence_source_key(foreign_occurrence).is_err());
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let parsed = parse(INPUT);
    let hir = lower(&parsed)?;
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).expect("selected ShadowArtifact");
    let binding = hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "value" => Some(binding),
        _ => None,
    }).expect("fixture binding");
    let root = SourceRootId::Definition(binding.definition_root().clone());
    assert!(hir.owns_source_root(&root));
    let definition_key = hir.definition_source_key(binding.definition_root())?
        .expect("definition root retains its exact parsed source key");
    let definition_position = position_for_key(&parsed, &artifact, definition_key, "definition");
    assert_eq!(definition_position.range, *binding.range(), "definition key range must equal admitted binding range");
    let source = hir.local_source_for(&root)?.expect("supported LocalSource carrier");
    let mut source_positions = authenticate_expressions(&parsed, &artifact, &hir, &root, source);
    source_positions.insert(0, definition_position.clone());

    let outer_index = source.body().clone();
    let outer = expression(source, &root, &outer_index);
    let LocalSourceForm::Lambda { parameter: outer_parameter, body: outer_body_index } = &outer.form else {
        panic!("fixture LocalSource body must be the outer inline Lambda");
    };
    assert_eq!(outer_parameter.spelling.as_ref(), "x");
    assert_eq!(outer_parameter.source, outer.source, "outer parameter origin must name the exact enclosing Lambda SourceNodeKey");
    assert!(matches!(&outer_parameter.scope, LocalSourceScope::Definition(id) if id == binding.definition_root()));
    assert_eq!(outer_parameter.id.source_root(), &root);
    let (outer_lambda_source, outer_binder) = inline_parameter_positions(
        &parsed, &artifact, &hir, &root, outer_parameter, "outer",
    );
    source_positions.push(outer_lambda_source);
    source_positions.push(outer_binder.clone());

    let mut candidates = Vec::new();
    for candidate in source.expressions() {
        let LocalSourceForm::Apply { callee: raw_callee, argument: raw_argument, .. } = &candidate.form else { continue; };
        let (projections, terminal_callee) = project_groups(
            &parsed, &artifact, &hir, source, &root, raw_callee,
        );
        let projected = expression(source, &root, terminal_callee);
        let LocalSourceForm::Lambda { parameter: inner_parameter, body: inner_body_index } = &projected.form else { continue; };
        if inner_parameter.spelling.as_ref() != "x" || inner_parameter.id == outer_parameter.id { continue; }
        let argument_expr = expression(source, &root, raw_argument);
        let inner_body_expr = expression(source, &root, inner_body_index);
        let argument_is_outer = matches!(&argument_expr.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
                if spelling.as_ref() == "x" && id == &outer_parameter.id);
        let body_is_inner = matches!(&inner_body_expr.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
                if spelling.as_ref() == "x" && id == &inner_parameter.id);
        if argument_is_outer && body_is_inner {
            candidates.push((candidate, raw_callee, raw_argument, projections, terminal_callee,
                inner_parameter, inner_body_index));
        }
    }
    assert_eq!(candidates.len(), 1, "fixture must contain one Apply with the nested same-spelling Lambda and outer argument");
    let (apply, raw_callee_index, raw_argument_index, projections, inner_index, inner_parameter, inner_body_index) =
        candidates.pop().expect("unique authentic Apply");
    assert!(!projections.is_empty(), "raw parenthesized Apply callee must have an explicit Group projection");
    assert_ne!(raw_callee_index, inner_index, "raw Group callee index must remain distinct from projected Lambda index");
    assert!(matches!(&expression(source, &root, raw_callee_index).form, LocalSourceForm::Group { .. }));
    assert!(matches!(&expression(source, &root, raw_argument_index).form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(_), .. }));
    assert!(apply.range.start < apply.range.end);
    let inner = expression(source, &root, inner_index);
    let LocalSourceForm::Lambda { parameter: selected_inner_parameter, body: selected_inner_body } = &inner.form else { unreachable!() };
    assert_eq!(selected_inner_parameter.id, inner_parameter.id);
    assert_eq!(selected_inner_body, inner_body_index, "terminal projected Lambda body index is exact");
    assert_eq!(inner_parameter.spelling.as_ref(), outer_parameter.spelling.as_ref());
    assert_eq!(inner_parameter.source, inner.source, "inner parameter origin must name the exact projected Lambda SourceNodeKey");
    assert_ne!(inner_parameter.id, outer_parameter.id);
    assert_eq!(inner_parameter.id.source_root(), &root);
    assert!(matches!(&inner_parameter.scope,
        LocalSourceScope::Expression(parent) if parent.source_root() == &root),
        "nested inline parameter must retain its enclosing expression scope");
    let (inner_lambda_source, inner_binder) = inline_parameter_positions(
        &parsed, &artifact, &hir, &root, inner_parameter, "inner",
    );
    source_positions.push(inner_lambda_source);
    source_positions.push(inner_binder.clone());

    let outer_body_expr = expression(source, &root, outer_body_index);
    let body_entries = body_entries(
        &parsed, &artifact, &hir, source, &root, outer_body_expr,
    );
    let apply_entries: Vec<_> = body_entries.iter().enumerate().filter_map(|(position, entry)| {
        let index = entry.index_value.as_ref()?;
        std::ptr::eq(expression(source, &root, index), apply).then_some((position, index.clone()))
    }).collect();
    assert_eq!(apply_entries.len(), 1, "actual Apply must occur exactly once in complete ordered outer-body incidence");
    let (apply_entry_order, apply_index) = apply_entries[0].clone();
    let sibling_candidates: Vec<_> = body_entries.iter().enumerate().skip(apply_entry_order + 1).filter_map(|(order, entry)| {
        let index = entry.index_value.as_ref()?;
        let sibling_expr = expression(source, &root, index);
        let LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) } = &sibling_expr.form else { return None; };
        (spelling.as_ref() == "x" && id == &outer_parameter.id && sibling_expr.range.start > apply.range.end)
            .then_some((order, index.clone()))
    }).collect();
    assert_eq!(sibling_candidates.len(), 1, "one later direct sibling must restore outer x resolution");
    let (_sibling_order, sibling_index) = sibling_candidates[0].clone();
    let sibling_use = name_use(
        &parsed, &artifact, &hir, source, &root, "restored-sibling", &sibling_index, &outer_parameter.id,
    );
    let argument_use = name_use(
        &parsed, &artifact, &hir, source, &root, "apply-argument", raw_argument_index, &outer_parameter.id,
    );
    let inner_body_use = name_use(
        &parsed, &artifact, &hir, source, &root, "inner-body", inner_body_index, &inner_parameter.id,
    );
    assert_eq!(sibling_use.index, sibling_index.ordinal());
    assert_eq!(argument_use.index, raw_argument_index.ordinal());
    assert_eq!(inner_body_use.index, inner_body_index.ordinal());

    let (raw_callee_expr, projected_inner_expr) = {
        let raw = expression(source, &root, raw_callee_index);
        let projected = expression(source, &root, inner_index);
        (raw, projected)
    };
    let raw_position = position_for_key(&parsed, &artifact, &raw_callee_expr.source, "raw-apply-callee");
    let argument_position = position_for_key(&parsed, &artifact, &expression(source, &root, raw_argument_index).source, "raw-apply-argument");
    let apply_position = position_for_key(&parsed, &artifact, &apply.source, "apply");
    let outer_body_position = position_for_key(&parsed, &artifact, &outer_body_expr.source, "outer-body");
    let inner_position = position_for_key(&parsed, &artifact, &projected_inner_expr.source, "projected-inner-lambda");
    source_positions.extend([raw_position, argument_position, apply_position, outer_body_position, inner_position]);
    for (step, projection) in projections.iter().enumerate() {
        let group = source.expressions().get(projection.group_index as usize).expect("Group index belongs to source expressions");
        let inner_expr = source.expressions().get(projection.inner_index as usize).expect("Group child index belongs to source expressions");
        source_positions.push(position_for_key(&parsed, &artifact, &group.source, format!("group-projection-{step}")));
        source_positions.push(position_for_key(&parsed, &artifact, &inner_expr.source, format!("group-projection-{step}-inner")));
    }
    for entry in &body_entries {
        if let (Some(position), Some(position_kind), Some(range)) =
            (entry.source_position, entry.source_position_kind, entry.source_position_range.clone())
        {
            source_positions.push(SourcePositionEvidence {
                label: format!("outer-body-entry-{}", entry.source_order),
                position_kind,
                position,
                range,
            });
        }
    }

    authenticate_foreign_rejection(&parsed, &artifact, &hir, inner_parameter, &inner.occurrence)?;
    let raw_callee_expr = expression(source, &root, raw_callee_index);
    let generated = emit(
        &parsed,
        &definition_position,
        &source_positions,
        outer,
        &outer_index,
        outer_parameter,
        &outer_binder,
        outer_body_expr,
        outer_body_index,
        &body_entries,
        apply,
        &apply_index,
        raw_callee_expr,
        raw_callee_index,
        raw_argument_index,
        &projections,
        inner_index,
        inner,
        inner_parameter,
        &inner_binder,
        inner_body_index,
        &argument_use,
        &inner_body_use,
        &sibling_use,
    );
    std::fs::write(OUTPUT, generated)?;
    println!("source_root={:?} source_bytes={} output={}", source.source_root(), parsed.source().len(), OUTPUT);
    println!("authenticated_parse_keys={} authenticated_hir_occurrences={} source_position_rows={}",
        source.expressions().len(), source.expressions().len(), source_positions.len());
    println!("apply_raw_callee_index={} argument_index={} group_projection_edges={} projected_lambda_index={}",
        raw_callee_index.ordinal(), raw_argument_index.ordinal(), projections.len(), inner_index.ordinal());
    println!("outer_parameter={} inner_parameter={} same_spelling=true identities_distinct=true", outer_parameter.id.ordinal(), inner_parameter.id.ordinal());
    println!("body_form={} body_range={:?} ordered_incidence_entries={}", body_form_name(&outer_body_expr.form), outer_body_expr.range, body_entries.len());
    println!("foreign_parse=REJECTED(ForeignParse) foreign_hir=REJECTED(ForeignHirArtifact); original_allocator=OPEN");
    Ok(())
}

fn body_form_name(form: &LocalSourceForm) -> &'static str {
    match form {
        LocalSourceForm::Sequence { .. } => "Sequence",
        LocalSourceForm::StatementBlock { .. } => "StatementBlock",
        _ => "unsupported",
    }
}
