use std::{fmt::Write as _, sync::Arc};

use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, HirParameterId, LocalSource,
    LocalSourceExpr, LocalSourceForm, LocalSourceIndex, LocalSourceResolution, ModuleIdentity,
    SemanticImports, SourceRootId,
    shadow::{
        ParameterSourceOrigin, ShadowArtifact, SourceIdentityError, lower_module_with_local_source,
    },
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const INPUT: &str = "my value = \\x -> { (\\x -> x) x; x }";
const OUTPUT: &str = "notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTrace.lean";

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
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "inline-authentic-extraction",
            "inline_authentic_extraction.yu",
        ))),
        parsed,
        SemanticImports::empty(),
    )
}

fn children(form: &LocalSourceForm) -> Vec<&LocalSourceIndex> {
    match form {
        LocalSourceForm::Apply { callee, argument, .. } => vec![callee, argument],
        LocalSourceForm::Lambda { body, .. } => vec![body],
        LocalSourceForm::Group { inner } => vec![inner],
        LocalSourceForm::Sequence { items } => items.iter().collect(),
        LocalSourceForm::StatementBlock { statements, final_expression } => {
            let mut out = Vec::new();
            for statement in statements {
                if let yu_hir::LocalSourceStatement::Expression(index) = statement {
                    out.push(index);
                }
            }
            out.push(final_expression);
            out
        }
        _ => Vec::new(),
    }
}

fn expression<'a>(source: &'a LocalSource, index: &LocalSourceIndex) -> &'a LocalSourceExpr {
    source.expression(index).expect("index must belong to the authenticated LocalSource")
}

fn ungroup<'a>(source: &'a LocalSource, mut index: &'a LocalSourceIndex) -> &'a LocalSourceIndex {
    loop {
        match &expression(source, index).form {
            LocalSourceForm::Group { inner } => index = inner,
            _ => return index,
        }
    }
}

fn inline_origin(
    artifact: &ShadowArtifact,
    hir: &HirModule,
    parameter: &HirParameterId,
) -> (yu_hir::shadow::PositionId, yu_hir::shadow::PositionId, std::ops::Range<usize>) {
    match artifact.parameter_source_origin(hir, parameter).expect("authentic parameter origin") {
        ParameterSourceOrigin::InlineLambda { lambda, binder } => {
            let lambda_range = artifact.position(&lambda).expect("owned Lambda key").range().clone();
            let binder_range = artifact.position(&binder).expect("owned binder token").range().clone();
            (lambda, binder, lambda_range.start..binder_range.end)
        }
        ParameterSourceOrigin::IdentifierPattern(_) => panic!("fixture requires an inline Lambda origin"),
    }
}

fn authenticate_exprs(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    hir: &HirModule,
    root: &SourceRootId,
    source: &LocalSource,
) {
    assert!(hir.owns_source_root(root), "source root must belong to this HIR artifact");
    assert_eq!(source.source_root(), root, "LocalSource must retain the exact selected root");
    for expr in source.expressions() {
        assert!(parsed.owns_source_key(&expr.source), "expression key must belong to the input parse");
        assert!(artifact.parsed().owns_source_key(&expr.source), "shadow artifact must share the parse owner");
        assert!(hir.owns_occurrence(&expr.occurrence), "occurrence must belong to the input HIR");
        assert_eq!(
            hir.occurrence_source_key(&expr.occurrence).expect("same HIR occurrence"),
            Some(&expr.source),
            "occurrence must retain this exact parse-owned SourceNodeKey",
        );
        let position = artifact.source_position(&expr.source).expect("same-parse source key");
        assert_eq!(
            artifact.position(&position).expect("same shadow artifact position").range(),
            &expr.range,
            "retained LocalSource range must agree with the exact keyed CST node",
        );
    }
}

fn range_of(artifact: &ShadowArtifact, key: &yu_hir::shadow::SourceNodeKey) -> std::ops::Range<usize> {
    let position = artifact.source_position(key).expect("authenticated SourceNodeKey");
    artifact.position(&position).expect("authenticated source position").range().clone()
}

fn emit(
    parsed: &ParsedFile,
    artifact: &ShadowArtifact,
    source: &LocalSource,
    outer: &LocalSourceExpr,
    outer_parameter: &yu_hir::LocalSourceParameter,
    apply: &LocalSourceExpr,
    inner: &LocalSourceExpr,
    inner_parameter: &yu_hir::LocalSourceParameter,
    outer_body_index: &LocalSourceIndex,
    apply_index: &LocalSourceIndex,
    actual_callee_index: &LocalSourceIndex,
    inner_lambda_index: &LocalSourceIndex,
    inner_body_index: &LocalSourceIndex,
    argument_index: &LocalSourceIndex,
    sibling_index: &LocalSourceIndex,
    inner_body: &LocalSourceExpr,
    argument: &LocalSourceExpr,
    sibling: &LocalSourceExpr,
    outer_origin: &(yu_hir::shadow::PositionId, yu_hir::shadow::PositionId, std::ops::Range<usize>),
    inner_origin: &(yu_hir::shadow::PositionId, yu_hir::shadow::PositionId, std::ops::Range<usize>),
) -> String {
    let mut out = String::new();
    writeln!(out, "-- Generated by tools/inference-playground/src/bin/inline_authentic_extraction.rs.").unwrap();
    writeln!(out, "-- Finite authenticated Rust-owner trace; numeric projections below are not Site/Name allocations.").unwrap();
    writeln!(out, "namespace YulangClosure.OriginalAuthenticInlineExtractionTrace").unwrap();
    writeln!(out, "").unwrap();
    writeln!(out, "def inputUtf8 : String := {:?}", parsed.source()).unwrap();
    writeln!(out, "def inputByteLength : Nat := {}", parsed.source().len()).unwrap();
    writeln!(out, "def outerLambdaRange : Nat × Nat := ({}, {})", outer.range.start, outer.range.end).unwrap();
    writeln!(out, "def outerBinderRange : Nat × Nat := ({}, {})", outer_parameter.range.start, outer_parameter.range.end).unwrap();
    writeln!(out, "def applyRange : Nat × Nat := ({}, {})", apply.range.start, apply.range.end).unwrap();
    writeln!(out, "def innerLambdaRange : Nat × Nat := ({}, {})", range_of(artifact, &inner_parameter.source).start, range_of(artifact, &inner_parameter.source).end).unwrap();
    writeln!(out, "def innerBinderRange : Nat × Nat := ({}, {})", inner_parameter.range.start, inner_parameter.range.end).unwrap();
    writeln!(out, "def innerBodyNameRange : Nat × Nat := ({}, {})", inner_body.range.start, inner_body.range.end).unwrap();
    writeln!(out, "def applyArgumentRange : Nat × Nat := ({}, {})", argument.range.start, argument.range.end).unwrap();
    writeln!(out, "def restoredSiblingNameRange : Nat × Nat := ({}, {})", sibling.range.start, sibling.range.end).unwrap();
    writeln!(out, "def outerParameterOrdinal : Nat := {}", outer_parameter.id.ordinal()).unwrap();
    writeln!(out, "def innerParameterOrdinal : Nat := {}", inner_parameter.id.ordinal()).unwrap();
    writeln!(out, "def innerBodyResolutionParameterOrdinal : Nat := {}", inner_parameter.id.ordinal()).unwrap();
    writeln!(out, "def applyArgumentResolutionParameterOrdinal : Nat := {}", outer_parameter.id.ordinal()).unwrap();
    writeln!(out, "def restoredSiblingResolutionParameterOrdinal : Nat := {}", outer_parameter.id.ordinal()).unwrap();
    writeln!(out, "def outerLambdaOccurrenceOrdinal : Nat := {}", outer.occurrence.ordinal()).unwrap();
    writeln!(out, "def applyOccurrenceOrdinal : Nat := {}", apply.occurrence.ordinal()).unwrap();
    writeln!(out, "def innerLambdaOccurrenceOrdinal : Nat := {}", inner.occurrence.ordinal()).unwrap();
    writeln!(out, "def innerBodyOccurrenceOrdinal : Nat := {}", inner_body.occurrence.ordinal()).unwrap();
    writeln!(out, "def argumentOccurrenceOrdinal : Nat := {}", argument.occurrence.ordinal()).unwrap();
    writeln!(out, "def restoredSiblingOccurrenceOrdinal : Nat := {}", sibling.occurrence.ordinal()).unwrap();
    writeln!(out, "def outerBinderTokenRange : Nat × Nat := ({}, {})", outer_origin.2.start, outer_origin.2.end).unwrap();
    writeln!(out, "def innerBinderTokenRange : Nat × Nat := ({}, {})", inner_origin.2.start, inner_origin.2.end).unwrap();
    writeln!(out, "def sourceRootKind : String := \"definition\"").unwrap();
    writeln!(out, "def localSourceBodyOrdinal : Nat := {}", source.body().ordinal()).unwrap();
    writeln!(out, "def outerBodyIndexOrdinal : Nat := {}", outer_body_index.ordinal()).unwrap();
    writeln!(out, "def applyIndexOrdinal : Nat := {}", apply_index.ordinal()).unwrap();
    writeln!(out, "def actualApplyCalleeIndexOrdinal : Nat := {}", actual_callee_index.ordinal()).unwrap();
    writeln!(out, "def innerLambdaIndexOrdinal : Nat := {}", inner_lambda_index.ordinal()).unwrap();
    writeln!(out, "def innerBodyIndexOrdinal : Nat := {}", inner_body_index.ordinal()).unwrap();
    writeln!(out, "def applyArgumentIndexOrdinal : Nat := {}", argument_index.ordinal()).unwrap();
    writeln!(out, "def restoredSiblingIndexOrdinal : Nat := {}", sibling_index.ordinal()).unwrap();
    writeln!(out, "def outerNameSpelling : String := \"x\"").unwrap();
    writeln!(out, "def innerNameSpelling : String := \"x\"").unwrap();
    writeln!(out, "def innerBodyResolvesToInnerParameter : Bool := true").unwrap();
    writeln!(out, "def applyArgumentResolvesToOuterParameter : Bool := true").unwrap();
    writeln!(out, "def laterSiblingResolvesToOuterParameter : Bool := true").unwrap();
    writeln!(out, "def applyCalleeIsInnerLambda : Bool := true").unwrap();
    writeln!(out, "def allSourceNodesUseOneParseOwner : Bool := true").unwrap();
    writeln!(out, "def allOccurrencesUseOneHirOwner : Bool := true").unwrap();
    writeln!(out, "-- The Rust-branded SourceNodeKey/HirParameterId/HirOccurrenceId values were authenticated before projection.").unwrap();
    writeln!(out, "-- These Nat ordinals and byte ranges do not establish a Rust-to-Lean Site/Name allocation law.").unwrap();
    writeln!(out, "end YulangClosure.OriginalAuthenticInlineExtractionTrace").unwrap();
    out
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let parsed = parse(INPUT);
    let hir = lower(&parsed)?;
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).expect("fixture ShadowArtifact");
    let binding = hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "value" => Some(binding),
        _ => None,
    }).expect("fixture binding");
    let root = SourceRootId::Definition(binding.definition_root().clone());
    assert!(hir.owns_source_root(&root));
    let definition_key = hir.definition_source_key(binding.definition_root())?
        .expect("definition root has an exact parsed source key");
    assert!(parsed.owns_source_key(definition_key));
    assert!(artifact.parsed().owns_source_key(definition_key));
    let definition_position = artifact.source_position(definition_key).expect("definition key belongs to ShadowArtifact");
    assert_eq!(artifact.position(&definition_position).expect("definition position").range(), binding.range());
    let source = hir.local_source_for(&root)?.expect("supported LocalSource carrier");
    authenticate_exprs(&parsed, &artifact, &hir, &root, source);

    let outer = source.expressions().iter().find(|expr| {
        matches!(&expr.form, LocalSourceForm::Lambda { parameter, .. }
            if parameter.spelling.as_ref() == "x" && matches!(parameter.scope, yu_hir::LocalSourceScope::Definition(_)))
    }).expect("outer inline x Lambda");
    let LocalSourceForm::Lambda { parameter: outer_parameter, body: outer_body } = &outer.form else { unreachable!() };
    let outer_origin = inline_origin(&artifact, &hir, &outer_parameter.id);
    assert!(parsed.owns_source_key(&outer_parameter.source));
    assert_eq!(range_of(&artifact, &outer_parameter.source), outer.range);

    let mut found = None;
    for candidate in source.expressions() {
        let LocalSourceForm::Apply { callee, argument: argument_index, .. } = &candidate.form else { continue; };
        let callee_index = ungroup(source, callee);
        let callee_expr = expression(source, callee_index);
        let LocalSourceForm::Lambda { parameter: inner_parameter, body: inner_body_index } = &callee_expr.form else { continue; };
        if inner_parameter.spelling.as_ref() != "x" { continue; }
        let argument = expression(source, argument_index);
        if !matches!(&argument.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
            if spelling.as_ref() == "x" && id == &outer_parameter.id) { continue; }
        let inner_body = expression(source, inner_body_index);
        if !matches!(&inner_body.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
            if spelling.as_ref() == "x" && id == &inner_parameter.id) { continue; }
        found = Some((candidate, callee, callee_index, inner_body_index, argument_index,
            callee_expr, inner_parameter, inner_body, argument));
        break;
    }
    let (apply, actual_callee_index, inner_lambda_index, inner_body_index, argument_index,
        inner, inner_parameter, inner_body, argument) = found.expect("inner inline x is Apply callee; actual argument is outer x");
    let inner_origin = inline_origin(&artifact, &hir, &inner_parameter.id);
    assert_eq!(range_of(&artifact, &inner_parameter.source), inner.range);
    assert!(inner_parameter.range.start >= inner.range.start && inner_parameter.range.end <= inner.range.end);
    assert!(inner_body.range.start >= inner.range.start && inner_body.range.end <= inner.range.end);
    assert!(argument.range.start >= apply.range.start && argument.range.end <= apply.range.end);
    assert!(matches!(&expression(source, outer_body).form, LocalSourceForm::Sequence { .. } | LocalSourceForm::StatementBlock { .. }));

    let outer_body_expr = expression(source, outer_body);
    let apply_sibling = source.expressions().iter().filter(|parent| std::ptr::eq(*parent, outer_body_expr)).find_map(|parent| {
        let child_indices = children(&parent.form);
        let apply_slot = child_indices.iter().position(|index| std::ptr::eq(expression(source, index), apply))?;
        child_indices.iter().enumerate().skip(apply_slot + 1).find_map(|(slot, index)| {
            let expr = expression(source, index);
            (matches!(&expr.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
                if spelling.as_ref() == "x" && id == &outer_parameter.id)
                && expr.range.start > apply.range.end
                && expr.range.start >= expression(source, outer_body).range.start
                && expr.range.end <= expression(source, outer_body).range.end)
                .then_some((expr, index.clone(), child_indices[apply_slot].clone(), slot))
        })
    }).expect("later direct sibling x resolves again to the outer parameter");
    let (sibling, sibling_index, apply_child_index, _sibling_slot) = apply_sibling;

    // Equal bytes do not authenticate a different parse or HIR allocation.
    let foreign_parse = parse(INPUT);
    assert_eq!(foreign_parse.source(), parsed.source());
    let foreign_hir = lower(&foreign_parse)?;
    let foreign_artifact = ShadowArtifact::from_parsed(foreign_parse.clone()).expect("equal-text foreign artifact");
    assert_eq!(
        foreign_artifact.parameter_source_origin(&hir, &inner_parameter.id),
        Err(SourceIdentityError::ForeignParse),
        "equal text from a distinct parse must be rejected",
    );
    assert_eq!(
        artifact.parameter_source_origin(&foreign_hir, &inner_parameter.id),
        Err(SourceIdentityError::ForeignHirArtifact),
        "equal text from a distinct HIR must be rejected",
    );

    let generated = emit(
        &parsed, &artifact, source, outer, outer_parameter, apply, inner, inner_parameter,
        outer_body, &apply_child_index, actual_callee_index, inner_lambda_index,
        inner_body_index, argument_index, &sibling_index, inner_body, argument, sibling,
        &outer_origin, &inner_origin,
    );
    std::fs::write(OUTPUT, generated)?;
    println!("source_bytes={} output={} source_root={:?}", INPUT.len(), OUTPUT, source.source_root());
    println!("outer_parameter={:?} inner_parameter={:?}", outer_parameter.id, inner_parameter.id);
    println!("outer_key={:?} inner_key={:?} apply_key={:?} body_key={:?} argument_key={:?} sibling_key={:?}",
        outer.source, inner.source, apply.source, inner_body.source, argument.source, sibling.source);
    println!("occurrences=outer:{} apply:{} inner:{} body:{} argument:{} sibling:{}",
        outer.occurrence.ordinal(), apply.occurrence.ordinal(), inner.occurrence.ordinal(),
        inner_body.occurrence.ordinal(), argument.occurrence.ordinal(), sibling.occurrence.ordinal());
    println!("foreign_equal_text_parse=REJECTED(ForeignParse) foreign_equal_text_hir=REJECTED(ForeignHirArtifact)");
    println!("local_source_body={} outer_body={} actual_apply={} inner_body={} argument={} later_sibling={}",
        source.body().ordinal(), outer_body.ordinal(), apply.range.start, inner_body.range.start,
        argument.range.start, sibling.range.start);
    Ok(())
}

