use std::{fmt::Write as _, ops::Range, sync::Arc};

use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, LocalSource, LocalSourceExpr,
    LocalSourceForm, LocalSourceIndex, LocalSourceParameter, LocalSourceResolution,
    LocalSourceScope, LocalSourceStatement, ModuleIdentity, SemanticImports, SourceRootId,
    shadow::{ParameterSourceOrigin, ShadowArtifact, SourceIdentityError, lower_module_with_local_source},
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

const INPUT: &str = r"my value = \x -> { (\x -> x) x; x }";
const MODULE: &str = "inline-authentic-extraction";
const FILE: &str = "inline_authentic_extraction.yu";
const OUTPUT: &str = "notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean";

#[derive(Clone)]
struct Locator { ordinal: usize, range: Range<usize> }
#[derive(Clone)]
struct OwnerExpr { label: &'static str, index: LocalSourceIndex, locator: Locator, occurrence: u32 }
#[derive(Clone)]
struct BodyEvidence { order: usize, expr: OwnerExpr, final_expr: bool }
#[derive(Clone)]
struct NameEvidence { key: &'static str, occurrence: &'static str, expr: OwnerExpr, parameter: u32 }

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()))
}
fn lower(parsed: &ParsedFile) -> Result<HirModule, HirAvailabilityError> {
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(MODULE, FILE))),
        parsed,
        SemanticImports::empty(),
    )
}
fn availability<T>(label: &'static str, result: Result<T, HirAvailabilityError>) -> Result<T, Box<dyn std::error::Error>> {
    result.map_err(|error| format!("{label}: {error:?}").into())
}
fn position_ordinal(artifact: &ShadowArtifact, position: &yu_hir::shadow::Position) -> usize {
    artifact.positions().iter().position(|candidate| std::ptr::eq(candidate, position))
        .expect("position belongs to exact ShadowArtifact")
}
fn locator_for_key(parsed: &ParsedFile, artifact: &ShadowArtifact, key: &yu_syntax::SourceNodeKey) -> Locator {
    assert!(parsed.owns_source_key(key), "source key belongs to selected parse");
    assert!(artifact.parsed().owns_source_key(key), "ShadowArtifact shares selected parse");
    let position = artifact.source_position(key).expect("same-parse source key has source position");
    let value = artifact.position(&position).expect("position belongs to artifact");
    assert!(value.is_node(), "expression and definition keys are CST nodes");
    Locator { ordinal: position_ordinal(artifact, value), range: value.range().clone() }
}
fn expression<'a>(source: &'a LocalSource, root: &SourceRootId, index: &LocalSourceIndex) -> &'a LocalSourceExpr {
    assert_eq!(index.source_root(), root, "index is branded by selected root");
    source.expression(index).expect("index belongs to selected LocalSource")
}
fn owner_expr(
    parsed: &ParsedFile, artifact: &ShadowArtifact, hir: &HirModule,
    source: &LocalSource, root: &SourceRootId, label: &'static str, index: &LocalSourceIndex,
) -> OwnerExpr {
    let expr = expression(source, root, index);
    assert!(hir.owns_occurrence(&expr.occurrence), "occurrence is selected-HIR owned");
    assert_eq!(hir.occurrence_source_key(&expr.occurrence).expect("occurrence owner"), Some(&expr.source));
    let locator = locator_for_key(parsed, artifact, &expr.source);
    assert_eq!(locator.range, expr.range, "CST range is exact LocalSource range");
    OwnerExpr { label, index: index.clone(), locator, occurrence: expr.occurrence.ordinal() }
}
fn lean_range(range: &Range<usize>) -> String { format!("({}, {})", range.start, range.end) }
fn lean_string(value: &str) -> String { format!("{value:?}") }
fn key_for_name(parameter: &LocalSourceParameter, outer: &LocalSourceParameter, inner: &LocalSourceParameter) -> &'static str {
    if parameter.id == outer.id { "outer" } else if parameter.id == inner.id { "inner" } else { panic!("resolved parameter is outside selected fixture binders") }
}
fn write_physical(out: &mut String, key: &str, owner: &OwnerExpr) {
    writeln!(out, "  {{ key := .{key}, sourceLocator := {{ positionOrdinal := {}, byteRange := {} }}, localSourceIndex := some {}, occurrenceOrdinal := some {} }},",
        owner.locator.ordinal, lean_range(&owner.locator.range), owner.index.ordinal(), owner.occurrence).unwrap();
}
fn write_physical_definition(out: &mut String, locator: &Locator) {
    writeln!(out, "  {{ key := .definition, sourceLocator := {{ positionOrdinal := {}, byteRange := {} }}, localSourceIndex := none, occurrenceOrdinal := none }},",
        locator.ordinal, lean_range(&locator.range)).unwrap();
}
fn write_formal(out: &mut String, key: &str, lambda: &str, parameter: &LocalSourceParameter, binder: &Locator) {
    writeln!(out, "  {{ key := .{key}, lambda := .{lambda}, parameterOrdinal := {}, binderToken := {{ positionOrdinal := {}, byteRange := {} }}, spelling := {} }},",
        parameter.id.ordinal(), binder.ordinal, lean_range(&binder.range), lean_string(parameter.spelling.as_ref())).unwrap();
}
fn write_resolution(out: &mut String, occurrence: &str, name: &str, parameter: u32) {
    writeln!(out, "  {{ occurrence := .{occurrence}, name := .{name}, parameterOrdinal := {parameter} }},").unwrap();
}

fn emit(
    parsed: &ParsedFile,
    definition: &Locator,
    owners: &[(&str, &OwnerExpr)],
    outer_parameter: &LocalSourceParameter,
    outer_binder: &Locator,
    inner_parameter: &LocalSourceParameter,
    inner_binder: &Locator,
    names: &[NameEvidence],
    group: &OwnerExpr,
    projected: &OwnerExpr,
    body: &[BodyEvidence],
    module_root_ordinal: u32,
) -> String {
    let mut out = String::new();
    writeln!(out, "import YulangClosure.OriginalSourceOwnerReification").unwrap();
    writeln!(out, "\nnamespace YulangClosure.OriginalSourceOwnerReificationTrace\n").unwrap();
    writeln!(out, "open OriginalSourceOwnerReification\n").unwrap();
    writeln!(out, "/-- Generated by the isolated authenticated runner. Row indices are constructed from the typed owner table; they are not claimed to be original allocations. The incoming OriginalSource Context is not available in this runner. -/").unwrap();
    writeln!(out, "def originTable : OriginTable := {{").unwrap();
    writeln!(out, "  inputUtf8 := {}, sourceModule := {}, sourceFile := {},",
        lean_string(parsed.source()), lean_string(MODULE), lean_string(FILE)).unwrap();
    writeln!(out, "  physical := [").unwrap();
    write_physical_definition(&mut out, definition);
    for (key, owner) in owners { write_physical(&mut out, key, owner); }
    writeln!(out, "  ],").unwrap();
    writeln!(out, "  formals := [").unwrap();
    write_formal(&mut out, "outer", "outerLambda", outer_parameter, outer_binder);
    write_formal(&mut out, "inner", "innerLambda", inner_parameter, inner_binder);
    writeln!(out, "  ], wilds := [{{ key := .outer, formal := .outer }}, {{ key := .inner, formal := .inner }}],").unwrap();
    writeln!(out, "  names := [").unwrap();
    writeln!(out, "    {{ key := .declaration, owner := .declaration .value, spelling := \"value\" }},").unwrap();
    writeln!(out, "    {{ key := .outer, owner := .parameter .outer, spelling := \"{}\" }},", outer_parameter.spelling).unwrap();
    writeln!(out, "    {{ key := .inner, owner := .parameter .inner, spelling := \"{}\" }},", inner_parameter.spelling).unwrap();
    writeln!(out, "  ], declarations := [{{ key := .value, sourceNode := .definition, definitionRootOrdinal := {module_root_ordinal} }}],").unwrap();
    writeln!(out, "  statements := [{{ key := .application, block := .outerBody, sourceOrder := 0, expression := .application }}],").unwrap();
    writeln!(out, "  resolutions := [").unwrap();
    for evidence in names {
        write_resolution(&mut out, evidence.occurrence, evidence.key, evidence.parameter);
    }
    writeln!(out, "  ], groups := [{{ group := .rawCallee, projected := .innerLambda }}],").unwrap();
    writeln!(out, "  body := [").unwrap();
    for entry in body {
        let kind = if entry.final_expr { ".finalExpression" } else { ".statementExpression" };
        let key = if entry.final_expr { "sibling" } else { "application" };
        writeln!(out, "    {{ sourceOrder := {}, occurrence := .{key}, kind := {kind} }},", entry.order).unwrap();
    }
    writeln!(out, "  ], callerContext := none }}\n").unwrap();
    writeln!(out, "def rowIndexedCoordinates : Option OriginalCoordinates := constructCoordinates originTable").unwrap();
    writeln!(out, "def constructedCoordinates : OriginalCoordinates := rowIndexedCoordinates.get (by native_decide)\n").unwrap();
    writeln!(out, "/-- A checked finite index representation derived from typed owner rows. This says nothing about Rust allocating these original Nat labels. -/").unwrap();
    writeln!(out, "theorem constructedCoordinateLaws : CoordinateLaws originTable constructedCoordinates := by").unwrap();
    writeln!(out, "  apply coordinate_laws_of_rows originTable constructedCoordinates <;> intro key <;> cases key <;> native_decide\n").unwrap();
    writeln!(out, "def locatedInner : LocatedExpression := .lambda .innerLambda .inner .inner .inner (.name .innerBody .inner)").unwrap();
    writeln!(out, "def locatedArgument : LocatedExpression := .name .argument .outer").unwrap();
    writeln!(out, "def locatedApplication : LocatedExpression := .app .application (.group .rawCallee .innerLambda locatedInner) locatedArgument").unwrap();
    writeln!(out, "def locatedBody : LocatedExpression := .block .outerBody .application locatedApplication (.name .sibling .outer)").unwrap();
    writeln!(out, "def locatedFixture : LocatedExpression := .lambda .outerLambda .outer .outer .outer locatedBody\n").unwrap();
    writeln!(out, "def rawGroupOwner : PhysicalKey := .{}", "rawCallee").unwrap();
    writeln!(out, "def projectedLambdaOwner : PhysicalKey := .{}", "innerLambda").unwrap();
    writeln!(out, "theorem rawGroupProjectionRetained : originTable.groups = [{{ group := rawGroupOwner, projected := projectedLambdaOwner }}] := by native_decide").unwrap();
    writeln!(out, "def orderedBodyOwnerRows : List BodyRow := originTable.body").unwrap();
    writeln!(out, "theorem bodyOwnerOrderExact : orderedBodyOwnerRows = [⟨0, .application, .statementExpression⟩, ⟨1, .sibling, .finalExpression⟩] := by native_decide\n").unwrap();
    writeln!(out, "def callerContextStatus : String := \"OPEN: runner lowers with SemanticImports.empty and receives no source-module Context/scope owner\"").unwrap();
    writeln!(out, "def declarationCoordinateStatus : String := \"table carries the authentic HIR DefinitionRoot/DefId ordinal; OriginalSource.Declaration allocation is not exposed by Rust\"").unwrap();
    writeln!(out, "def eventTelescopeStatus : String := \"OPEN: no caller Context or full-root sourceOwners telescope is allocated by this runner\"").unwrap();
    writeln!(out, "def sourceOwnersStatus : String := \"physical CST key/range + LocalSource index + HIR occurrence joins checked by executed runner; table values alone are not Lean-authenticated pointers\"").unwrap();
    writeln!(out, "def fixtureInputByteLength : Nat := {}", parsed.source().len()).unwrap();
    writeln!(out, "def sameSpellingParametersDistinct : Bool := true").unwrap();
    writeln!(out, "def rawCalleeIsGroupAndNotProjectedLambda : Bool := {}", group.index != projected.index).unwrap();
    writeln!(out, "end YulangClosure.OriginalSourceOwnerReificationTrace").unwrap();
    out
}

fn binder_locator(
    parsed: &ParsedFile, artifact: &ShadowArtifact, hir: &HirModule,
    parameter: &LocalSourceParameter, expected_root: &SourceRootId,
) -> Result<Locator, Box<dyn std::error::Error>> {
    assert_eq!(parameter.id.source_root(), expected_root);
    let lambda = artifact.source_position(&parameter.source).expect("parameter Lambda SourceNodeKey");
    let origin = artifact.parameter_source_origin(hir, &parameter.id)
        .map_err(|error| format!("parameter origin authentication failed: {error:?}"))?;
    let ParameterSourceOrigin::InlineLambda { lambda: registered, binder } = origin else { panic!("fixture parameter must have registered inline Lambda origin") };
    assert_eq!(registered, lambda, "registered Lambda matches parameter source key");
    let value = artifact.position(&binder).expect("registered binder token");
    assert_eq!(value.kind(), SyntaxKind::Identifier);
    assert!(!value.is_node());
    assert!(parsed.owns_source_key(&parameter.source));
    Ok(Locator { ordinal: position_ordinal(artifact, value), range: value.range().clone() })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let parsed = parse(INPUT);
    let hir = availability("lower selected HIR", lower(&parsed))?;
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).expect("selected parse artifact");
    let binding = hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "value" => Some(binding), _ => None,
    }).expect("authentic direct declaration");
    let root = SourceRootId::Definition(binding.definition_root().clone());
    assert!(hir.owns_source_root(&root));
    let definition_key = availability("definition source key", hir.definition_source_key(binding.definition_root()))?
        .expect("HIR root retains parse-owned Definition source key");
    let definition = locator_for_key(&parsed, &artifact, definition_key);
    assert_eq!(definition.range, *binding.range());
    let source = availability("LocalSource owner", hir.local_source_for(&root))?.expect("supported source carrier");
    assert_eq!(source.source_root(), &root);
    let outer_index = source.body().clone();
    let outer = expression(source, &root, &outer_index);
    let LocalSourceForm::Lambda { parameter: outer_parameter, body: body_index } = &outer.form else { panic!("root value is not Lambda") };
    assert!(matches!(&outer_parameter.scope, LocalSourceScope::Definition(id) if id == binding.definition_root()));
    let outer_binder = binder_locator(&parsed, &artifact, &hir, outer_parameter, &root)?;
    assert_eq!(outer_binder.range, outer_parameter.range);
    let body_expr = expression(source, &root, body_index);
    let LocalSourceForm::StatementBlock { statements, final_expression } = &body_expr.form else { panic!("fixture body is not a statement block") };
    assert_eq!(statements.len(), 1);
    let LocalSourceStatement::Expression(apply_index) = &statements[0] else { panic!("first statement is not expression") };
    let apply = expression(source, &root, apply_index);
    let LocalSourceForm::Apply { callee: raw_callee_index, argument: argument_index, .. } = &apply.form else { panic!("statement is not Apply") };
    let raw_callee = expression(source, &root, raw_callee_index);
    let LocalSourceForm::Group { inner: projected_index } = &raw_callee.form else { panic!("raw Apply callee lost Group") };
    let projected = expression(source, &root, projected_index);
    let LocalSourceForm::Lambda { parameter: inner_parameter, body: inner_body_index } = &projected.form else { panic!("Group child is not nested Lambda") };
    assert_ne!(outer_parameter.id, inner_parameter.id);
    assert_eq!(outer_parameter.spelling, inner_parameter.spelling);
    assert_eq!(inner_parameter.source, projected.source);
    assert!(matches!(&inner_parameter.scope, LocalSourceScope::Expression(_)));
    let inner_binder = binder_locator(&parsed, &artifact, &hir, inner_parameter, &root)?;
    assert_eq!(inner_binder.range, inner_parameter.range);
    let inner_body = expression(source, &root, inner_body_index);
    let argument = expression(source, &root, argument_index);
    let LocalSourceForm::Name { spelling: arg_name, resolution: LocalSourceResolution::Parameter(arg_parameter) } = &argument.form else { panic!("Apply argument does not resolve to parameter") };
    let LocalSourceForm::Name { spelling: body_name, resolution: LocalSourceResolution::Parameter(body_parameter) } = &inner_body.form else { panic!("inner body does not resolve to parameter") };
    assert_eq!(arg_parameter, &outer_parameter.id);
    assert_eq!(body_parameter, &inner_parameter.id);
    assert_eq!(arg_name, &outer_parameter.spelling);
    assert_eq!(body_name, &inner_parameter.spelling);
    let sibling = expression(source, &root, final_expression);
    let LocalSourceForm::Name { spelling: sibling_name, resolution: LocalSourceResolution::Parameter(sibling_parameter) } = &sibling.form else { panic!("final expression is not resolved Name") };
    assert_eq!(sibling_parameter, &outer_parameter.id);
    assert_eq!(sibling_name, &outer_parameter.spelling);
    let owner = |label, index| owner_expr(&parsed, &artifact, &hir, source, &root, label, index);
    let outer_owner = owner("outerLambda", &outer_index);
    let body_owner = owner("outerBody", body_index);
    let app_owner = owner("application", apply_index);
    let group_owner = owner("rawCallee", raw_callee_index);
    let argument_owner = owner("argument", argument_index);
    let inner_owner = owner("innerLambda", projected_index);
    let inner_body_owner = owner("innerBody", inner_body_index);
    let sibling_owner = owner("sibling", final_expression);
    assert_ne!(group_owner.index, inner_owner.index);
    let app_pos = artifact.position(&artifact.source_position(&apply.source).expect("Apply source key")).expect("Apply position");
    let apply_source_form = match &apply.form { LocalSourceForm::Apply { source_form, .. } => format!("{source_form:?}"), _ => unreachable!() };
    let body_entries = vec![
        BodyEvidence { order: 0, expr: app_owner.clone(), final_expr: false },
        BodyEvidence { order: 1, expr: sibling_owner.clone(), final_expr: true },
    ];
    let names = vec![
        NameEvidence { key: "outer", occurrence: "argument", expr: argument_owner.clone(), parameter: outer_parameter.id.ordinal() },
        NameEvidence { key: "inner", occurrence: "innerBody", expr: inner_body_owner.clone(), parameter: inner_parameter.id.ordinal() },
        NameEvidence { key: "outer", occurrence: "sibling", expr: sibling_owner.clone(), parameter: outer_parameter.id.ordinal() },
    ];
    assert!(names.iter().all(|name| name.expr.occurrence > 0));
    assert_eq!(key_for_name(outer_parameter, outer_parameter, inner_parameter), "outer");
    assert_eq!(key_for_name(inner_parameter, outer_parameter, inner_parameter), "inner");
    let owners = [
        ("outerLambda", &outer_owner), ("outerBody", &body_owner), ("application", &app_owner),
        ("rawCallee", &group_owner), ("argument", &argument_owner), ("innerLambda", &inner_owner),
        ("innerBody", &inner_body_owner), ("sibling", &sibling_owner),
    ];
    let generated = emit(&parsed, &definition, &owners, outer_parameter, &outer_binder,
        inner_parameter, &inner_binder, &names, &group_owner, &inner_owner, &body_entries,
        binding.id().same_name_ordinal());
    std::fs::write(OUTPUT, generated)?;
    let foreign_parse = parse(INPUT);
    assert!(!parsed.owns_source_key(&foreign_parse.source_root().key()), "same bytes in another parse must not authenticate");
    assert!(matches!(artifact.source_position(&foreign_parse.source_root().key()), Err(SourceIdentityError::ForeignParse)));
    println!("source={} module={MODULE} declaration={} definition_root_ordinal={} physical_rows={} formal_rows=2 body_rows={} resolutions={} imports=empty callerContext=OPEN", INPUT, binding.name().spelling(), binding.id().same_name_ordinal(), owners.len() + 1, body_entries.len(), names.len());
    println!("apply_source_form={apply_source_form} apply_position={:?} raw_callee={} projected_lambda={} group_projection=authenticated outer_parameter={} inner_parameter={} foreign_parse=REJECTED output={OUTPUT}", app_pos.range(), group_owner.index.ordinal(), inner_owner.index.ordinal(), outer_parameter.id.ordinal(), inner_parameter.id.ordinal());
    Ok(())
}
