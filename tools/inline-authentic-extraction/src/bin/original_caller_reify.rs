use std::{fmt::Write as _, ops::Range, path::PathBuf, sync::Arc};

use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirItem, HirModule, LocalSource, LocalSourceExpr,
    LocalSourceForm, LocalSourceIndex, LocalSourceParameter, LocalSourceResolution,
    LocalSourceScope, LocalSourceStatement, ModuleIdentity, SemanticImports, SourceRootId,
    SourceExportIndex, SourceExportId, SourceImportBinding, index_source_exports,
    shadow::{ParameterSourceOrigin, ShadowArtifact, SourceIdentityError, lower_module_with_local_source},
};
use yu_syntax::{ParsedFile, SourceText, SourceNodeKey, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

const CONSUMER_INPUT: &str = "use std::core::id as identity\npub first = identity 1\npub second = id 2\nmy value = \\x -> { (\\x -> x) x; x }";
const CONSUMER_MODULE: &str = "consumer";
const CONSUMER_FILE: &str = "consumer.yu";
const PROVIDER_FILES: [&str; 3] = ["lib/std.yu", "lib/std/core.yu", "lib/std/prelude.yu"];
const PROVIDER_MODULES: [&str; 3] = ["std", "std::core", "std::prelude"];
const PROVIDER_INPUTS: [&str; 3] = ["pub mod core;\npub mod prelude;", "pub id x = x", "pub use std::core::*"];
const OUTPUT: &str = "notes/theory/lean/YulangClosure/OriginalSourceCallerReificationTrace.lean";

#[derive(Clone)]
struct Locator { ordinal: usize, range: Range<usize> }
#[derive(Clone)]
struct OwnerExpr { label: &'static str, index: LocalSourceIndex, locator: Locator, occurrence: u32 }
#[derive(Clone)]
struct BodyEvidence { order: usize, expr: OwnerExpr, final_expr: bool }
#[derive(Clone)]
struct NameEvidence { key: &'static str, occurrence: &'static str, expr: OwnerExpr, parameter: u32 }
struct ModuleOwner {
    ordinal: usize, name: &'static str, file: &'static str, parsed: ParsedFile,
    identity: ModuleIdentity, artifact: ShadowArtifact, index: SourceExportIndex,
}
#[derive(Clone)]
struct LeafEvidence {
    owner_module: usize, declaration: Locator, leaf: Locator, path: Vec<String>,
    selected_name: Option<String>, alias: Option<String>, is_glob: bool,
    is_public: bool, recovered: bool, declaration_key: SourceNodeKey,
    leaf_key: SourceNodeKey,
}
struct ExportEvidence { ordinal: usize, provider_module: usize, module_name: String,
    name: String, declaration: Locator, kind: String, is_public: bool,
    recovered: bool, identity: SourceExportId }
struct LookupEvidence { exposed_name: String, export_ordinal: usize, route: Vec<LeafEvidence> }
struct ImportedUseEvidence { root_source_order: usize, source: Locator,
    local_source_index: u32, occurrence: u32, exposed_name: String,
    export_ordinal: usize }
struct RootEvidence { source_order: usize, node: Locator, syntax_kind: String,
    hir_kind: String, declaration_name: Option<String>, definition_ordinal: Option<u32>,
    binding: Option<yu_hir::HirBinding> }

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()))
}
fn identity(module: &str, file: &str) -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new(module, file)))
}
fn lower(parsed: &ParsedFile, identity: ModuleIdentity, imports: SemanticImports) -> Result<HirModule, HirAvailabilityError> {
    lower_module_with_local_source(identity, parsed, imports)
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
fn locator_for_module_root(module: &ModuleOwner) -> Locator {
    let root = module.parsed.source_root().key();
    locator_for_key(&module.parsed, &module.artifact, &root)
}
fn owner_modules() -> Result<Vec<ModuleOwner>, Box<dyn std::error::Error>> {
    let mut modules = Vec::new();
    let consumer = parse(CONSUMER_INPUT);
    let consumer_identity = identity(CONSUMER_MODULE, CONSUMER_FILE);
    let consumer_artifact = ShadowArtifact::from_parsed(consumer.clone()).expect("consumer parse artifact");
    let consumer_index = availability("index consumer source exports", index_source_exports(consumer_identity.clone(), &consumer))?;
    modules.push(ModuleOwner { ordinal: 0, name: CONSUMER_MODULE, file: CONSUMER_FILE,
        parsed: consumer, identity: consumer_identity, artifact: consumer_artifact, index: consumer_index });
    for i in 0..PROVIDER_FILES.len() {
        let parsed = parse(PROVIDER_INPUTS[i]);
        let identity = identity(PROVIDER_MODULES[i], PROVIDER_FILES[i]);
        let artifact = ShadowArtifact::from_parsed(parsed.clone()).expect("provider parse artifact");
        let index = availability("index provider source exports", index_source_exports(identity.clone(), &parsed))?;
        modules.push(ModuleOwner { ordinal: i + 1, name: PROVIDER_MODULES[i], file: PROVIDER_FILES[i],
            parsed, identity, artifact, index });
    }
    Ok(modules)
}
fn flatten_owned_imports(modules: &[ModuleOwner]) -> Result<Vec<LeafEvidence>, Box<dyn std::error::Error>> {
    let mut rows = Vec::new();
    for module in modules {
        for declaration in &module.index.uses {
            if declaration.recovered { return Err(format!("recovered import declaration in {}", module.name).into()); }
            let declaration_locator = locator_for_key(&module.parsed, &module.artifact, &declaration.source);
            for tree in &declaration.tree {
                assert_eq!(tree.kind, SyntaxKind::UseTree, "fixture use tree shape");
                let path_node = tree.children.iter().find(|node| node.kind == SyntaxKind::UsePath)
                    .ok_or("fixture import path missing")?;
                let path_text = path_node.text.trim();
                let path = path_text.split("::").map(str::to_owned).collect::<Vec<_>>();
                assert!(!path.is_empty() && path.iter().all(|segment| !segment.is_empty()), "valid source import path");
                let glob = tree.children.iter().find(|node| node.kind == SyntaxKind::UseGlob);
                let alias_node = tree.children.iter().find(|node| node.kind == SyntaxKind::UseAlias);
                let alias = alias_node.map(|node| {
                    node.text.trim().strip_prefix("as ").expect("exact alias syntax").trim().to_owned()
                });
                if tree.children.iter().any(|node| matches!(node.kind, SyntaxKind::UseGroup | SyntaxKind::UseExclusionGroup | SyntaxKind::UseQualifiers)) {
                    return Err(format!("unsupported grouped/qualified fixture import in {}", module.name).into());
                }
                let (leaf_key, selected_name, is_glob) = if let Some(glob) = glob {
                    (glob.source.clone(), None, true)
                } else {
                    (tree.source.clone(), path.last().cloned(), false)
                };
                let leaf = locator_for_key(&module.parsed, &module.artifact, &leaf_key);
                rows.push(LeafEvidence { owner_module: module.ordinal, declaration: declaration_locator.clone(),
                    leaf, path: path.clone(), selected_name, alias, is_glob, is_public: declaration.public,
                    recovered: declaration.recovered || tree.recovered || path_node.recovered,
                    declaration_key: declaration.source.clone(), leaf_key });
            }
        }
    }
    Ok(rows)
}
fn root_inventory(module: &ModuleOwner, hir: &HirModule) -> Result<(Vec<RootEvidence>, usize, yu_hir::HirBinding), Box<dyn std::error::Error>> {
    assert_eq!(hir.identity(), &module.identity, "consumer HIR module identity");
    let syntax_roots = module.parsed.source_root().children().collect::<Vec<_>>();
    assert_eq!(syntax_roots.len(), hir.items().len(), "complete direct CST/HIR root inventory cardinality");
    let mut rows = Vec::new();
    let mut selected = None;
    for (source_order, (node, item)) in syntax_roots.iter().zip(hir.items()).enumerate() {
        let key = node.key();
        assert!(module.parsed.owns_source_key(&key), "root is consumer-parse owned");
        let range = node.syntax().text_range();
        let bytes = (u32::from(range.start()) as usize)..(u32::from(range.end()) as usize);
        let locator = locator_for_key(&module.parsed, &module.artifact, &key);
        assert_eq!(locator.range, bytes, "position range is exact direct root range");
        let syntax_kind = format!("{:?}", node.syntax().kind());
        let (hir_kind, declaration_name, definition_ordinal, binding) = match item {
            HirItem::Import { range } => {
                assert_eq!(range, &bytes, "HIR import retains exact root range");
                assert_eq!(node.syntax().kind(), SyntaxKind::UseDeclaration);
                ("Import".to_owned(), None, None, None)
            }
            HirItem::Binding(binding) => {
                let root = binding.definition_root();
                assert!(hir.owns_definition_root(root), "direct binding root belongs to selected HIR");
                let source = availability("direct binding source key", hir.definition_source_key(root))?.expect("binding source key retained");
                assert_eq!(source, &key, "definition source root equals direct parse root");
                assert_eq!(binding.range(), &bytes, "binding byte range agrees with direct root");
                let name = binding.name().spelling().to_owned();
                let ordinal = binding.id().same_name_ordinal();
                if name == "value" { selected = Some((source_order, binding.clone())); }
                ("Binding".to_owned(), Some(name), Some(ordinal), Some(binding.clone()))
            }
            HirItem::Expression(_) => return Err(format!("unexpected expression root at order {source_order}").into()),
            HirItem::Error { .. } => return Err(format!("HIR error root at order {source_order}").into()),
        };
        rows.push(RootEvidence { source_order, node: locator, syntax_kind, hir_kind,
            declaration_name, definition_ordinal, binding });
    }
    let (selected_order, selected_binding) = selected.ok_or("selected `value` declaration absent")?;
    Ok((rows, selected_order, selected_binding))
}
fn export_rows(modules: &[ModuleOwner]) -> Result<Vec<ExportEvidence>, Box<dyn std::error::Error>> {
    let mut rows = Vec::new();
    for module in modules.iter().skip(1) {
        for declaration in &module.index.declarations {
            let Some(name) = declaration.name.as_deref() else { continue; };
            assert!(module.parsed.owns_source_key(&declaration.source), "provider export belongs to indexed provider parse");
            let locator = locator_for_key(&module.parsed, &module.artifact, &declaration.source);
            assert_eq!(locator.range, declaration.range, "export source/range join");
            let ordinal = rows.len();
            rows.push(ExportEvidence {
                ordinal, provider_module: module.ordinal, module_name: declaration.namespace.to_string(),
                name: name.to_owned(), declaration: locator,
                kind: format!("{:?}", declaration.kind), is_public: declaration.public,
                recovered: declaration.recovered,
                identity: SourceExportId { module: declaration.namespace.clone(), name: name.into(),
                    source: declaration.source.clone(), range: declaration.range.clone(), kind: declaration.kind },
            });
        }
    }
    Ok(rows)
}
fn resolved_import<'a>(
    module: &'a HirModule, exposed: &str,
) -> Result<&'a yu_hir::SourceExportResolution, Box<dyn std::error::Error>> {
    let environment = module.source_imports().ok_or("lowered HIR omitted source import environment")?;
    match environment.resolve(exposed) {
        Some(SourceImportBinding::Resolved(resolution)) => Ok(resolution),
        other => Err(format!("source import {exposed:?} is not uniquely resolved: {other:?}").into()),
    }
}
fn module_ordinal(modules: &[ModuleOwner], module_name: &str) -> Result<usize, Box<dyn std::error::Error>> {
    modules.iter().find(|module| module.name == module_name).map(|module| module.ordinal)
        .ok_or_else(|| format!("provider module {module_name:?} is absent from exact corpus").into())
}
fn route_rows(
    resolution: &yu_hir::SourceExportResolution, imports: &[LeafEvidence], modules: &[ModuleOwner],
) -> Result<Vec<LeafEvidence>, Box<dyn std::error::Error>> {
    let mut rows = Vec::new();
    for leaf in &resolution.route {
        let owner = modules.iter().find(|module| module.parsed.owns_source_key(&leaf.leaf)
            && module.parsed.owns_source_key(&leaf.declaration))
            .map(|module| module.ordinal).ok_or("resolver route leaf has no source-owning provider module")?;
        let row = imports.iter().find(|row| row.owner_module == owner
            && row.declaration_key == leaf.declaration && row.leaf_key == leaf.leaf)
            .ok_or("resolver route leaf has no matching indexed raw import leaf")?;
        assert_eq!(row.path, leaf.path.iter().map(|segment| segment.to_string()).collect::<Vec<_>>());
        assert_eq!(row.alias.as_deref(), leaf.alias.as_deref());
        assert_eq!(row.is_public, leaf.public);
        assert_eq!(row.recovered, leaf.recovered);
        rows.push(row.clone());
    }
    Ok(rows)
}
fn lookup_evidence(
    hir: &HirModule, names: &[&str], exports: &[ExportEvidence], imports: &[LeafEvidence],
    modules: &[ModuleOwner],
) -> Result<Vec<LookupEvidence>, Box<dyn std::error::Error>> {
    let mut rows = Vec::new();
    for name in names {
        let resolution = resolved_import(hir, name)?;
        let id = resolution.identity();
        let export = exports.iter().find(|row| row.identity == id)
            .ok_or_else(|| format!("resolved provider identity for {name:?} absent from indexed exports"))?;
        assert_eq!(resolution.module.as_ref(), export.module_name);
        assert_eq!(resolution.name.as_ref(), export.name);
        assert!(modules[export.provider_module].parsed.owns_source_key(&id.source), "resolved export source is owned by selected provider parse");
        rows.push(LookupEvidence { exposed_name: (*name).to_owned(), export_ordinal: export.ordinal,
            route: route_rows(resolution, imports, modules)? });
    }
    Ok(rows)
}
fn imported_use_rows(
    module: &ModuleOwner, hir: &HirModule, roots: &[RootEvidence], exports: &[ExportEvidence],
) -> Result<Vec<ImportedUseEvidence>, Box<dyn std::error::Error>> {
    let mut rows = Vec::new();
    for root in roots {
        let Some(binding) = &root.binding else { continue; };
        let owner = SourceRootId::Definition(binding.definition_root().clone());
        assert!(hir.owns_source_root(&owner));
        let source = availability("consumer LocalSource", hir.local_source_for(&owner))?.ok_or("missing consumer LocalSource")?;
        assert_eq!(source.source_root(), &owner);
        for expression in source.expressions() {
            if let LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Imported(id) } = &expression.form {
                assert!(hir.owns_occurrence(&expression.occurrence), "imported Name occurrence belongs to consumer HIR");
                assert_eq!(hir.occurrence_source_key(&expression.occurrence).expect("imported Name source owner"), Some(&expression.source));
                assert!(module.parsed.owns_source_key(&expression.source));
                let locator = locator_for_key(&module.parsed, &module.artifact, &expression.source);
                assert_eq!(locator.range, expression.range);
                let export = exports.iter().find(|row| row.identity == *id)
                    .ok_or_else(|| format!("LocalSource imported identity for {spelling:?} has no export row"))?;
                let lookup = resolved_import(hir, spelling)?;
                assert_eq!(lookup.identity(), *id, "LocalSource imported identity equals resolver lookup");
                rows.push(ImportedUseEvidence { root_source_order: root.source_order, source: locator,
                    local_source_index: source.expressions().iter().position(|candidate| std::ptr::eq(candidate, expression)).expect("expression in exact LocalSource") as u32,
                    occurrence: expression.occurrence.ordinal(), exposed_name: spelling.to_string(), export_ordinal: export.ordinal });
            }
        }
    }
    Ok(rows)
}
fn emit_locator(out: &mut String, locator: &Locator) {
    write!(out, "{{ positionOrdinal := {}, byteRange := {} }}", locator.ordinal, lean_range(&locator.range)).unwrap();
}
fn emit_import_leaf(out: &mut String, row: &LeafEvidence) {
    write!(out, "{{ ownerModule := {}, declarationLocator := ", row.owner_module).unwrap();
    emit_locator(out, &row.declaration);
    write!(out, ", leafLocator := ").unwrap(); emit_locator(out, &row.leaf);
    write!(out, ", path := [{}], selectedName := {}, alias := {}, isGlob := {}, isPublic := {}, recovered := {} }}",
        row.path.iter().map(|part| lean_string(part)).collect::<Vec<_>>().join(", "),
        row.selected_name.as_deref().map(lean_string).map(|s| format!("some {s}")).unwrap_or_else(|| "none".into()),
        row.alias.as_deref().map(lean_string).map(|s| format!("some {s}")).unwrap_or_else(|| "none".into()),
        row.is_glob, row.is_public, row.recovered).unwrap();
}
fn emit_module_row(out: &mut String, module: &ModuleOwner) {
    write!(out, "{{ ordinal := {}, moduleName := {}, sourceFile := {}, inputUtf8 := {}, parseRoot := ",
        module.ordinal, lean_string(module.name), lean_string(module.file), lean_string(module.parsed.source())).unwrap();
    emit_locator(out, &locator_for_module_root(module));
    write!(out, " }}").unwrap();
}
fn emit_caller_table(
    modules: &[ModuleOwner], imports: &[LeafEvidence], exports: &[ExportEvidence],
    lookups: &[LookupEvidence], imported_uses: &[ImportedUseEvidence], roots: &[RootEvidence],
    selected_root_order: usize, selected_value: &str,
) -> String {
    let mut out = String::new();
    writeln!(out, "import YulangClosure.OriginalSourceCallerSchema").unwrap();
    writeln!(out, "\nnamespace YulangClosure.OriginalSourceCallerReificationTrace\n").unwrap();
    writeln!(out, "open OriginalSourceCallerSchema OriginalSourceOwnerReification\n").unwrap();
    writeln!(out, "def callerTable : CallerTable := {{").unwrap();
    write!(out, "  consumer := ").unwrap(); emit_module_row(&mut out, &modules[0]); writeln!(out, ",").unwrap();
    writeln!(out, "  providers := [").unwrap();
    for module in modules.iter().skip(1) { write!(out, "    ").unwrap(); emit_module_row(&mut out, module); writeln!(out, ",").unwrap(); }
    writeln!(out, "  ], imports := [").unwrap();
    for row in imports { write!(out, "    ").unwrap(); emit_import_leaf(&mut out, row); writeln!(out, ",").unwrap(); }
    writeln!(out, "  ], exports := [").unwrap();
    for row in exports {
        write!(out, "    {{ ordinal := {}, providerModule := {}, moduleName := {}, name := {}, declaration := ",
            row.ordinal, row.provider_module, lean_string(&row.module_name), lean_string(&row.name)).unwrap();
        emit_locator(&mut out, &row.declaration);
        writeln!(out, ", kind := {}, isPublic := {}, recovered := {} }},", lean_string(&row.kind), row.is_public, row.recovered).unwrap();
    }
    writeln!(out, "  ], lookups := [").unwrap();
    for row in lookups {
        writeln!(out, "    {{ exposedName := {}, exportOrdinal := {}, publicRoute := [",
            lean_string(&row.exposed_name), row.export_ordinal).unwrap();
        for leaf in &row.route { write!(out, "      ").unwrap(); emit_import_leaf(&mut out, leaf); writeln!(out, ",").unwrap(); }
        writeln!(out, "    ] }},").unwrap();
    }
    writeln!(out, "  ], importedUses := [").unwrap();
    for row in imported_uses {
        write!(out, "    {{ rootSourceOrder := {}, sourceLocator := ", row.root_source_order).unwrap();
        emit_locator(&mut out, &row.source);
        writeln!(out, ", localSourceIndex := {}, occurrenceOrdinal := {}, exposedName := {}, exportOrdinal := {} }},",
            row.local_source_index, row.occurrence, lean_string(&row.exposed_name), row.export_ordinal).unwrap();
    }
    writeln!(out, "  ], roots := [").unwrap();
    for row in roots {
        write!(out, "    {{ sourceOrder := {}, node := ", row.source_order).unwrap(); emit_locator(&mut out, &row.node);
        writeln!(out, ", syntaxKind := {}, hirKind := {}, declarationName := {}, definitionOrdinal := {} }},",
            lean_string(&row.syntax_kind), lean_string(&row.hir_kind),
            row.declaration_name.as_deref().map(lean_string).map(|s| format!("some {s}")).unwrap_or_else(|| "none".into()),
            row.definition_ordinal.map(|x| format!("some {x}")).unwrap_or_else(|| "none".into())).unwrap();
    }
    writeln!(out, "  ], selectedRootOrder := {selected_root_order}, selected := {{").unwrap();
    out.push_str(selected_value);
    writeln!(out, "  }}, unresolved := [").unwrap();
    writeln!(out, "    \"No adopted import-to-OriginalSource.Context elaboration equation maps resolver identities to every Binding field.\",").unwrap();
    writeln!(out, "    \"No adopted complete module-root-to-OriginalSource.Source equation covers the import root; route and ambient scope are not constructed.\",").unwrap();
    writeln!(out, "    \"Runtime OwnedFrame provenance is outside this finite caller resolver trace.\"").unwrap();
    writeln!(out, "  ] }}\nend YulangClosure.OriginalSourceCallerReificationTrace").unwrap();
    let _ = selected_value;
    out
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

fn emit_selected_value(
    parsed: &ParsedFile,
    module_name: &str,
    source_file: &str,
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
    writeln!(out, "    inputUtf8 := {}, sourceModule := {}, sourceFile := {},",
        lean_string(parsed.source()), lean_string(module_name), lean_string(source_file)).unwrap();
    writeln!(out, "    physical := [").unwrap();
    write_physical_definition(&mut out, definition);
    for (key, owner) in owners { write_physical(&mut out, key, owner); }
    writeln!(out, "    ],").unwrap();
    writeln!(out, "    formals := [").unwrap();
    write_formal(&mut out, "outer", "outerLambda", outer_parameter, outer_binder);
    write_formal(&mut out, "inner", "innerLambda", inner_parameter, inner_binder);
    writeln!(out, "    ], wilds := [{{ key := .outer, formal := .outer }}, {{ key := .inner, formal := .inner }}],").unwrap();
    writeln!(out, "    names := [").unwrap();
    writeln!(out, "      {{ key := .declaration, owner := .declaration .value, spelling := \"value\" }},").unwrap();
    writeln!(out, "    {{ key := .outer, owner := .parameter .outer, spelling := \"{}\" }},", outer_parameter.spelling).unwrap();
    writeln!(out, "    {{ key := .inner, owner := .parameter .inner, spelling := \"{}\" }},", inner_parameter.spelling).unwrap();
    writeln!(out, "    ], declarations := [{{ key := .value, sourceNode := .definition, definitionRootOrdinal := {module_root_ordinal} }}],").unwrap();
    writeln!(out, "    statements := [{{ key := .application, block := .outerBody, sourceOrder := 0, expression := .application }}],").unwrap();
    writeln!(out, "    resolutions := [").unwrap();
    for evidence in names {
        write_resolution(&mut out, evidence.occurrence, evidence.key, evidence.parameter);
    }
    writeln!(out, "    ], groups := [{{ group := .rawCallee, projected := .innerLambda }}],").unwrap();
    writeln!(out, "    body := [").unwrap();
    for entry in body {
        let kind = if entry.final_expr { ".finalExpression" } else { ".statementExpression" };
        let key = if entry.final_expr { "sibling" } else { "application" };
        writeln!(out, "    {{ sourceOrder := {}, occurrence := .{key}, kind := {kind} }},", entry.order).unwrap();
    }
    writeln!(out, "    ], callerContext := none }}").unwrap();
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
    let cwd = std::env::current_dir()?;
    let manifest_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).canonicalize()?;
    let repo_root = manifest_root.join("../..").canonicalize()?;
    if cwd != repo_root { return Err(format!("working directory mismatch: actual={} expected={}", cwd.display(), repo_root.display()).into()); }
    let expected_output = repo_root.join(OUTPUT);
    let output = std::env::args_os().nth(1).map(PathBuf::from).ok_or("required absolute output target argument is missing")?;
    if std::env::args_os().nth(2).is_some() { return Err("unexpected extra argument".into()); }
    if !output.is_absolute() || output != expected_output { return Err(format!("output target mismatch: actual={} expected_absolute={}", output.display(), expected_output.display()).into()); }

    let modules = owner_modules()?;
    let consumer = &modules[0];
    let provider_indexes = modules.iter().skip(1).map(|module| module.index.clone()).collect::<Vec<_>>();
    let imports = availability("construct consumer source imports", SemanticImports::with_source_imports(&consumer.parsed, &consumer.identity, &provider_indexes))?;
    let hir = availability("lower consumer HIR", lower(&consumer.parsed, consumer.identity.clone(), imports.clone()))?;
    assert_eq!(hir.identity(), &consumer.identity);
    let environment = hir.source_imports().ok_or("lowered consumer omitted import environment")?;
    assert_eq!(environment.identity(), &consumer.identity);
    assert_eq!(environment.parse_root(), &consumer.parsed.source_root().key(), "resolver bound to consumer parse root");
    let alias_resolution = resolved_import(&hir, "identity")?;
    let glob_resolution = resolved_import(&hir, "id")?;
    assert_eq!(alias_resolution.module.as_ref(), "std::core");
    assert_eq!(alias_resolution.name.as_ref(), "id");
    assert_eq!(glob_resolution.identity(), alias_resolution.identity(), "prelude glob and named alias resolve to one exact provider identity");
    let core = modules.iter().find(|module| module.name == "std::core").ok_or("core provider absent")?;
    assert!(core.parsed.owns_source_key(&alias_resolution.declaration.source));
    let core_imports = availability("construct provider source imports", SemanticImports::with_source_imports(&core.parsed, &core.identity, &provider_indexes))?;
    let core_hir = availability("lower exact provider HIR", lower(&core.parsed, core.identity.clone(), core_imports))?;
    let core_binding = core_hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "id" => Some(binding), _ => None,
    }).ok_or("resolved provider HIR binding `id` missing")?;
    assert!(core_hir.owns_definition_root(core_binding.definition_root()));
    assert_eq!(core_hir.identity(), &core.identity);
    assert_eq!(availability("provider definition source key", core_hir.definition_source_key(core_binding.definition_root()))?.expect("provider definition source"), &alias_resolution.declaration.source);
    assert_eq!(core_binding.range(), &alias_resolution.declaration.range);

    let (roots, selected_root_order, binding) = root_inventory(consumer, &hir)?;
    let imports_table = flatten_owned_imports(&modules)?;
    assert!(imports_table.iter().any(|row| row.owner_module == consumer.ordinal
        && row.path == ["std", "core", "id"] && row.selected_name.as_deref() == Some("id")
        && row.alias.as_deref() == Some("identity") && !row.is_glob), "consumer alias leaf is retained");
    assert!(imports_table.iter().any(|row| row.owner_module == module_ordinal(&modules, "std::prelude").unwrap()
        && row.path == ["std", "core"] && row.selected_name.is_none() && row.is_glob), "provider prelude glob leaf is retained");
    let exports = export_rows(&modules)?;
    let identity = alias_resolution.identity();
    let export = exports.iter().find(|row| row.identity == identity).ok_or("provider export row missing")?;
    let lookups = lookup_evidence(&hir, &["identity", "id"], &exports, &imports_table, &modules)?;
    assert_eq!(lookups.len(), 2);
    assert_eq!(lookups[0].export_ordinal, lookups[1].export_ordinal);
    assert_eq!(lookups[0].route.len(), 0, "named direct provider has empty public re-export route");
    assert_eq!(lookups[1].route.len(), 1, "prelude glob route retains one exact provider use leaf");
    let imported_uses = imported_use_rows(consumer, &hir, &roots, &exports)?;
    assert!(imported_uses.iter().any(|row| row.exposed_name == "identity" && row.export_ordinal == export.ordinal));
    assert!(imported_uses.iter().any(|row| row.exposed_name == "id" && row.export_ordinal == export.ordinal));

    let root = SourceRootId::Definition(binding.definition_root().clone());
    assert!(hir.owns_source_root(&root));
    let definition_key = availability("selected definition source key", hir.definition_source_key(binding.definition_root()))?.ok_or("selected definition source missing")?;
    let definition = locator_for_key(&consumer.parsed, &consumer.artifact, definition_key);
    assert_eq!(definition.range, *binding.range());
    let source = availability("selected LocalSource", hir.local_source_for(&root))?.ok_or("selected source carrier absent")?;
    assert_eq!(source.source_root(), &root);
    let outer_index = source.body().clone();
    let outer = expression(source, &root, &outer_index);
    let LocalSourceForm::Lambda { parameter: outer_parameter, body: body_index } = &outer.form else { return Err("selected value is not the accepted outer Lambda".into()); };
    assert!(matches!(&outer_parameter.scope, LocalSourceScope::Definition(id) if id == binding.definition_root()));
    let outer_binder = binder_locator(&consumer.parsed, &consumer.artifact, &hir, outer_parameter, &root)?;
    assert_eq!(outer_binder.range, outer_parameter.range);
    let body_expr = expression(source, &root, body_index);
    let LocalSourceForm::StatementBlock { statements, final_expression } = &body_expr.form else { return Err("selected body is not the accepted StatementBlock".into()); };
    assert_eq!(statements.len(), 1);
    let LocalSourceStatement::Expression(apply_index) = &statements[0] else { return Err("accepted body prefix is not an expression statement".into()); };
    let apply = expression(source, &root, apply_index);
    let LocalSourceForm::Apply { callee: raw_callee_index, argument: argument_index, .. } = &apply.form else { return Err("accepted body statement is not Apply".into()); };
    let raw_callee = expression(source, &root, raw_callee_index);
    let LocalSourceForm::Group { inner: projected_index } = &raw_callee.form else { return Err("raw Apply callee lost Group".into()); };
    let projected = expression(source, &root, projected_index);
    let LocalSourceForm::Lambda { parameter: inner_parameter, body: inner_body_index } = &projected.form else { return Err("Group child is not nested Lambda".into()); };
    assert_ne!(outer_parameter.id, inner_parameter.id);
    assert_eq!(outer_parameter.spelling, inner_parameter.spelling);
    assert_eq!(inner_parameter.source, projected.source);
    assert!(matches!(&inner_parameter.scope, LocalSourceScope::Expression(_)));
    let inner_binder = binder_locator(&consumer.parsed, &consumer.artifact, &hir, inner_parameter, &root)?;
    assert_eq!(inner_binder.range, inner_parameter.range);
    let inner_body = expression(source, &root, inner_body_index);
    let argument = expression(source, &root, argument_index);
    let LocalSourceForm::Name { spelling: arg_name, resolution: LocalSourceResolution::Parameter(arg_parameter) } = &argument.form else { return Err("accepted application argument is not the outer parameter".into()); };
    let LocalSourceForm::Name { spelling: body_name, resolution: LocalSourceResolution::Parameter(body_parameter) } = &inner_body.form else { return Err("nested lambda body is not the inner parameter".into()); };
    assert_eq!(arg_parameter, &outer_parameter.id);
    assert_eq!(body_parameter, &inner_parameter.id);
    assert_eq!(arg_name, &outer_parameter.spelling);
    assert_eq!(body_name, &inner_parameter.spelling);
    let sibling = expression(source, &root, final_expression);
    let LocalSourceForm::Name { spelling: sibling_name, resolution: LocalSourceResolution::Parameter(sibling_parameter) } = &sibling.form else { return Err("accepted final expression is not the restored outer parameter".into()); };
    assert_eq!(sibling_parameter, &outer_parameter.id);
    assert_eq!(sibling_name, &outer_parameter.spelling);
    let owner = |label, index| owner_expr(&consumer.parsed, &consumer.artifact, &hir, source, &root, label, index);
    let outer_owner = owner("outerLambda", &outer_index);
    let body_owner = owner("outerBody", body_index);
    let app_owner = owner("application", apply_index);
    let group_owner = owner("rawCallee", raw_callee_index);
    let argument_owner = owner("argument", argument_index);
    let inner_owner = owner("innerLambda", projected_index);
    let inner_body_owner = owner("innerBody", inner_body_index);
    let sibling_owner = owner("sibling", final_expression);
    assert_ne!(group_owner.index, inner_owner.index);
    let body_entries = vec![BodyEvidence { order: 0, expr: app_owner.clone(), final_expr: false },
        BodyEvidence { order: 1, expr: sibling_owner.clone(), final_expr: true }];
    let names = vec![
        NameEvidence { key: "outer", occurrence: "argument", expr: argument_owner.clone(), parameter: outer_parameter.id.ordinal() },
        NameEvidence { key: "inner", occurrence: "innerBody", expr: inner_body_owner.clone(), parameter: inner_parameter.id.ordinal() },
        NameEvidence { key: "outer", occurrence: "sibling", expr: sibling_owner.clone(), parameter: outer_parameter.id.ordinal() },
    ];
    assert_eq!(key_for_name(outer_parameter, outer_parameter, inner_parameter), "outer");
    assert_eq!(key_for_name(inner_parameter, outer_parameter, inner_parameter), "inner");
    let owners = [("outerLambda", &outer_owner), ("outerBody", &body_owner), ("application", &app_owner),
        ("rawCallee", &group_owner), ("argument", &argument_owner), ("innerLambda", &inner_owner),
        ("innerBody", &inner_body_owner), ("sibling", &sibling_owner)];
    let selected_value = emit_selected_value(&consumer.parsed, consumer.name, consumer.file,
        &definition, &owners, outer_parameter, &outer_binder, inner_parameter, &inner_binder,
        &names, &group_owner, &inner_owner, &body_entries, binding.id().same_name_ordinal());

    // Foreign parse rejection and foreign HIR occurrence rejection both run before output publication.
    let foreign_parse = parse(CONSUMER_INPUT);
    assert!(!consumer.parsed.owns_source_key(&foreign_parse.source_root().key()));
    assert!(matches!(consumer.artifact.source_position(&foreign_parse.source_root().key()), Err(SourceIdentityError::ForeignParse)));
    assert!(matches!(lower(&foreign_parse, consumer.identity.clone(), imports.clone()), Err(HirAvailabilityError::ForeignSourceImport)));
    let foreign_imports = availability("construct foreign source imports", SemanticImports::with_source_imports(&foreign_parse, &consumer.identity, &provider_indexes))?;
    let foreign_hir = availability("lower separately branded foreign HIR", lower(&foreign_parse, consumer.identity.clone(), foreign_imports))?;
    let foreign_binding = foreign_hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "value" => Some(binding), _ => None,
    }).ok_or("foreign HIR selected declaration absent")?;
    let foreign_root = SourceRootId::Definition(foreign_binding.definition_root().clone());
    let foreign_source = availability("foreign HIR LocalSource", foreign_hir.local_source_for(&foreign_root))?.ok_or("foreign HIR LocalSource absent")?;
    let foreign_occurrence = &foreign_source.expressions()[0].occurrence;
    assert!(foreign_hir.owns_occurrence(foreign_occurrence));
    assert!(!hir.owns_occurrence(foreign_occurrence));
    assert!(hir.occurrence_source_key(foreign_occurrence).is_err());

    let generated = emit_caller_table(&modules, &imports_table, &exports, &lookups, &imported_uses,
        &roots, selected_root_order, &selected_value);
    std::fs::write(&output, generated)?;
    println!("consumer roots={} imports={} exports={} lookups={} imported_uses={} selected_root={} provider=std::core::id alias_and_glob_identity=equal foreign_parse=REJECTED foreign_hir=REJECTED", roots.len(), imports_table.len(), exports.len(), lookups.len(), imported_uses.len(), selected_root_order);
    println!("selected_nested_subtree=preserved outer={} inner={} group_projection=authenticated ordered_body=2 cwd={} absolute_output={}", outer_parameter.id.ordinal(), inner_parameter.id.ordinal(), cwd.display(), output.display());
    println!("unresolved=import-to-Context-elaboration, import-root-to-OriginalSource-root, runtime-OwnedFrame");
    Ok(())
}
