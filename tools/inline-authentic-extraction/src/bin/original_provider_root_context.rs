use std::{
    env, fs,
    ops::Range,
    path::{Path, PathBuf},
    sync::Arc,
};

use yu_hir::{
    FileId, FileKey, HirItem, LocalSourceForm, LocalSourceResolution, ModuleIdentity,
    SemanticImports, SourceExportIndex, SourceRootId, index_source_exports, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const PROVIDER_TEXT: &str = "pub id x = x\n";
const PROVIDER_SHA256: &str = "9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e";
const PROVIDER_MODULE: &str = "std::core";
const PROVIDER_FILE: &str = "lib/std/core.yu";
const OUTPUT: &str = "notes/theory/lean/YulangClosure/OriginalProviderRootContextTrace.lean";

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn identity(module: &str, file: &str) -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new(module, file)))
}

fn lean_string(value: &str) -> String { format!("{value:?}") }
fn lean_range(range: &Range<usize>) -> String { format!("({}, {})", range.start, range.end) }

fn checked_binding<'a>(
    parsed: &ParsedFile,
    hir: &'a yu_hir::HirModule,
) -> Result<&'a yu_hir::HirBinding, Box<dyn std::error::Error>> {
    let mut found = None;
    for item in hir.items() {
        if let HirItem::Binding(binding) = item {
            if binding.name().spelling() == "id" {
                if found.replace(binding).is_some() { return Err("duplicate provider id binding".into()); }
            }
        }
    }
    let binding = found.ok_or("provider HIR omitted id")?;
    let key = hir.definition_source_key(binding.definition_root())
        .map_err(|error| format!("provider definition source lookup failed: {error:?}"))?
        .ok_or("provider HIR omitted definition source key")?;
    if !parsed.owns_source_key(key) { return Err("definition source key is foreign".into()); }
    if &parsed.source()[binding.range().clone()] != "pub id x = x" {
        return Err("provider HIR declaration range differs from exact provider bytes".into());
    }
    Ok(binding)
}

fn provider_index(
    parsed: &ParsedFile,
    module: &str,
    file: &str,
) -> Result<SourceExportIndex, Box<dyn std::error::Error>> {
    index_source_exports(identity(module, file), parsed)
        .map_err(|error| format!("source export index failed for {module}: {error:?}").into())
}

fn render(
    cwd: &Path,
    output: &Path,
    declaration: &Range<usize>,
    formal: &Range<usize>,
    body: &Range<usize>,
    local_index: u32,
    occurrence: u32,
    export_matches: bool,
    imports_empty_has_no_source_environment: bool,
    consumer_import_environment_retained: bool,
    caller_evidence_absent: bool,
) -> String {
    format!(
        "import YulangClosure.OriginalSourceSyntax\n\nnamespace YulangClosure.OriginalProviderRootContextTrace\n\nopen OriginalSource\n\n\
structure ProviderDeclarationEvidence where\n  moduleName : String\n  sourceFile : String\n  declaration : String\n  declarationRange : Nat × Nat\n  public : Bool\n  definitionRootOwned : Bool\n  deriving DecidableEq, Repr\n\n\
structure ProviderLexicalEvidence where\n  formalName : String\n  formalRange : Nat × Nat\n  bodyName : String\n  bodyRange : Nat × Nat\n  sameHirParameter : Bool\n  localSourceIndex : Nat\n  occurrenceOrdinal : Nat\n  deriving DecidableEq, Repr\n\n\
def providerUtf8Sha256 : String := {}\ndef providerDeclaration : ProviderDeclarationEvidence := {{\n  moduleName := {}, sourceFile := {}, declaration := \"pub id x = x\", declarationRange := {}, public := true, definitionRootOwned := true\n}}\ndef providerLexical : ProviderLexicalEvidence := {{\n  formalName := \"x\", formalRange := {}, bodyName := \"x\", bodyRange := {}, sameHirParameter := true, localSourceIndex := {}, occurrenceOrdinal := {}\n}}\ndef providerExportIdentityJoinsDefinition : Bool := {}\n\n\
def semanticImportsEmptyHasNoImportEnvironment : Bool := {}\ndef semanticImportsWithSourceImportsRetainsEnvironment : Bool := {}\ndef callerEvidenceAbsentOnSourceImports : Bool := {}\ndef rootContextConstructionOwner : String := \"NO_SAFE_CODE_SLICE: inspected HIR module declaration/LocalSource owners and SemanticImports constructors; none constructs or supplies OriginalSource.Context\"\ndef missingAuthority : String := \"no approved constructor maps provider declaration, initializer, imported exports and lexical/source owners to Binding fields (name, Site owner, BindingKind, component, annotation, Entry, singleUse) and ordered Context\"\ndef missingConsumer : String := \"OriginalSourceGeneration.sourceRules consumes Context as an explicit argument; provider entry/admission has no Rust-to-OriginalSource Context bridge\"\ndef prohibitedInferences : String := \"export identity, visibility, spelling and opaque caller payload do not classify Binding fields or establish Context ordering\"\ndef scopeOfNegativeClaim : String := \"the inspected provider fixture and inspected SemanticImports/HirModule/LocalSource construction path only\"\ndef actualWorkingDirectory : String := {}\ndef absoluteOutputTarget : String := {}\n\nend YulangClosure.OriginalProviderRootContextTrace\n",
        lean_string(PROVIDER_SHA256), lean_string(PROVIDER_MODULE), lean_string(PROVIDER_FILE),
        lean_range(declaration), lean_range(formal), lean_range(body), local_index,
        occurrence, export_matches, imports_empty_has_no_source_environment,
        consumer_import_environment_retained, caller_evidence_absent,
        lean_string(&cwd.display().to_string()),
        lean_string(&output.display().to_string()),
    )
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let output = PathBuf::from(env::args_os().nth(1).ok_or("expected exact leased output path")?);
    let cwd = env::current_dir()?;
    if !output.is_absolute() || output != cwd.join(OUTPUT) {
        return Err(format!("output must be exact leased path {}", cwd.join(OUTPUT).display()).into());
    }
    if PROVIDER_TEXT.as_bytes() != b"pub id x = x\n" { return Err("fixture bytes changed".into()); }

    let provider = parse(PROVIDER_TEXT);
    let provider_hir = lower_module(identity(PROVIDER_MODULE, PROVIDER_FILE), &provider, SemanticImports::empty())
        .map_err(|error| format!("provider HIR lowering failed: {error:?}"))?;
    let binding = checked_binding(&provider, &provider_hir)?;
    let root = SourceRootId::Definition(binding.definition_root().clone());
    let source = provider_hir.local_source_for(&root)
        .map_err(|error| format!("provider LocalSource lookup failed: {error:?}"))?
        .ok_or("provider has no LocalSource")?;
    if source.source_root() != &root { return Err("LocalSource root mismatch".into()); }
    let LocalSourceForm::Lambda { parameter: formal, body: body_index } =
        &source.expression(source.body()).ok_or("provider root expression missing")?.form
    else { return Err("provider root is not its expected Lambda".into()); };
    let body = source.expression(body_index).ok_or("provider body LocalSource index missing")?;
    let LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(resolved) } = &body.form
    else { return Err("provider body is not a resolved parameter Name".into()); };
    if spelling.as_ref() != "x" || resolved != &formal.id || resolved != binding.parameters()[0].id() {
        return Err("provider lexical owner join failed".into());
    }

    let exports = provider_index(&provider, PROVIDER_MODULE, PROVIDER_FILE)?;
    let export = exports.declarations.iter().find(|row| row.name.as_deref() == Some("id"))
        .ok_or("source export index omitted provider id")?;
    let export_matches = provider.owns_source_key(&export.source)
        && export.range == *binding.range() && export.public && !export.recovered
        && export.namespace.as_ref() == PROVIDER_MODULE;
    if !export_matches { return Err("provider export failed exact source/HIR join".into()); }

    let std_root = parse("pub mod core;\npub mod prelude;\n");
    let prelude = parse("pub use std::core::*\n");
    let std_index = provider_index(&std_root, "std", "lib/std.yu")?;
    let prelude_index = provider_index(&prelude, "std::prelude", "lib/std/prelude.yu")?;
    let consumer = parse("use std::core::id as identity\npub use_it = identity\n");
    let consumer_identity = identity("root-context-consumer", "consumer.yu");
    let consumer_imports = SemanticImports::with_source_imports(
        &consumer, &consumer_identity, &[std_index, exports, prelude_index],
    ).map_err(|error| format!("consumer source-import construction failed: {error:?}"))?;
    let consumer_import_environment_retained = consumer_imports.source_imports().is_some();
    let caller_evidence_absent = consumer_imports.caller_evidence().is_none();
    let empty_imports = SemanticImports::empty();
    let imports_empty_has_no_source_environment = empty_imports.source_imports().is_none();

    let trace = render(
        &cwd, &output, binding.range(), &formal.range, &body.range,
        body_index.ordinal(), body.occurrence.ordinal(), export_matches,
        imports_empty_has_no_source_environment, consumer_import_environment_retained,
        caller_evidence_absent,
    );
    fs::write(&output, trace)?;
    println!("provider_utf8_sha256={PROVIDER_SHA256}");
    println!("provider_declaration_range={:?}; formal_range={:?}; body_range={:?}",
        binding.range(), formal.range, body.range);
    println!("hir_parameter={} body_resolves_same_parameter=true", formal.id.ordinal());
    println!("source_export_joins_exact_public_hir_declaration={export_matches}");
    println!("SemanticImports::empty_has_no_source_environment={imports_empty_has_no_source_environment}");
    println!("with_source_imports_retains_environment={consumer_import_environment_retained}; caller_evidence_absent={caller_evidence_absent}");
    println!("trace_output={}", output.display());
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("original_provider_root_context: {error}");
        std::process::exit(1);
    }
}
