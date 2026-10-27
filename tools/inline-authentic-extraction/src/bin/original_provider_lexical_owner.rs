use std::{
    env,
    fs,
    ops::Range,
    path::{Path, PathBuf},
    sync::Arc,
};

use yu_hir::{
    FileId, FileKey, HirItem, LocalSourceForm, LocalSourceResolution,
    ModuleIdentity, SemanticImports, SourceExportId, SourceExportIndex,
    SourceImportEnvironment, SourceRootId,
    index_source_exports, lower_module,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const PROVIDER_TEXT: &str = "pub id x = x\n";
const PROVIDER_SHA256: &str = "9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e";
const PROVIDER_MODULE: &str = "std::core";
const PROVIDER_FILE: &str = "lib/std/core.yu";
const LEAN_MODULE: &str = "OriginalProviderLexicalOwnerTrace";
const OUTPUT_RELATIVE: &str = "notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean";

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn module_identity(module: &str, file: &str) -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new(module, file)))
}

fn range_tuple(range: &Range<usize>) -> (usize, usize) {
    (range.start, range.end)
}

fn lean_string(value: &str) -> String {
    format!("{value:?}")
}

fn lean_range(range: &Range<usize>) -> String {
    format!("({}, {})", range.start, range.end)
}

fn source_key_owned(parsed: &ParsedFile, key: &yu_syntax::SourceNodeKey) -> bool {
    parsed.owns_source_key(key)
}

fn checked_definition<'a>(
    parsed: &ParsedFile,
    module: &'a yu_hir::HirModule,
    name: &str,
) -> Result<&'a yu_hir::HirBinding, Box<dyn std::error::Error>> {
    let mut found = None;
    for item in module.items() {
        if let HirItem::Binding(binding) = item {
            if binding.name().spelling() == name {
                if found.replace(binding).is_some() {
                    return Err(format!("multiple HIR bindings named {name:?}").into());
                }
            }
        }
    }
    let binding = found.ok_or_else(|| format!("HIR binding {name:?} absent"))?;
    let key = module
        .definition_source_key(binding.definition_root())
        .map_err(|error| format!("provider definition source owner query failed: {error:?}"))?
        .ok_or("HIR binding has no original definition source key")?;
    if !source_key_owned(parsed, key) {
        return Err("selected HIR definition source key is foreign to provider parse".into());
    }
    if &parsed.source()[binding.range().clone()] != PROVIDER_TEXT.trim_end() {
        return Err("HIR declaration range is not the exact provider declaration".into());
    }
    Ok(binding)
}

fn owner_rows(
    parsed: &ParsedFile,
    hir: &yu_hir::HirModule,
    binding: &yu_hir::HirBinding,
) -> Result<(Range<usize>, Range<usize>, u32, u32, Range<usize>, u32, u32), Box<dyn std::error::Error>> {
    if binding.parameters().len() != 1 {
        return Err(format!("expected the exact one-formal provider; got {}", binding.parameters().len()).into());
    }
    let source = hir
        .local_source(binding.definition_root())
        .map_err(|error| format!("provider LocalSource owner query failed: {error:?}"))?
        .ok_or("HIR definition has no LocalSource carrier")?;
    if source.source_root() != &SourceRootId::Definition(binding.definition_root().clone()) {
        return Err("LocalSource is not owned by selected definition root".into());
    }
    let group = source
        .named_groups()
        .first()
        .ok_or("LocalSource omitted the named formal group")?;
    if source.named_groups().len() != 1 || group.formals.len() != 1 {
        return Err("LocalSource named-group inventory differs from exact provider".into());
    }
    if group.owner != yu_hir::LocalSourceNamedGroupOwner::Definition(binding.definition_root().clone()) {
        return Err("named-formal group is not owned by selected HIR definition".into());
    }
    let lambda = source
        .expression(&group.formals[0].lambda)
        .ok_or("named-formal lambda index is foreign to its LocalSource")?;
    let LocalSourceForm::Lambda { parameter, body } = &lambda.form else {
        return Err("named-formal owner does not point to a Lambda expression".into());
    };
    if &parameter.id != binding.parameters()[0].id()
        || parameter.spelling.as_ref() != "x"
        || group.formals[0].parameter != parameter.id
        || parameter.id.source_root() != &yu_hir::SourceRootId::Definition(binding.definition_root().clone())
        || !hir.owns_parameter(&parameter.id)
        || group.enclosing.is_some()
        || !parsed.owns_source_key(&group.source)
    {
        return Err("LocalSource formal does not join to HIR's exact named parameter".into());
    }
    let body_expr = source
        .expression(body)
        .ok_or("formal body index is foreign to its LocalSource")?;
    let LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(resolved) } =
        &body_expr.form
    else {
        return Err("provider body occurrence is not a resolved parameter name".into());
    };
    if spelling.as_ref() != "x" || resolved != &parameter.id {
        return Err("provider body name does not resolve to the retained named formal".into());
    }
    if resolved != binding.parameters()[0].id()
        || !hir.owns_parameter(resolved)
        || group.owner != yu_hir::LocalSourceNamedGroupOwner::Definition(binding.definition_root().clone())
    {
        return Err("formal/body lexical ownership chain does not terminate at the selected definition".into());
    }
    if !parsed.owns_source_key(&parameter.source) || !parsed.owns_source_key(&body_expr.source) {
        return Err("formal or body SourceNodeKey is foreign to exact provider parse".into());
    }
    if &parsed.source()[parameter.range.clone()] != "x"
        || &parsed.source()[body_expr.range.clone()] != "x"
    {
        return Err("formal/body byte ranges do not select exact source spelling".into());
    }
    Ok((
        binding.range().clone(),
        parameter.range.clone(),
        parameter.id.ordinal(),
        group.formals[0].lambda.ordinal(),
        body_expr.range.clone(),
        body.ordinal(),
        body_expr.occurrence.ordinal(),
    ))
}

fn provider_index(
    parsed: &ParsedFile,
    module: &str,
    file: &str,
) -> Result<SourceExportIndex, Box<dyn std::error::Error>> {
    index_source_exports(module_identity(module, file), parsed)
        .map_err(|error| format!("source export indexing failed for {module}: {error:?}").into())
}

fn publication_identity(
    environment: &SourceImportEnvironment,
    exposed: &str,
) -> Result<SourceExportId, Box<dyn std::error::Error>> {
    let Some(yu_hir::SourceImportBinding::Resolved(resolution)) = environment.resolve(exposed) else {
        return Err(format!("source import {exposed:?} is not uniquely resolved").into());
    };
    Ok(resolution.identity())
}

fn render_trace(
    cwd: &Path,
    output: &Path,
    declaration: &Range<usize>,
    formal: &Range<usize>,
    parameter_ordinal: u32,
    lambda_index: u32,
    body: &Range<usize>,
    body_index: u32,
    occurrence: u32,
    exports: &[(&str, SourceExportId)],
    explicit_identity_matches: bool,
    prelude_id_matches: bool,
    parsed_key_owner: bool,
    definition_root_owner: bool,
) -> String {
    let exposure_rows = exports
        .iter()
        .map(|(exposed, id)| {
            format!(
                "  {{ exposedName := {}, providerModule := {}, providerName := {}, providerDeclarationRange := {}, matchesSameProviderIdentity := true }},\n",
                lean_string(exposed),
                lean_string(&id.module),
                lean_string(&id.name),
                lean_range(&id.range),
            )
        })
        .collect::<String>();
    format!(
        "import Std\n\nnamespace YulangClosure.{LEAN_MODULE}\n\ninductive OwnerNode where\n  | declaration | lambda | formal | bodyName\n  deriving DecidableEq, Repr\n\nstructure LexicalParentEdge where\n  child : OwnerNode\n  parent : OwnerNode\n  deriving DecidableEq, Repr\n\nstructure ProviderDeclarationRow where\n  moduleName : String\n  sourceFile : String\n  name : String\n  byteStart : Nat\n  byteEnd : Nat\n  isPublic : Bool\n  parsedSourceKeyOwned : Bool\n  definitionRootOwned : Bool\n  deriving DecidableEq, Repr\n\nstructure ProviderFormalRow where\n  spelling : String\n  byteStart : Nat\n  byteEnd : Nat\n  hirParameterOrdinal : Nat\n  localSourceLambdaOrdinal : Nat\n  lexicalParent : OwnerNode\n  deriving DecidableEq, Repr\n\nstructure ProviderBodyNameRow where\n  spelling : String\n  byteStart : Nat\n  byteEnd : Nat\n  resolvedHirParameterOrdinal : Nat\n  localSourceIndexOrdinal : Nat\n  hirOccurrenceOrdinal : Nat\n  lexicalParent : OwnerNode\n  deriving DecidableEq, Repr\n\nstructure ProviderOwnerRows where\n  declaration : ProviderDeclarationRow\n  formal : ProviderFormalRow\n  bodyName : ProviderBodyNameRow\n  lexicalParents : List LexicalParentEdge\n  deriving DecidableEq, Repr\n\nstructure ConsumerExposure where\n  exposedName : String\n  providerModule : String\n  providerName : String\n  providerDeclarationRange : Nat × Nat\n  matchesSameProviderIdentity : Bool\n  deriving DecidableEq, Repr\n\n/-- These constructor-shaped rows are serialized only after Rust has compared the branded DefinitionRootId, HirParameterId, SourceNodeKey, HirOccurrenceId, and complete SourceExportId values. HIR ordinals remain separate provenance fields; the consumer derives logical coordinates from constructors. -/\ndef providerOwnerRows : ProviderOwnerRows := {{\n  declaration := {{ moduleName := {}, sourceFile := {}, name := \"id\", byteStart := {}, byteEnd := {}, isPublic := true, parsedSourceKeyOwned := {}, definitionRootOwned := {} }},\n  formal := {{ spelling := \"x\", byteStart := {}, byteEnd := {}, hirParameterOrdinal := {}, localSourceLambdaOrdinal := {}, lexicalParent := .lambda }},\n  bodyName := {{ spelling := \"x\", byteStart := {}, byteEnd := {}, resolvedHirParameterOrdinal := {}, localSourceIndexOrdinal := {}, hirOccurrenceOrdinal := {}, lexicalParent := .formal }},\n  lexicalParents := [{{ child := .lambda, parent := .declaration }}, {{ child := .formal, parent := .lambda }}, {{ child := .bodyName, parent := .formal }}]\n}}\n\ndef consumerExposures : List ConsumerExposure := [\n{}]\n\ndef exactProviderPublicationIdentityChecked : Bool := {}\ndef explicitIdentityResolvesToProvider : Bool := {}\ndef implicitPreludeIdResolvesToProvider : Bool := {}\ndef providerUtf8Sha256 : String := {}\n/-- The owner rows establish provider provenance and lexical identity only. They do not provide initializer execution or original logical event payloads. -/\ndef traceBoundary : String := \"HIR/CST owner rows only; initializer execution and Return/Shared payloads absent\"\ndef originalSourceAttempt : String := \"OPEN: no actual Rust owner constructs OriginalSource.Source and the incoming Context from this HIR/CST evidence\"\ndef firstMissingOwner : String := \"provider Source/Context introduction: declaration/formal/body owners exist, but Source Site/Name/Declaration allocation, Context, and independent local source admission are absent\"\ndef initializerEventStatus : String := \"OPEN: no semantic initializer execution, Return-rebind frame, Shared frame, or captures supplied\"\ndef fixedPublicationMapStatus : String := \"OPEN: no actual PublicationRecord or independently justified Environment.publications equation supplied\"\ndef actualWorkingDirectory : String := {}\ndef absoluteOutputTarget : String := {}\n\nend YulangClosure.{LEAN_MODULE}\n",
        lean_string(PROVIDER_MODULE), lean_string(PROVIDER_FILE), declaration.start, declaration.end,
        parsed_key_owner, definition_root_owner, formal.start, formal.end, parameter_ordinal, lambda_index, body.start, body.end,
        parameter_ordinal, body_index, occurrence, exposure_rows.trim_end(), explicit_identity_matches && prelude_id_matches,
        explicit_identity_matches, prelude_id_matches, lean_string(PROVIDER_SHA256),
        lean_string(&cwd.to_string_lossy()), lean_string(&output.to_string_lossy()),
    )
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let output = PathBuf::from(env::args_os().nth(1).ok_or("expected one absolute output path")?);
    if !output.is_absolute() {
        return Err("output path must be absolute".into());
    }
    let cwd = env::current_dir()?;
    if output != cwd.join(OUTPUT_RELATIVE) {
        return Err(format!("output must be the exact leased path {}", cwd.join(OUTPUT_RELATIVE).display()).into());
    }
    if fs::read_dir(&cwd)?.next().is_none() {
        return Err("unexpected empty execution directory".into());
    }
    if PROVIDER_TEXT.as_bytes() != b"pub id x = x\n" {
        return Err("provider source bytes differ from fixed UTF-8 fixture".into());
    }

    let provider = parse(PROVIDER_TEXT);
    let syntax_diagnostics = provider
        .syntax_diagnostics()
        .map_err(|error| format!("provider syntax diagnostic projection failed: {error:?}"))?;
    let provider_id = module_identity(PROVIDER_MODULE, PROVIDER_FILE);
    let provider_hir = lower_module(
        provider_id.clone(),
        &provider,
        SemanticImports::empty(),
    )
    .map_err(|error| format!("lower exact provider HIR with LocalSource: {error:?}; parser diagnostics: {syntax_diagnostics:#?}"))?;
    let binding = checked_definition(&provider, &provider_hir, "id")?;
    if binding.visibility() != yu_hir::HirVisibility::Public {
        return Err("provider binding is not HIR-public".into());
    }
    let (declaration_range, formal_range, parameter_ordinal, lambda_index, body_range, body_index, occurrence) =
        owner_rows(&provider, &provider_hir, binding)?;
    let provider_export_index = provider_index(&provider, PROVIDER_MODULE, PROVIDER_FILE)?;
    let provider_export = provider_export_index
        .declarations
        .iter()
        .find(|row| row.name.as_deref() == Some("id"))
        .ok_or("source export index omitted exact provider id declaration")?;
    if !provider.owns_source_key(&provider_export.source)
        || provider_export.range != declaration_range
        || provider_export.namespace.as_ref() != PROVIDER_MODULE
        || !provider_export.public
        || provider_export.recovered
    {
        return Err("public SourceExportId does not join to exact provider HIR declaration".into());
    }
    let provider_export_id = SourceExportId {
        module: PROVIDER_MODULE.into(),
        name: "id".into(),
        source: provider_export.source.clone(),
        range: provider_export.range.clone(),
        kind: provider_export.kind,
    };
    let provider_export_source = provider_export.source.clone();

    let foreign_parse = parse(PROVIDER_TEXT);
    let foreign_parse_key = foreign_parse.source_root().key();
    if provider.owns_source_key(&foreign_parse_key) {
        return Err("foreign parse ownership rejection failed".into());
    }
    let foreign_hir = lower_module(
        module_identity(PROVIDER_MODULE, "lib/std/core-foreign.yu"),
        &foreign_parse,
        SemanticImports::empty(),
    )
    .map_err(|error| format!("lower foreign provider HIR for ownership rejection: {error:?}"))?;
    let foreign_binding = checked_definition(&foreign_parse, &foreign_hir, "id")?;
    let foreign_source = foreign_hir
        .local_source(foreign_binding.definition_root())
        .map_err(|error| format!("foreign HIR LocalSource owner query failed: {error:?}"))?
        .ok_or("foreign HIR omitted LocalSource needed for ownership check")?;
    let foreign_body = foreign_source
        .expressions()
        .iter()
        .find(|expression| expression.range == body_range)
        .ok_or("foreign HIR body occurrence not found")?;
    if provider_hir.owns_occurrence(&foreign_body.occurrence) {
        return Err("foreign HIR occurrence ownership rejection failed".into());
    }
    let selected_source = provider_hir
        .local_source(binding.definition_root())
        .map_err(|error| format!("selected HIR LocalSource owner query failed: {error:?}"))?
        .ok_or("selected HIR omitted its checked LocalSource")?;
    let selected_body = selected_source
        .expression(&selected_source.named_groups()[0].terminal_body)
        .ok_or("selected named group omitted its terminal body")?;
    if !provider_hir.owns_occurrence(&selected_body.occurrence) {
        return Err("selected HIR does not own its provider body occurrence".into());
    }

    let std_root = parse("pub mod core;\npub mod prelude;");
    let prelude = parse("pub use std::core::*\n");
    let std_index = provider_index(&std_root, "std", "lib/std.yu")?;
    let prelude_index = provider_index(&prelude, "std::prelude", "lib/std/prelude.yu")?;
    let consumer_text = "use std::core::id as identity\npub first = identity 1\npub second = id 2\n";
    let consumer = parse(consumer_text);
    let consumer_identity = module_identity("provider-source-consumer", "consumer.yu");
    let imports = SemanticImports::with_source_imports(
        &consumer,
        &consumer_identity,
        &[std_index, provider_export_index, prelude_index],
    )
    .map_err(|error| format!("source imports for exact consumer fixture failed: {error:?}"))?;
    let environment = imports
        .source_imports()
        .ok_or("source import environment was not retained by HIR owner API")?;
    let explicit = publication_identity(environment, "identity")?;
    let implicit = publication_identity(environment, "id")?;
    let explicit_identity_matches = explicit == provider_export_id;
    let prelude_id_matches = implicit == provider_export_id;
    if !explicit_identity_matches || !prelude_id_matches || explicit != implicit {
        return Err("consumer exposures do not retain exact same provider SourceExportId".into());
    }
    let exposure_rows = vec![("identity", explicit), ("id", implicit)];

    // Ownership rejection is complete before the only output write.
    let trace = render_trace(
        &cwd,
        &output,
        &declaration_range,
        &formal_range,
        parameter_ordinal,
        lambda_index,
        &body_range,
        body_index,
        occurrence,
        &exposure_rows,
        explicit_identity_matches,
        prelude_id_matches,
        provider.owns_source_key(&provider_export_source)
            && provider_hir
                .definition_source_key(binding.definition_root())
                .map_err(|error| format!("provider definition source owner query failed: {error:?}"))?
                .is_some_and(|key| provider.owns_source_key(key))
            && provider.owns_source_key(&foreign_parse_key) == false,
        provider_hir.owns_definition_root(binding.definition_root())
            && provider_hir.owns_parameter(binding.parameters()[0].id())
            && provider_hir.owns_occurrence(&selected_body.occurrence),
    );
    fs::write(&output, trace)?;
    println!("provider_utf8_sha256={PROVIDER_SHA256}");
    println!("provider_hir_definition={}::{}#{}", PROVIDER_MODULE, binding.name().spelling(), binding.id().same_name_ordinal());
    println!("provider_declaration_bytes={}", range_tuple(&declaration_range).0);
    println!("provider_formal_bytes={:?}", range_tuple(&formal_range));
    println!("provider_body_bytes={:?}; local_source_index={body_index}; occurrence={occurrence}", range_tuple(&body_range));
    println!("consumer_identity_and_id_share_exact_source_export_id=true");
    println!("foreign_parse_rejected=true; foreign_hir_occurrence_rejected=true");
    println!("trace_output={}", output.display());
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("original_provider_lexical_owner: {error}");
        std::process::exit(1);
    }
}
