//! Finite, research-only extraction of real resolved HIR operation signatures.
//!
//! Run from any directory: `source_signature_r300 [--lean] INPUT.yu`.
//! JSON is the default; `--lean` emits data of the existing R300 syntax type.
//! Native keys are interned by their complete Eq identity during this execution.
//! Serialized numbers name those equivalence classes only within this artifact;
//! ranges, spellings and position ordinals are diagnostic locators, not identity.
//! This does not execute solver preflight, prove Rust/Lean equivalence, or supply
//! original IF, field licenses, EvalInvoke registration, or R159 admission.

use std::{collections::HashMap, fmt::Write as _, ops::Range, path::Path, sync::Arc};

use yu_hir::shadow::{
    LocalSourceForm, ShadowArtifact, SourceAnnotationType, SourceAnnotationValue, SourceEffectId,
    SourceEffectRow, SourceOperationDeclaration, SourceOperationResolution,
    lower_module_with_local_source,
};
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, HirVisibility, LocalSource, LocalSourceIndex,
    ModuleIdentity, SemanticImports,
};
use yu_syntax::{
    ParsedFile, SourceNodeKey, SourceText, SyntaxEnvironment, parse_file, scan_header,
};

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct KeyRecord {
    id: usize,
    position: usize,
    range: Range<usize>,
    kind: String,
}

struct Keys<'a> {
    parsed: &'a ParsedFile,
    artifact: &'a ShadowArtifact,
    native: HashMap<SourceNodeKey, usize>,
    records: Vec<KeyRecord>,
}

impl<'a> Keys<'a> {
    fn new(parsed: &'a ParsedFile, artifact: &'a ShadowArtifact) -> Self {
        Self {
            parsed,
            artifact,
            native: HashMap::new(),
            records: Vec::new(),
        }
    }

    fn intern(&mut self, key: &SourceNodeKey) -> Result<usize> {
        if !self.parsed.owns_source_key(key) || !self.artifact.parsed().owns_source_key(key) {
            return Err("foreign parse key rejected".into());
        }
        // Always authenticate before interning, including repeated keys.
        let position = self
            .artifact
            .source_position(key)
            .map_err(|error| format!("source key has no unique artifact position: {error:?}"))?;
        let value = self
            .artifact
            .position(&position)
            .map_err(|error| format!("position owner mismatch: {error:?}"))?;
        let ordinal = self
            .artifact
            .positions()
            .iter()
            .position(|candidate| std::ptr::eq(candidate, value))
            .ok_or("position is not in the selected artifact")?;
        if let Some(&id) = self.native.get(key) {
            return Ok(id);
        }
        let id = self.records.len();
        self.native.insert(key.clone(), id);
        self.records.push(KeyRecord {
            id,
            position: ordinal,
            range: value.range().clone(),
            kind: format!("{:?}", value.kind()),
        });
        Ok(id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Family {
    id: usize,
    declaration: usize,
    realm: String,
    module_path: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    position: usize,
    concrete: Vec<usize>,
    variables: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Annotation {
    effects: Option<Row>,
    value: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Unit,
    Int,
    Bool,
    Str,
    Variable(String),
    Hole(usize),
    Tuple(Vec<Annotation>),
    Function {
        argument: Box<Annotation>,
        result: Box<Annotation>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Step {
    Argument,
    Result,
    Element(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Field {
    path: Vec<Step>,
    positive: bool,
    variance_positive: bool,
    kind: &'static str,
    effects: Option<Row>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FunctionPorts {
    function_path: Vec<Step>,
    argument_effect_path: Vec<Step>,
    result_effect_path: Vec<Step>,
    argument_positive: bool,
    argument_variance_positive: bool,
    result_positive: bool,
    result_variance_positive: bool,
    // This marker belongs to the FUNCTION owner and is passed only to re.
    result_family: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Operation {
    family: usize,
    declaration: usize,
    name_position: usize,
    signature_position: usize,
    spelling: String,
    visibility: &'static str,
    range: Range<usize>,
    signature: Annotation,
    fields: Vec<Field>,
    functions: Vec<FunctionPorts>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Extraction {
    source: String,
    source_path: String,
    keys: Vec<KeyRecord>,
    families: Vec<Family>,
    operations: Vec<Operation>,
    diagnostics: Vec<Diagnostic>,
    uses: Vec<OperationUse>,
    apply_incidences: Vec<ApplyIncidence>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OperationUse {
    source_key: usize,
    definition_key: usize,
    occurrence_ordinal: u32,
    resolution: &'static str,
    operation: Option<usize>,
}

/// One exact node reached through a LocalSourceIndex in the selected carrier.
/// The occurrence ordinal is intentionally independent from `source_key`:
/// distinct HIR occurrences may share one CST key and range (notably empty
/// call Unit and Apply nodes).
#[derive(Clone, Debug, PartialEq, Eq)]
struct ApplyNodeRef {
    local_source_index: u32,
    occurrence_ordinal: u32,
    source_key: usize,
    position: usize,
    range: Range<usize>,
    form: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ApplyIncidence {
    owner_definition_source_key: usize,
    owner_local_source_index: u32,
    application: ApplyNodeRef,
    raw_callee: ApplyNodeRef,
    argument: ApplyNodeRef,
    raw_callee_group_projection: Vec<ApplyNodeRef>,
    source_form: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Diagnostic {
    kind: String,
    range: Range<usize>,
    retained_effect_placeholder: bool,
}

struct Extractor<'a> {
    hir: &'a HirModule,
    keys: Keys<'a>,
    family_ids: HashMap<SourceEffectId, usize>,
    families: Vec<Family>,
}

impl<'a> Extractor<'a> {
    fn family(&mut self, family: &SourceEffectId) -> Result<usize> {
        if family.module.as_ref() != self.hir.identity().module() {
            return Err(
                "external module identity is not authenticated by this single-module extractor"
                    .into(),
            );
        }
        let declaration = self.keys.intern(&family.declaration)?;
        if let Some(&id) = self.family_ids.get(family) {
            return Ok(id);
        }
        let id = self.families.len();
        self.family_ids.insert(family.clone(), id);
        let key = family.module.file().key();
        self.families.push(Family {
            id,
            declaration,
            realm: key.realm().into(),
            module_path: key.normalized_workspace_relative_path().into(),
        });
        Ok(id)
    }

    fn row(&mut self, row: &SourceEffectRow) -> Result<Row> {
        let position = self.keys.intern(&row.position)?;
        let concrete = row
            .concrete
            .iter()
            .map(|family| self.family(family))
            .collect::<Result<_>>()?;
        Ok(Row {
            position,
            concrete,
            variables: row.variables.iter().map(|v| v.to_string()).collect(),
        })
    }

    fn annotation(&mut self, annotation: &SourceAnnotationType) -> Result<Annotation> {
        let effects = annotation
            .effects
            .as_ref()
            .map(|row| self.row(row))
            .transpose()?;
        let value = match &annotation.value {
            SourceAnnotationValue::Unit => Value::Unit,
            SourceAnnotationValue::Int => Value::Int,
            SourceAnnotationValue::Bool => Value::Bool,
            SourceAnnotationValue::Str => Value::Str,
            SourceAnnotationValue::Variable(name) => Value::Variable(name.to_string()),
            SourceAnnotationValue::Hole(key) => Value::Hole(self.keys.intern(key)?),
            SourceAnnotationValue::Tuple(elements) => Value::Tuple(
                elements
                    .iter()
                    .map(|element| self.annotation(element))
                    .collect::<Result<_>>()?,
            ),
            SourceAnnotationValue::Function { argument, result } => Value::Function {
                argument: Box::new(self.annotation(argument)?),
                result: Box::new(self.annotation(result)?),
            },
        };
        Ok(Annotation { effects, value })
    }

    fn visit(
        &mut self,
        declaration: &SourceOperationDeclaration,
        ty: &SourceAnnotationType,
        family: usize,
        path: &mut Vec<Step>,
        positive: bool,
        variance_positive: bool,
        fields: &mut Vec<Field>,
        functions: &mut Vec<FunctionPorts>,
    ) -> Result<()> {
        let kind = match &ty.value {
            SourceAnnotationValue::Unit => "unit",
            SourceAnnotationValue::Int => "int",
            SourceAnnotationValue::Bool => "bool",
            SourceAnnotationValue::Str => "str",
            SourceAnnotationValue::Variable(_) => "variable",
            SourceAnnotationValue::Hole(_) => "hole",
            SourceAnnotationValue::Tuple(_) => "tuple",
            SourceAnnotationValue::Function { .. } => "function",
        };
        fields.push(Field {
            path: path.clone(),
            positive,
            variance_positive,
            kind,
            effects: ty.effects.as_ref().map(|row| self.row(row)).transpose()?,
        });
        match &ty.value {
            SourceAnnotationValue::Function { argument, result } => {
                let mut argument_path = path.clone();
                argument_path.push(Step::Argument);
                let mut result_path = path.clone();
                result_path.push(Step::Result);
                functions.push(FunctionPorts {
                    function_path: path.clone(),
                    argument_effect_path: argument_path,
                    result_effect_path: result_path,
                    argument_positive: !positive,
                    argument_variance_positive: !variance_positive,
                    result_positive: positive,
                    result_variance_positive: variance_positive,
                    result_family: std::ptr::eq(ty, &declaration.signature).then_some(family),
                });
                path.push(Step::Argument);
                self.visit(
                    declaration,
                    argument,
                    family,
                    path,
                    !positive,
                    !variance_positive,
                    fields,
                    functions,
                )?;
                path.pop();
                path.push(Step::Result);
                self.visit(
                    declaration,
                    result,
                    family,
                    path,
                    positive,
                    variance_positive,
                    fields,
                    functions,
                )?;
                path.pop();
            }
            SourceAnnotationValue::Tuple(elements) => {
                for (index, element) in elements.iter().enumerate() {
                    path.push(Step::Element(index));
                    self.visit(
                        declaration,
                        element,
                        family,
                        path,
                        positive,
                        variance_positive,
                        fields,
                        functions,
                    )?;
                    path.pop();
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn operation(
        &mut self,
        operation: &SourceOperationDeclaration,
        family: usize,
    ) -> Result<Operation> {
        if self.family(&operation.id.family)? != family {
            return Err("operation family differs from containing declaration".into());
        }
        let declaration = self.keys.intern(&operation.id.declaration)?;
        let name_position = self.keys.intern(&operation.name_position)?;
        let signature_position = self.keys.intern(&operation.signature_position)?;
        let signature = self.annotation(&operation.signature)?;
        let mut fields = Vec::new();
        let mut functions = Vec::new();
        self.visit(
            operation,
            &operation.signature,
            family,
            &mut Vec::new(),
            true,
            true,
            &mut fields,
            &mut functions,
        )?;
        Ok(Operation {
            family,
            declaration,
            name_position,
            signature_position,
            spelling: operation.spelling.to_string(),
            range: operation.range.clone(),
            visibility: match operation.visibility {
                HirVisibility::Private => "private",
                HirVisibility::Our => "our",
                HirVisibility::Public => "public",
            },
            signature,
            fields,
            functions,
        })
    }
}

fn source_form_name(form: &LocalSourceForm) -> &'static str {
    match form {
        LocalSourceForm::Unit => "Unit",
        LocalSourceForm::Apply { .. } => "Apply",
        LocalSourceForm::Group { .. } => "Group",
        LocalSourceForm::Lambda { .. } => "Lambda",
        LocalSourceForm::Name { .. } => "Name",
        LocalSourceForm::Primitive { .. } => "Primitive",
        LocalSourceForm::Operation { .. } => "Operation",
        LocalSourceForm::Integer(_) => "Integer",
        LocalSourceForm::Boolean(_) => "Boolean",
        LocalSourceForm::String(_) => "String",
        LocalSourceForm::DecodedString(_) => "DecodedString",
        LocalSourceForm::InterpolatedString { .. } => "InterpolatedString",
        LocalSourceForm::Catch { .. } => "Catch",
        LocalSourceForm::Case { .. } => "Case",
        LocalSourceForm::If { .. } => "If",
        LocalSourceForm::Sequence { .. } => "Sequence",
        LocalSourceForm::StatementBlock { .. } => "StatementBlock",
        LocalSourceForm::Tuple { .. } => "Tuple",
        LocalSourceForm::Record { .. } => "Record",
        LocalSourceForm::Variant { .. } => "Variant",
        LocalSourceForm::FieldTail { .. } => "FieldTail",
        LocalSourceForm::GeneratedFormatSelection { .. } => "GeneratedFormatSelection",
        LocalSourceForm::OperatorApplication { .. } => "OperatorApplication",
        LocalSourceForm::Ascription { .. } => "Ascription",
        LocalSourceForm::Block { .. } => "Block",
    }
}

fn apply_node_ref(
    source: &LocalSource,
    hir: &HirModule,
    keys: &mut Keys<'_>,
    index: &LocalSourceIndex,
) -> Result<ApplyNodeRef> {
    if index.source_root() != source.source_root() {
        return Err("Apply child index belongs to a foreign LocalSource root".into());
    }
    let expression = source
        .expression(index)
        .ok_or("Apply child index is absent from selected LocalSource")?;
    if !hir.owns_occurrence(&expression.occurrence)
        || hir
            .occurrence_source_key(&expression.occurrence)
            .map_err(|error| format!("Apply child occurrence lookup failed: {error:?}"))?
            != Some(&expression.source)
    {
        return Err("Apply child occurrence/source key is not joined in selected HIR".into());
    }
    let source_key = keys.intern(&expression.source)?;
    let key_record = keys
        .records
        .get(source_key)
        .ok_or("interned Apply child source key has no record")?;
    if key_record.range != expression.range {
        return Err("Apply child LocalSource and source-key ranges differ".into());
    }
    Ok(ApplyNodeRef {
        local_source_index: index.ordinal(),
        occurrence_ordinal: expression.occurrence.ordinal(),
        source_key,
        position: key_record.position,
        range: expression.range.clone(),
        form: source_form_name(&expression.form).into(),
    })
}

fn collect_apply_incidences(hir: &HirModule, keys: &mut Keys<'_>) -> Result<Vec<ApplyIncidence>> {
    let mut incidences = Vec::new();
    for item in hir.items() {
        let HirItem::Binding(binding) = item else {
            continue;
        };
        let Some(source) = hir
            .local_source(binding.definition_root())
            .map_err(|error| format!("Apply LocalSource lookup failed: {error:?}"))?
        else {
            continue;
        };
        if source.definition_root() != Some(binding.definition_root()) {
            return Err("Apply LocalSource has a different definition owner".into());
        }
        let owner_definition_source_key = keys.intern(
            hir.definition_source_key(binding.definition_root())
                .map_err(|error| format!("Apply owner definition lookup failed: {error:?}"))?
                .ok_or("Apply owner definition has no source key")?,
        )?;
        let owner_local_source_index = source.body().ordinal();
        // LocalSourceIndex ordinals are the positions in `expressions`; each
        // actual child edge below is still followed through its branded index.
        for (ordinal, application_expr) in source.expressions().iter().enumerate() {
            let LocalSourceForm::Apply {
                callee,
                argument,
                source_form,
            } = &application_expr.form
            else {
                continue;
            };
            if !hir.owns_occurrence(&application_expr.occurrence)
                || hir
                    .occurrence_source_key(&application_expr.occurrence)
                    .map_err(|error| format!("Apply occurrence lookup failed: {error:?}"))?
                    != Some(&application_expr.source)
            {
                return Err(
                    "Apply parent occurrence/source key is not joined in selected HIR".into(),
                );
            }
            let application_key = keys.intern(&application_expr.source)?;
            let application_key_record = &keys.records[application_key];
            if application_key_record.range != application_expr.range {
                return Err("Apply parent LocalSource and source-key ranges differ".into());
            }
            let application = ApplyNodeRef {
                local_source_index: u32::try_from(ordinal)
                    .map_err(|_| "Apply LocalSource index exceeds u32")?,
                occurrence_ordinal: application_expr.occurrence.ordinal(),
                source_key: application_key,
                position: application_key_record.position,
                range: application_expr.range.clone(),
                form: "Apply".into(),
            };
            let raw_callee = apply_node_ref(source, hir, keys, callee)?;
            let argument = apply_node_ref(source, hir, keys, argument)?;
            let mut raw_callee_group_projection = Vec::new();
            let mut projection_index = callee.clone();
            loop {
                let projection = source
                    .expression(&projection_index)
                    .ok_or("raw callee Group projection is absent from LocalSource")?;
                let LocalSourceForm::Group { inner } = &projection.form else {
                    break;
                };
                projection_index = inner.clone();
                raw_callee_group_projection.push(apply_node_ref(
                    source,
                    hir,
                    keys,
                    &projection_index,
                )?);
            }
            incidences.push(ApplyIncidence {
                owner_definition_source_key,
                owner_local_source_index,
                application,
                raw_callee,
                argument,
                raw_callee_group_projection,
                source_form: format!("{source_form:?}"),
            });
        }
    }
    Ok(incidences)
}

fn parse(text: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(text);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn extract(text: &str, source_path: &str) -> Result<Extraction> {
    let parsed = parse(text);
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "source-signature-r300",
            source_path,
        ))),
        &parsed,
        SemanticImports::empty(),
    )
    .map_err(|error| format!("HIR formation failed: {error:?}"))?;
    let artifact = ShadowArtifact::from_parsed(parsed.clone())
        .map_err(|error| format!("shadow source index failed: {error:?}"))?;
    let mut extractor = Extractor {
        hir: &hir,
        keys: Keys::new(&parsed, &artifact),
        family_ids: HashMap::new(),
        families: Vec::new(),
    };
    // Intern in declaration order, including unused/forward-declared families.
    for family in hir.source_effect_declarations() {
        extractor.family(&family.id)?;
    }
    let mut operations = Vec::new();
    for family in hir.source_effect_declarations() {
        let id = extractor.family(&family.id)?;
        for operation in &family.operations {
            operations.push(extractor.operation(operation, id)?);
        }
    }
    let declarations = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|family| family.operations.iter())
        .collect::<Vec<_>>();
    let mut uses = Vec::new();
    for item in hir.items() {
        let HirItem::Binding(binding) = item else {
            continue;
        };
        let Some(source) = hir
            .local_source(binding.definition_root())
            .map_err(|error| format!("local source lookup failed: {error:?}"))?
        else {
            continue;
        };
        for expression in source.expressions() {
            let LocalSourceForm::Operation { resolution } = &expression.form else {
                continue;
            };
            if !hir.owns_occurrence(&expression.occurrence)
                || hir
                    .occurrence_source_key(&expression.occurrence)
                    .map_err(|error| format!("occurrence source lookup failed: {error:?}"))?
                    != Some(&expression.source)
            {
                return Err(
                    "operation use occurrence is not owned by the selected HIR/source".into(),
                );
            }
            let source_key = extractor.keys.intern(&expression.source)?;
            if extractor.keys.records[source_key].range != expression.range {
                return Err("operation use and parser source ranges differ".into());
            }
            let definition_key = extractor.keys.intern(
                hir.definition_source_key(binding.definition_root())
                    .map_err(|error| format!("definition source lookup failed: {error:?}"))?
                    .ok_or("missing definition source key")?,
            )?;
            let (resolution, operation) = match resolution {
                SourceOperationResolution::Resolved(resolved) => {
                    let index = declarations
                        .iter()
                        .position(|decl| Arc::ptr_eq(decl, resolved))
                        .ok_or(
                            "resolved operation Arc is absent from the selected declaration table",
                        )?;
                    if declarations[index].id != resolved.id {
                        return Err("operation identity mismatch".into());
                    }
                    ("resolved_same_arc_as_table", Some(index))
                }
                SourceOperationResolution::Unresolved => ("unresolved", None),
                SourceOperationResolution::Ambiguous => ("ambiguous", None),
                SourceOperationResolution::Private => ("private", None),
            };
            uses.push(OperationUse {
                source_key,
                definition_key,
                occurrence_ordinal: expression.occurrence.ordinal(),
                resolution,
                operation,
            });
        }
    }
    let apply_incidences = collect_apply_incidences(&hir, &mut extractor.keys)?;
    let diagnostics = hir
        .errors()
        .iter()
        .map(|error| Diagnostic {
            kind: format!("{:?}", error.kind()),
            range: error.range().clone(),
            retained_effect_placeholder: hir
                .source_effect_declarations()
                .iter()
                .any(|family| family.placeholder_errors.contains(&error.id())),
        })
        .collect();
    Ok(Extraction {
        source: text.into(),
        source_path: source_path.into(),
        keys: extractor.keys.records,
        families: extractor.families,
        operations,
        diagnostics,
        uses,
        apply_incidences,
    })
}

fn quoted(value: &str) -> String {
    let mut result = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c <= '\u{1f}' => write!(result, "\\u{:04x}", c as u32).unwrap(),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}
fn array<T>(items: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", items.iter().map(f).collect::<Vec<_>>().join(","))
}
fn optional<T>(value: &Option<T>, f: impl Fn(&T) -> String) -> String {
    value.as_ref().map(f).unwrap_or_else(|| "null".into())
}
fn json_apply_node_ref(node: &ApplyNodeRef) -> String {
    format!(
        "{{\"local_source_index\":{},\"occurrence_ordinal\":{},\"source_key_id\":{},\"source_position_ordinal\":{},\"byte_range\":[{},{}],\"source_form\":{}}}",
        node.local_source_index,
        node.occurrence_ordinal,
        node.source_key,
        node.position,
        node.range.start,
        node.range.end,
        quoted(&node.form)
    )
}
fn json_path(path: &[Step]) -> String {
    array(path, |step| match step {
        Step::Argument => quoted("argument"),
        Step::Result => quoted("result"),
        Step::Element(i) => format!("{{\"element\":{i}}}"),
    })
}
fn json_row(row: &Row) -> String {
    format!(
        "{{\"position_key\":{},\"concrete_family_ids\":{},\"variables\":{}}}",
        row.position,
        array(&row.concrete, |v| v.to_string()),
        array(&row.variables, |v| quoted(v))
    )
}
fn json_annotation(a: &Annotation) -> String {
    let (kind, details) = match &a.value {
        Value::Unit => ("unit", String::new()),
        Value::Int => ("int", String::new()),
        Value::Bool => ("bool", String::new()),
        Value::Str => ("str", String::new()),
        Value::Variable(name) => ("variable", format!(",\"name\":{}", quoted(name))),
        Value::Hole(key) => ("hole", format!(",\"position_key\":{key}")),
        Value::Tuple(elements) => (
            "tuple",
            format!(",\"elements\":{}", array(elements, json_annotation)),
        ),
        Value::Function { argument, result } => (
            "function",
            format!(
                ",\"argument\":{},\"result\":{}",
                json_annotation(argument),
                json_annotation(result)
            ),
        ),
    };
    format!(
        "{{\"kind\":{},\"effects\":{}{details}}}",
        quoted(kind),
        optional(&a.effects, json_row)
    )
}

impl Extraction {
    fn json(&self) -> String {
        let keys = array(&self.keys, |k| {
            format!(
                "{{\"id\":{},\"position_ordinal\":{},\"byte_range\":[{},{}],\"syntax_kind\":{}}}",
                k.id,
                k.position,
                k.range.start,
                k.range.end,
                quoted(&k.kind)
            )
        });
        let families = array(&self.families, |f| {
            format!(
                "{{\"id\":{},\"declaration_key\":{},\"module_realm\":{},\"module_path\":{}}}",
                f.id,
                f.declaration,
                quoted(&f.realm),
                quoted(&f.module_path)
            )
        });
        let diagnostics = array(&self.diagnostics, |d| {
            format!(
                "{{\"kind\":{},\"byte_range\":[{},{}],\"retained_effect_placeholder\":{}}}",
                quoted(&d.kind),
                d.range.start,
                d.range.end,
                d.retained_effect_placeholder
            )
        });
        let uses = array(&self.uses, |u| {
            format!(
                "{{\"source_key\":{},\"definition_key\":{},\"occurrence_ordinal\":{},\"resolution\":{},\"operation_index\":{}}}",
                u.source_key,
                u.definition_key,
                u.occurrence_ordinal,
                quoted(u.resolution),
                optional(&u.operation, |v| v.to_string())
            )
        });
        let apply_incidences = array(&self.apply_incidences, |row| {
            format!(
                "{{\"owner_definition_source_key_id\":{},\"owner_local_source_index\":{},\"application\":{},\"raw_callee\":{},\"argument\":{},\"raw_callee_group_projection\":{},\"apply_source_form\":{}}}",
                row.owner_definition_source_key,
                row.owner_local_source_index,
                json_apply_node_ref(&row.application),
                json_apply_node_ref(&row.raw_callee),
                json_apply_node_ref(&row.argument),
                array(&row.raw_callee_group_projection, json_apply_node_ref),
                quoted(&row.source_form)
            )
        });
        let operations = array(&self.operations, |o| {
            let fields = array(&o.fields, |f| {
                format!(
                    "{{\"path\":{},\"kind\":{},\"positive\":{},\"variance_positive\":{},\"effects\":{}}}",
                    json_path(&f.path),
                    quoted(f.kind),
                    f.positive,
                    f.variance_positive,
                    optional(&f.effects, json_row)
                )
            });
            let functions = array(&o.functions, |f| {
                format!(
                    "{{\"function_owner_path\":{},\"argument_effect_path\":{},\"result_effect_path\":{},\"argument_positive\":{},\"argument_variance_positive\":{},\"result_positive\":{},\"result_variance_positive\":{},\"result_family\":{}}}",
                    json_path(&f.function_path),
                    json_path(&f.argument_effect_path),
                    json_path(&f.result_effect_path),
                    f.argument_positive,
                    f.argument_variance_positive,
                    f.result_positive,
                    f.result_variance_positive,
                    optional(&f.result_family, |v| v.to_string())
                )
            });
            format!(
                "{{\"family_id\":{},\"declaration_key\":{},\"name_position_key\":{},\"signature_position_key\":{},\"spelling\":{},\"visibility\":{},\"byte_range\":[{},{}],\"signature\":{},\"fields\":{},\"function_ports\":{}}}",
                o.family,
                o.declaration,
                o.name_position,
                o.signature_position,
                quoted(&o.spelling),
                quoted(o.visibility),
                o.range.start,
                o.range.end,
                json_annotation(&o.signature),
                fields,
                functions
            )
        });
        format!(
            "{{\"schema_version\":1,\"claim\":\"finite authentic HIR extraction; no Rust-Lean equivalence or original semantic proof\",\"identity_scope\":\"single execution and selected parse; IDs intern complete native Eq identities; locators are not identity\",\"solver_preflight\":\"not run; retained HIR includes tuples and holes unsupported by operation inference\",\"use_scope\":\"LocalSourceForm::Operation expressions in top-level binding carriers; catch patterns are outside this inventory\",\"source_path\":{},\"source\":{},\"keys\":{keys},\"families\":{families},\"operations\":{operations},\"operation_uses\":{uses},\"apply_incidences\":{apply_incidences},\"hir_diagnostics\":{diagnostics}}}\n",
            quoted(&self.source_path),
            quoted(&self.source)
        )
    }

    fn lean(&self) -> String {
        let mut out = String::from(
            "import YulangClosure.SourceSignatureRealizationR300\n\n/- Generated finite HIR extraction. IDs have only artifact-local native identity.\nNo Rust/Lean equivalence, solver acceptance, IF or R159 proof is asserted.\nUse the default JSON output for identity locators and original HIR diagnostics. -/\nnamespace YulangClosure.SourceSignatureExtractionR300\nopen PrimitiveOperation SourceSignatureRealizationR300\n",
        );
        // Same-run metadata keeps the identity table and original diagnostics
        // beside the data. Comparing numbers from separate runs is not identity.
        writeln!(
            out,
            "def extractionJson : String := {}",
            lean_string(&self.json())
        )
        .unwrap();
        for (i, operation) in self.operations.iter().enumerate() {
            writeln!(
                out,
                "def signature{i} : Signature Nat Nat := {}",
                lean_annotation(&operation.signature)
            )
            .unwrap();
        }
        out.push_str(
            "structure ApplyNodeRef where\n  localSourceIndex : Nat\n  occurrenceOrdinal : Nat\n  sourceKeyId : Nat\n  sourcePositionOrdinal : Nat\n  byteRange : Nat × Nat\n  sourceForm : String\n  deriving DecidableEq, Repr\n\nstructure ApplyOccurrenceRow where\n  ownerDefinitionSourceKeyId : Nat\n  ownerLocalSourceIndex : Nat\n  application : ApplyNodeRef\n  rawCallee : ApplyNodeRef\n  argument : ApplyNodeRef\n  rawCalleeGroupProjection : List ApplyNodeRef\n  applySourceForm : String\n  deriving DecidableEq, Repr\n\n",
        );
        writeln!(
            out,
            "def applyIncidences : List ApplyOccurrenceRow := {}",
            array(&self.apply_incidences, lean_apply_incidence)
        )
        .unwrap();
        out.push_str("end YulangClosure.SourceSignatureExtractionR300\n");
        out
    }
}

fn lean_row(row: &Row) -> String {
    format!(
        "{{ position := {}, concrete := {}, variables := {} }}",
        row.position,
        array(&row.concrete, |v| v.to_string()),
        array(&row.variables, |v| lean_string(v))
    )
}
fn lean_string(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c <= '\u{1f}' => write!(out, "\\u{{{:x}}}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn lean_apply_node_ref(node: &ApplyNodeRef) -> String {
    format!(
        "{{ localSourceIndex := {}, occurrenceOrdinal := {}, sourceKeyId := {}, sourcePositionOrdinal := {}, byteRange := ({}, {}), sourceForm := {} }}",
        node.local_source_index,
        node.occurrence_ordinal,
        node.source_key,
        node.position,
        node.range.start,
        node.range.end,
        lean_string(&node.form)
    )
}
fn lean_apply_incidence(row: &ApplyIncidence) -> String {
    format!(
        "{{ ownerDefinitionSourceKeyId := {}, ownerLocalSourceIndex := {}, application := {}, rawCallee := {}, argument := {}, rawCalleeGroupProjection := {}, applySourceForm := {} }}",
        row.owner_definition_source_key,
        row.owner_local_source_index,
        lean_apply_node_ref(&row.application),
        lean_apply_node_ref(&row.raw_callee),
        lean_apply_node_ref(&row.argument),
        array(&row.raw_callee_group_projection, lean_apply_node_ref),
        lean_string(&row.source_form)
    )
}
fn lean_annotation(a: &Annotation) -> String {
    let row = a
        .effects
        .as_ref()
        .map(|r| format!("(some {})", lean_row(r)))
        .unwrap_or_else(|| "none".into());
    match &a.value {
        Value::Unit => format!("(.primitive {row} .unit)"),
        Value::Int => format!("(.primitive {row} .int)"),
        Value::Bool => format!("(.primitive {row} .bool)"),
        Value::Str => format!("(.primitive {row} .string)"),
        Value::Variable(name) => format!("(.variable {row} {})", lean_string(name)),
        Value::Hole(key) => format!("(.hole {row} {key})"),
        Value::Tuple(elements) => format!("(.tuple {row} {})", array(elements, lean_annotation)),
        Value::Function { argument, result } => format!(
            "(.function {row} {} {})",
            lean_annotation(argument),
            lean_annotation(result)
        ),
    }
}

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let first = arguments
        .next()
        .ok_or("usage: source_signature_r300 [--lean] INPUT.yu")?;
    let (lean, path) = if first == "--lean" {
        (true, arguments.next().ok_or("missing INPUT.yu")?)
    } else {
        (false, first)
    };
    if arguments.next().is_some() {
        return Err("unexpected extra argument".into());
    }
    let path = Path::new(&path).canonicalize()?;
    let text = std::fs::read_to_string(&path)?;
    let source_path = path
        .to_str()
        .ok_or("input path must be UTF-8; lossy identity conversion is rejected")?;
    let extraction = extract(&text, source_path).map_err(std::io::Error::other)?;
    print!(
        "{}",
        if lean {
            extraction.lean()
        } else {
            extraction.json()
        }
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn operation<'a>(e: &'a Extraction, name: &str) -> &'a Operation {
        e.operations
            .iter()
            .find(|o| o.spelling == name)
            .expect("retained operation")
    }

    #[test]
    fn native_key_interning_rejects_foreign_parse_and_preserves_exact_reuse() {
        let text = "act E:\n    our op: () -> int\n";
        let selected = parse(text);
        let foreign = parse(text);
        let artifact = ShadowArtifact::from_parsed(selected.clone()).unwrap();
        let key = selected.source_root().key();
        let foreign_key = foreign.source_root().key();
        let mut keys = Keys::new(&selected, &artifact);
        let id = keys.intern(&key).unwrap();
        assert_eq!(keys.intern(&key.clone()).unwrap(), id);
        assert_eq!(keys.records.len(), 1);
        assert!(keys.intern(&foreign_key).is_err());
        assert_eq!(keys.records.len(), 1);
    }

    #[test]
    fn nested_callable_result_routes_family_to_only_root_result_port() {
        let e = extract("act E:\n    our op: () -> (() -> [E]int)\n", "nested.yu").unwrap();
        let o = operation(&e, "op");
        assert_eq!(o.functions.len(), 2);
        assert_eq!(o.functions[0].function_path, vec![]);
        assert_eq!(o.functions[0].result_effect_path, vec![Step::Result]);
        assert_eq!(o.functions[0].result_family, Some(o.family));
        assert_eq!(o.functions[1].function_path, vec![Step::Result]);
        assert_eq!(o.functions[1].result_family, None);
        let field = o
            .fields
            .iter()
            .find(|f| f.path == [Step::Result, Step::Argument])
            .unwrap();
        assert!(!field.positive && !field.variance_positive);
        let result = o
            .fields
            .iter()
            .find(|f| f.path == [Step::Result, Step::Result])
            .unwrap();
        assert_eq!(result.effects.as_ref().unwrap().concrete, vec![o.family]);
    }

    #[test]
    fn retains_omission_empty_order_duplicates_tail_variables_holes_and_tuples() {
        let text = "act E:\n    our omitted: () -> int\n    our empty: () -> []int\n    our rich: ('a, _) -> [F, E, F, 'e]('a -> [E]int)\nact F;\n";
        let e = extract(text, "rich.yu").unwrap();
        let omitted = operation(&e, "omitted");
        let empty = operation(&e, "empty");
        assert!(
            omitted
                .fields
                .iter()
                .find(|f| f.path == [Step::Result])
                .unwrap()
                .effects
                .is_none()
        );
        let empty_row = empty
            .fields
            .iter()
            .find(|f| f.path == [Step::Result])
            .unwrap()
            .effects
            .as_ref()
            .unwrap();
        assert!(empty_row.concrete.is_empty() && empty_row.variables.is_empty());
        let rich = operation(&e, "rich");
        let row = rich
            .fields
            .iter()
            .find(|f| f.path == [Step::Result])
            .unwrap()
            .effects
            .as_ref()
            .unwrap();
        assert_eq!(row.concrete, vec![1, 0, 1]);
        assert_eq!(row.variables, vec!["'e"]);
        let Value::Function { argument, result } = &rich.signature.value else {
            panic!()
        };
        let Value::Tuple(elements) = &argument.value else {
            panic!()
        };
        assert!(matches!(elements[0].value, Value::Variable(ref name) if name == "'a"));
        assert!(matches!(elements[1].value, Value::Hole(_)));
        assert!(matches!(result.value, Value::Function { .. }));
        assert!(
            rich.fields
                .iter()
                .any(|f| f.path == [Step::Argument, Step::Element(1)] && f.kind == "hole")
        );
    }

    #[test]
    fn repeated_spellings_keep_distinct_declarations_and_positions() {
        let e = extract(
            "act E:\n    our op: _ -> _\nact F:\n    our op: _ -> _\n",
            "same.yu",
        )
        .unwrap();
        assert_eq!(e.operations.len(), 2);
        assert_ne!(e.operations[0].family, e.operations[1].family);
        assert_ne!(e.operations[0].declaration, e.operations[1].declaration);
        let holes = e
            .operations
            .iter()
            .flat_map(|o| match &o.signature.value {
                Value::Function { argument, result } => vec![&argument.value, &result.value],
                _ => vec![],
            })
            .map(|v| match v {
                Value::Hole(id) => *id,
                _ => panic!(),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            holes.iter().collect::<std::collections::HashSet<_>>().len(),
            4
        );
    }

    #[test]
    fn json_and_lean_export_preserve_control_characters_and_full_tree() {
        let e = extract("act E:\n    our op: 'a -> ('a -> int)\n", "sample.yu").unwrap();
        assert!(e.json().contains("\"source\":\"act E:\\n"));
        assert!(e.json().contains("\"solver_preflight\":\"not run"));
        assert!(
            e.lean()
                .contains("(.function none (.variable none \"'a\") (.function")
        );
        assert!(e.lean().contains("def extractionJson : String"));
        assert_eq!(quoted("a\n\t\"\\\u{0}"), "\"a\\n\\t\\\"\\\\\\u0000\"");
    }

    #[test]
    fn preserves_diagnostics_and_rejects_unformed_effect_rows() {
        let e = extract("act E:\n    our op: () -> int\n", "diagnostic.yu").unwrap();
        assert!(!e.diagnostics.is_empty());
        assert!(
            e.diagnostics
                .iter()
                .any(|d| d.kind == "UnsupportedItem" && d.retained_effect_placeholder)
        );
        assert!(e.json().contains("\"hir_diagnostics\":["));
        assert!(extract("act E:\n    our op: () -> [missing]int\n", "missing.yu").is_err());
        assert!(extract("act E:\n    our op: () -> ['a, 'b]int\n", "tails.yu").is_err());
    }

    #[test]
    fn authentic_operation_use_joins_exact_table_arc_and_preserves_failure() {
        let text =
            "act E:\n    our op: () -> (() -> int)\nmy lookup = E::op\nmy bad = E::missing\n";
        let e = extract(text, "use.yu").unwrap();
        assert_eq!(e.uses.len(), 2);
        let resolved = e.uses.iter().find(|u| u.operation == Some(0)).unwrap();
        assert_eq!(resolved.resolution, "resolved_same_arc_as_table");
        assert_ne!(resolved.source_key, e.operations[0].declaration);
        assert_ne!(resolved.source_key, e.operations[0].signature_position);
        assert!(
            e.uses
                .iter()
                .any(|u| u.operation.is_none() && u.resolution == "unresolved")
        );
    }

    #[test]
    fn apply_incidence_authenticates_nested_children_and_is_deterministic() {
        let text = "my value f = f() (f())";
        let first = extract(text, "nested-apply.yu").unwrap();
        let second = extract(text, "nested-apply.yu").unwrap();
        assert_eq!(first.apply_incidences, second.apply_incidences);
        assert_eq!(first.json(), second.json());
        assert_eq!(first.lean(), second.lean());
        assert_eq!(first.apply_incidences.len(), 3);
        let outer = first
            .apply_incidences
            .iter()
            .find(|row| row.raw_callee.form == "Apply" && row.argument.form == "Group")
            .expect("outer application row");
        let inner = first
            .apply_incidences
            .iter()
            .find(|row| {
                row.application.range != outer.application.range
                    && row.application.range.start >= outer.argument.range.start
                    && row.application.range.end <= outer.argument.range.end
            })
            .expect("nested application row");
        assert_eq!(outer.argument.form, "Group");
        assert_eq!(outer.raw_callee.form, "Apply");
        assert_eq!(inner.application.form, "Apply");
        assert_eq!(
            outer.owner_definition_source_key,
            inner.owner_definition_source_key
        );
        assert!(
            first
                .lean()
                .contains("def applyIncidences : List ApplyOccurrenceRow")
        );
        assert!(first.json().contains("\"apply_incidences\":["));
    }

    #[test]
    fn empty_call_keeps_apply_and_unit_occurrences_distinct_at_one_source_key() {
        let e = extract("my invoke f = f()", "empty-apply.yu").unwrap();
        let row = e.apply_incidences.first().expect("authentic Apply row");
        assert_eq!(row.source_form, "CallTail");
        assert_eq!(row.argument.form, "Unit");
        assert_eq!(row.application.source_key, row.argument.source_key);
        assert_eq!(row.application.position, row.argument.position);
        assert_eq!(row.application.range, row.argument.range);
        assert_ne!(
            row.application.occurrence_ordinal,
            row.argument.occurrence_ordinal
        );
        assert_ne!(
            row.application.local_source_index,
            row.argument.local_source_index
        );
    }

    #[test]
    fn fixed_owner_reification_apply_fixture_has_real_group_and_both_children() {
        let e = extract("my value = \\x -> { (\\x -> x) x; x }", "owner-apply.yu").unwrap();
        let row = e.apply_incidences.first().expect("owner-fixture Apply row");
        assert_eq!(row.raw_callee.form, "Group");
        assert_eq!(row.raw_callee_group_projection.len(), 1);
        assert_eq!(row.raw_callee_group_projection[0].form, "Lambda");
        assert_eq!(row.argument.form, "Name");
        assert_ne!(
            row.raw_callee.local_source_index,
            row.raw_callee_group_projection[0].local_source_index
        );
        assert_ne!(
            row.application.occurrence_ordinal,
            row.argument.occurrence_ordinal
        );
    }

    #[test]
    fn multiple_group_projection_preserves_each_inner_edge_in_order() {
        let e = extract("my value f = (((f))) x", "multi-group-apply.yu").unwrap();
        let row = e.apply_incidences.first().expect("authentic Apply row");
        assert_eq!(row.raw_callee.form, "Group");
        assert_eq!(
            row.raw_callee_group_projection
                .iter()
                .map(|node| node.form.as_str())
                .collect::<Vec<_>>(),
            ["Group", "Group", "Name"]
        );
        assert_eq!(
            row.raw_callee_group_projection
                .iter()
                .map(|node| node.local_source_index)
                .collect::<Vec<_>>(),
            [4, 5, 6]
        );
        assert_ne!(
            row.raw_callee.local_source_index,
            row.raw_callee_group_projection[0].local_source_index
        );
    }

    #[test]
    fn two_definition_owners_can_reuse_local_index_without_sharing_owner() {
        let e = extract("my one f = f(); my two g = g()", "two-owner-apply.yu").unwrap();
        assert_eq!(e.apply_incidences.len(), 2);
        let [first, second] = e.apply_incidences.as_slice() else {
            panic!("expected one Apply from each binding owner");
        };
        assert_eq!(
            first.application.local_source_index,
            second.application.local_source_index
        );
        assert_eq!(
            first.owner_local_source_index,
            second.owner_local_source_index
        );
        assert_ne!(
            first.owner_definition_source_key,
            second.owner_definition_source_key
        );
        assert_ne!(
            first.application.occurrence_ordinal,
            second.application.occurrence_ordinal
        );
        assert_ne!(first.application.source_key, second.application.source_key);
    }
}
