use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    ops::Range,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use yu_syntax::{
    ParsedFile, SourceRevision, StructuralRecovery, StructuralRecoveryKind, SyntaxKind, SyntaxNode,
};

use crate::{AssociationError, HirExpr, associate_chain_owned, range_of};

/// A compiler-supplied, already-normalized file key.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FileKey {
    realm: Box<str>,
    normalized_workspace_relative_path: Box<str>,
}

impl FileKey {
    pub fn new(
        realm: impl Into<Box<str>>,
        normalized_workspace_relative_path: impl Into<Box<str>>,
    ) -> Self {
        Self {
            realm: realm.into(),
            normalized_workspace_relative_path: normalized_workspace_relative_path.into(),
        }
    }

    pub fn realm(&self) -> &str {
        &self.realm
    }

    pub fn normalized_workspace_relative_path(&self) -> &str {
        &self.normalized_workspace_relative_path
    }
}

/// Collision-safe identity for one compiler-supplied file key.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FileId(FileKey);

impl FileId {
    pub fn new(key: FileKey) -> Self {
        Self(key)
    }

    pub fn key(&self) -> &FileKey {
        &self.0
    }
}

/// The only module identity supported by this standalone slice.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ModuleId {
    SourceRoot(FileId),
}

impl ModuleId {
    pub fn source_root(file: FileId) -> Self {
        Self::SourceRoot(file)
    }

    pub fn file(&self) -> &FileId {
        match self {
            Self::SourceRoot(file) => file,
        }
    }
}

/// Compiler-owned module identity supplied to HIR lowering.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModuleIdentity {
    file: FileId,
    module: ModuleId,
}

impl ModuleIdentity {
    pub fn new(file: FileId, module: ModuleId) -> Self {
        Self { file, module }
    }

    pub fn source_root(file: FileId) -> Self {
        Self {
            module: ModuleId::source_root(file.clone()),
            file,
        }
    }

    pub fn file(&self) -> &FileId {
        &self.file
    }

    pub fn module(&self) -> &ModuleId {
        &self.module
    }
}

/// An opaque standalone import input. Imports are intentionally unavailable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticImports(());

impl SemanticImports {
    pub fn empty() -> Self {
        Self(())
    }
}

/// A stable definition identity within one source-root module.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DefId {
    module: ModuleId,
    spelling: Box<str>,
    same_name_ordinal: u32,
}

impl DefId {
    pub fn module(&self) -> &ModuleId {
        &self.module
    }

    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn same_name_ordinal(&self) -> u32 {
        self.same_name_ordinal
    }

    /// Returns the dynamic identity payload bytes that this `DefId`'s derived
    /// `Hash` and equality may scan.
    ///
    /// This includes the definition spelling plus the source-root module
    /// file-key realm and normalized workspace-relative path. It excludes
    /// fixed-size enum discriminants, string length metadata, pointer and
    /// container storage, and `same_name_ordinal`: those values participate in
    /// the derived operations but do not add a variable-length identity payload
    /// to scan.
    pub fn hash_eq_payload_bytes(&self) -> usize {
        let file_key = self.module.file().key();
        self.spelling.len()
            + file_key.realm().len()
            + file_key.normalized_workspace_relative_path().len()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HirErrorId(u32);

impl HirErrorId {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HirDiagnosticId(u32);

impl HirDiagnosticId {
    pub fn index(self) -> u32 {
        self.0
    }
}

/// A lowering-order expression identity branded by its immutable HIR artifact.
///
/// The token is intentionally private and non-serializable. An ordinal is only
/// meaningful alongside this token, so independently lowered modules cannot
/// accidentally use each other's occurrence zero.
#[derive(Clone)]
pub struct HirOccurrenceId {
    artifact: Arc<HirArtifactToken>,
    ordinal: u32,
}

/// An admitted definition identity branded by the immutable HIR artifact that
/// owns it. The definition payload is shared with its binding so copying a
/// root never copies a `DefId` payload.
#[derive(Clone)]
pub struct DefinitionRootId {
    artifact: Arc<HirArtifactToken>,
    definition: Arc<DefId>,
}

impl DefinitionRootId {
    fn new(artifact: Arc<HirArtifactToken>, definition: Arc<DefId>) -> Self {
        Self {
            artifact,
            definition,
        }
    }
}

impl std::fmt::Debug for DefinitionRootId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DefinitionRootId")
            .finish_non_exhaustive()
    }
}

impl PartialEq for DefinitionRootId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.definition == other.definition
    }
}

impl Eq for DefinitionRootId {}

impl Hash for DefinitionRootId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.definition.hash(state);
    }
}

/// An ordered parameter identity branded by the immutable HIR artifact that
/// owns its definition root.
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let _ = HirParameterId { owner: todo!(), ordinal: 0 };
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// fn requires_copy<T: Copy>() {}
/// requires_copy::<HirParameterId>();
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// fn requires_serialize<T: serde::Serialize>() {}
/// requires_serialize::<HirParameterId>();
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let _ = HirParameterId::new(todo!(), 0);
/// ```
///
/// ```compile_fail
/// use yu_hir::HirParameterId;
/// let left: HirParameterId = todo!();
/// let right: HirParameterId = todo!();
/// let _ = left < right;
/// ```
#[derive(Clone)]
pub struct HirParameterId {
    owner: DefinitionRootId,
    ordinal: u32,
}

impl HirParameterId {
    fn new(owner: DefinitionRootId, ordinal: u32) -> Self {
        Self { owner, ordinal }
    }

    pub fn definition_root(&self) -> &DefinitionRootId {
        &self.owner
    }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

impl std::fmt::Debug for HirParameterId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HirParameterId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

impl PartialEq for HirParameterId {
    fn eq(&self, other: &Self) -> bool {
        self.owner == other.owner && self.ordinal == other.ordinal
    }
}

impl Eq for HirParameterId {}

impl Hash for HirParameterId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.owner.hash(state);
        self.ordinal.hash(state);
    }
}

impl HirOccurrenceId {
    fn new(artifact: Arc<HirArtifactToken>, ordinal: u32) -> Self {
        Self { artifact, ordinal }
    }

    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}

impl std::fmt::Debug for HirOccurrenceId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HirOccurrenceId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

impl PartialEq for HirOccurrenceId {
    fn eq(&self, other: &Self) -> bool {
        self.ordinal == other.ordinal && Arc::ptr_eq(&self.artifact, &other.artifact)
    }
}

impl Eq for HirOccurrenceId {}

impl Hash for HirOccurrenceId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.ordinal.hash(state);
    }
}

#[derive(Debug)]
struct HirArtifactToken {
    _serial: u64,
}

static NEXT_HIR_ARTIFACT: AtomicU64 = AtomicU64::new(0);

fn mint_artifact_token() -> Arc<HirArtifactToken> {
    Arc::new(HirArtifactToken {
        _serial: NEXT_HIR_ARTIFACT.fetch_add(1, Ordering::Relaxed),
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirName {
    spelling: String,
    range: Range<usize>,
}

impl HirName {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Debug)]
pub struct HirParameter {
    id: HirParameterId,
    name: HirName,
    range: Range<usize>,
}

impl HirParameter {
    pub fn id(&self) -> &HirParameterId {
        &self.id
    }

    pub fn name(&self) -> &HirName {
        &self.name
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

impl PartialEq for HirParameter {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.range == other.range
    }
}

impl Eq for HirParameter {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirVisibility {
    Private,
    Our,
    Public,
}

#[derive(Clone, Debug)]
pub enum NameResolution {
    Resolved(DefId),
    Parameter(HirParameterId),
    Ambiguous,
    Unresolved,
}

impl PartialEq for NameResolution {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Resolved(left), Self::Resolved(right)) => left == right,
            (Self::Parameter(left), Self::Parameter(right)) => left.ordinal == right.ordinal,
            (Self::Ambiguous, Self::Ambiguous) | (Self::Unresolved, Self::Unresolved) => true,
            _ => false,
        }
    }
}

impl Eq for NameResolution {}

/// Source-owned generalization eligibility frozen while lowering an admitted
/// binding. F5a recognizes only values; later computation forms remain
/// unclassified until their exact gate specifies them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EvaluationClass {
    FetchValue,
}

#[derive(Clone, Debug)]
pub enum ResolvedExpr {
    Lambda {
        occurrence: HirOccurrenceId,
        parameter: HirParameterId,
        body: Box<ResolvedExpr>,
        range: Range<usize>,
    },
    Integer {
        occurrence: HirOccurrenceId,
        spelling: String,
        range: Range<usize>,
    },
    Name {
        occurrence: HirOccurrenceId,
        name: HirName,
        resolution: NameResolution,
        range: Range<usize>,
    },
    Error {
        occurrence: HirOccurrenceId,
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

impl ResolvedExpr {
    pub fn occurrence(&self) -> &HirOccurrenceId {
        match self {
            Self::Lambda { occurrence, .. }
            | Self::Integer { occurrence, .. }
            | Self::Name { occurrence, .. }
            | Self::Error { occurrence, .. } => occurrence,
        }
    }

    pub fn range(&self) -> &Range<usize> {
        match self {
            Self::Lambda { range, .. }
            | Self::Integer { range, .. }
            | Self::Name { range, .. }
            | Self::Error { range, .. } => range,
        }
    }
}

// Artifact identity protects cross-module lookup. It is not source semantics,
// so existing structural HIR equality intentionally continues to compare the
// lowered expression payload rather than the freshly minted artifact token.
impl PartialEq for ResolvedExpr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Lambda {
                    parameter: left_parameter,
                    body: left_body,
                    range: left_range,
                    ..
                },
                Self::Lambda {
                    parameter: right_parameter,
                    body: right_body,
                    range: right_range,
                    ..
                },
            ) => {
                left_parameter.ordinal == right_parameter.ordinal
                    && left_body == right_body
                    && left_range == right_range
            }
            (
                Self::Integer {
                    spelling: left_spelling,
                    range: left_range,
                    ..
                },
                Self::Integer {
                    spelling: right_spelling,
                    range: right_range,
                    ..
                },
            ) => left_spelling == right_spelling && left_range == right_range,
            (
                Self::Name {
                    name: left_name,
                    resolution: left_resolution,
                    range: left_range,
                    ..
                },
                Self::Name {
                    name: right_name,
                    resolution: right_resolution,
                    range: right_range,
                    ..
                },
            ) => {
                left_name == right_name
                    && left_resolution == right_resolution
                    && left_range == right_range
            }
            (
                Self::Error {
                    errors: left_errors,
                    range: left_range,
                    ..
                },
                Self::Error {
                    errors: right_errors,
                    range: right_range,
                    ..
                },
            ) => left_errors == right_errors && left_range == right_range,
            _ => false,
        }
    }
}

impl Eq for ResolvedExpr {}

#[derive(Clone, Debug)]
pub struct HirBinding {
    id: Arc<DefId>,
    definition_root: DefinitionRootId,
    visibility: HirVisibility,
    name: HirName,
    parameters: Box<[HirParameter]>,
    #[allow(dead_code, reason = "frozen for the later exact generalization gate")]
    evaluation_class: Option<EvaluationClass>,
    value: ResolvedExpr,
    range: Range<usize>,
}

fn evaluation_class(value: &ResolvedExpr) -> Option<EvaluationClass> {
    match value {
        ResolvedExpr::Lambda { .. }
        | ResolvedExpr::Integer { .. }
        | ResolvedExpr::Name {
            resolution: NameResolution::Resolved(_) | NameResolution::Parameter(_),
            ..
        } => Some(EvaluationClass::FetchValue),
        ResolvedExpr::Name {
            resolution: NameResolution::Ambiguous | NameResolution::Unresolved,
            ..
        }
        | ResolvedExpr::Error { .. } => None,
    }
}

impl HirBinding {
    pub fn id(&self) -> &DefId {
        &self.id
    }
    pub fn definition_root(&self) -> &DefinitionRootId {
        &self.definition_root
    }
    pub fn visibility(&self) -> HirVisibility {
        self.visibility
    }
    pub fn name(&self) -> &HirName {
        &self.name
    }
    pub fn parameters(&self) -> &[HirParameter] {
        &self.parameters
    }
    pub fn value(&self) -> &ResolvedExpr {
        &self.value
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

// Artifact identity protects root queries but is not source semantics, just
// like expression occurrence identity. Structural HIR equality excludes it.
impl PartialEq for HirBinding {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
            && self.visibility == other.visibility
            && self.name == other.name
            && self.parameters == other.parameters
            && self.value == other.value
            && self.range == other.range
    }
}

impl Eq for HirBinding {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirItem {
    Binding(HirBinding),
    Expression(ResolvedExpr),
    Error {
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirErrorOrigin {
    Syntax,
    Lowering,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirErrorAttachment {
    Module,
    DirectRootItem(u32),
    Definition(DefId),
    Value(DefId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirErrorKind {
    InheritedMissing,
    InheritedRawError,
    InheritedInvalid,
    UnsupportedItem,
    UnsupportedTarget,
    UnsupportedExpression,
    MissingBody,
    DuplicateDefinition,
    AmbiguousName,
    UnresolvedName,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirError {
    id: HirErrorId,
    origin: HirErrorOrigin,
    attachment: HirErrorAttachment,
    range: Range<usize>,
    kind: HirErrorKind,
    diagnostic: Option<HirDiagnosticId>,
}

impl HirError {
    pub fn id(&self) -> HirErrorId {
        self.id
    }
    pub fn origin(&self) -> HirErrorOrigin {
        self.origin
    }
    pub fn attachment(&self) -> &HirErrorAttachment {
        &self.attachment
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn kind(&self) -> HirErrorKind {
        self.kind
    }
    pub fn diagnostic(&self) -> Option<HirDiagnosticId> {
        self.diagnostic
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirDiagnostic {
    id: HirDiagnosticId,
    error: HirErrorId,
    kind: HirErrorKind,
    range: Range<usize>,
}

impl HirDiagnostic {
    pub fn id(&self) -> HirDiagnosticId {
        self.id
    }
    pub fn error(&self) -> HirErrorId {
        self.error
    }
    pub fn kind(&self) -> HirErrorKind {
        self.kind
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Debug)]
pub struct HirModule {
    artifact: Arc<HirArtifactToken>,
    identity: ModuleIdentity,
    source_revision: SourceRevision,
    items: Vec<HirItem>,
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
}

impl HirModule {
    /// Tests whether a branded occurrence was minted by this exact artifact.
    pub fn owns_occurrence(&self, occurrence: &HirOccurrenceId) -> bool {
        Arc::ptr_eq(&self.artifact, &occurrence.artifact)
    }

    /// Tests whether a branded definition root was minted by this exact artifact.
    pub fn owns_definition_root(&self, root: &DefinitionRootId) -> bool {
        Arc::ptr_eq(&self.artifact, &root.artifact)
    }

    pub fn owns_parameter(&self, parameter: &HirParameterId) -> bool {
        Arc::ptr_eq(&self.artifact, &parameter.owner.artifact)
            && self.items.iter().any(|item| {
                matches!(item, HirItem::Binding(binding)
                    if binding.definition_root == parameter.owner
                        && binding.parameters.iter().any(|candidate| candidate.id == *parameter))
            })
    }

    pub fn identity(&self) -> &ModuleIdentity {
        &self.identity
    }
    pub fn source_revision(&self) -> SourceRevision {
        self.source_revision
    }
    pub fn items(&self) -> &[HirItem] {
        &self.items
    }
    pub fn errors(&self) -> &[HirError] {
        &self.errors
    }
    pub fn diagnostics(&self) -> &[HirDiagnostic] {
        &self.diagnostics
    }
    /// Storage reserved for definition roots in this immutable HIR artifact.
    pub const fn definition_root_allocation_bytes(&self) -> usize {
        self.definition_root_allocation_bytes
    }
    /// Definition roots share their binding's `DefId` reference rather than
    /// cloning a definition payload.
    pub const fn definition_root_def_id_clone_bytes(&self) -> usize {
        self.definition_root_def_id_clone_bytes
    }
}

impl PartialEq for HirModule {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
            && self.source_revision == other.source_revision
            && self.items == other.items
            && self.errors == other.errors
            && self.diagnostics == other.diagnostics
    }
}

impl Eq for HirModule {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirAvailabilityError {
    InconsistentIdentity,
    StructuralProjection,
    ExactOperatorEnvironment,
    IdentityExhausted,
}

/// Lowers direct-root bindings and expressions against one complete local namespace.
pub fn lower_module(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    _imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    lower_module_with_counters(identity, parsed, _imports, &mut counters)
}

fn lower_module_with_counters(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    _imports: SemanticImports,
    counters: &mut LoweringCounters,
) -> Result<HirModule, HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let recoveries = validated_recoveries(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let mut plans = Vec::new();
    for (index, node) in root.children().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        plans.push(plan_root(node, ordinal, &identity, counters)?);
    }
    let partition = partition_recoveries(&recoveries, plans.len(), counters)?;
    let namespace = namespace(&mut plans)?;
    let mut sink = ErrorSink::default();
    let root_errors = emit_structural_errors(&recoveries, &partition, &plans, &mut sink, counters)?;

    let artifact = mint_artifact_token();
    let mut items = Vec::with_capacity(plans.len());
    let mut next_occurrence_ordinal = 0u32;
    let mut scope = ScopeStack::default();
    for (plan, errors) in plans.iter().zip(root_errors) {
        let occurrence = next_occurrence(&artifact, &mut next_occurrence_ordinal)?;
        let definition_root = match &plan.kind {
            RootPlanKind::Binding(admitted) => {
                Some(DefinitionRootId::new(artifact.clone(), admitted.id.clone()))
            }
            RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => None,
        };
        if definition_root.is_some() {
            counters.definition_root_allocation_bytes += std::mem::size_of::<DefinitionRootId>();
        }
        items.push(lower_plan(
            plan,
            parsed,
            &namespace,
            errors.item,
            errors.value,
            &mut sink,
            counters,
            occurrence,
            definition_root,
            &artifact,
            &mut next_occurrence_ordinal,
            &mut scope,
        )?);
    }
    Ok(HirModule {
        artifact,
        identity,
        source_revision: parsed.revision(),
        items,
        errors: sink.errors,
        diagnostics: sink.diagnostics,
        definition_root_allocation_bytes: counters.definition_root_allocation_bytes,
        definition_root_def_id_clone_bytes: counters.definition_root_def_id_clone_bytes,
    })
}

fn next_occurrence(
    artifact: &Arc<HirArtifactToken>,
    ordinal: &mut u32,
) -> Result<HirOccurrenceId, HirAvailabilityError> {
    let current = *ordinal;
    *ordinal = ordinal
        .checked_add(1)
        .ok_or(HirAvailabilityError::IdentityExhausted)?;
    Ok(HirOccurrenceId::new(artifact.clone(), current))
}

#[derive(Default)]
struct LoweringCounters {
    recovery_visits: usize,
    syntax_emissions: usize,
    copied_spelling_bytes: usize,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
}

#[derive(Default)]
struct ScopeStack {
    parameters: Vec<HirParameter>,
}

#[derive(Clone, Copy)]
struct ScopeDepthGuard(usize);

impl ScopeStack {
    fn push_parameter(&mut self, parameter: HirParameter) -> ScopeDepthGuard {
        let depth = ScopeDepthGuard(self.parameters.len());
        self.parameters.push(parameter);
        depth
    }

    fn root_guard(&self) -> ScopeDepthGuard {
        ScopeDepthGuard(self.parameters.len())
    }

    fn restore(&mut self, guard: ScopeDepthGuard) {
        self.parameters.truncate(guard.0);
    }

    fn parameter(&self, spelling: &str) -> Option<&HirParameter> {
        self.parameters
            .iter()
            .rev()
            .find(|parameter| parameter.name.spelling == spelling)
    }
}

struct RecoveryPartition {
    module: Vec<usize>,
    roots: Vec<Vec<usize>>,
}

#[derive(Default)]
struct RootErrors {
    item: Vec<HirErrorId>,
    value: Vec<HirErrorId>,
}

fn partition_recoveries(
    recoveries: &[StructuralRecovery],
    root_count: usize,
    counters: &mut LoweringCounters,
) -> Result<RecoveryPartition, HirAvailabilityError> {
    let mut partition = RecoveryPartition {
        module: Vec::new(),
        roots: (0..root_count).map(|_| Vec::new()).collect(),
    };
    for (index, recovery) in recoveries.iter().enumerate() {
        counters.recovery_visits += 1;
        match recovery.direct_root_ordinal() {
            None => partition.module.push(index),
            Some(ordinal) => {
                let root = usize::try_from(ordinal)
                    .map_err(|_| HirAvailabilityError::StructuralProjection)?;
                let bucket = partition
                    .roots
                    .get_mut(root)
                    .ok_or(HirAvailabilityError::StructuralProjection)?;
                bucket.push(index);
            }
        }
    }
    Ok(partition)
}

fn emit_structural_errors(
    recoveries: &[StructuralRecovery],
    partition: &RecoveryPartition,
    plans: &[RootPlan],
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
) -> Result<Vec<RootErrors>, HirAvailabilityError> {
    let mut recovery_errors = Vec::with_capacity(recoveries.len());
    for recovery in recoveries {
        let attachment = match recovery.direct_root_ordinal() {
            None => HirErrorAttachment::Module,
            Some(ordinal) => {
                let root = usize::try_from(ordinal)
                    .map_err(|_| HirAvailabilityError::StructuralProjection)?;
                plans
                    .get(root)
                    .ok_or(HirAvailabilityError::StructuralProjection)?
                    .recovery_attachment(recovery)
            }
        };
        recovery_errors.push(sink.syntax(recovery, attachment)?);
        counters.syntax_emissions += 1;
    }

    let mut roots = (0..plans.len())
        .map(|_| RootErrors::default())
        .collect::<Vec<_>>();
    for (root, indices) in partition.roots.iter().enumerate() {
        for &index in indices {
            let recovery = recoveries
                .get(index)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            let attachment = plans[root].recovery_attachment(recovery);
            let error = *recovery_errors
                .get(index)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            match attachment {
                HirErrorAttachment::DirectRootItem(_) => roots[root].item.push(error),
                HirErrorAttachment::Value(_) => roots[root].value.push(error),
                HirErrorAttachment::Module | HirErrorAttachment::Definition(_) => {}
            }
        }
    }
    if partition
        .module
        .iter()
        .any(|&index| index >= recovery_errors.len())
    {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    Ok(roots)
}

#[derive(Clone)]
struct RootPlan {
    ordinal: u32,
    node: SyntaxNode,
    range: Range<usize>,
    kind: RootPlanKind,
}

#[derive(Clone)]
enum RootPlanKind {
    Binding(Admitted),
    DirectExpression,
    Unsupported(HirErrorKind),
}

#[derive(Clone)]
struct Admitted {
    id: Arc<DefId>,
    visibility: HirVisibility,
    name: HirName,
    parameter: Option<HirName>,
}

impl RootPlan {
    fn recovery_attachment(&self, recovery: &StructuralRecovery) -> HirErrorAttachment {
        match &self.kind {
            RootPlanKind::Binding(admitted) => {
                if recovery.path().contains(&SyntaxKind::BindingBody) {
                    HirErrorAttachment::Value((*admitted.id).clone())
                } else {
                    HirErrorAttachment::Definition((*admitted.id).clone())
                }
            }
            RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => {
                HirErrorAttachment::DirectRootItem(self.ordinal)
            }
        }
    }
}

fn plan_root(
    node: SyntaxNode,
    ordinal: u32,
    identity: &ModuleIdentity,
    counters: &mut LoweringCounters,
) -> Result<RootPlan, HirAvailabilityError> {
    let range = range_of(&node);
    if node.kind() == SyntaxKind::OperatorChain {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::DirectExpression,
        });
    }
    if node.kind() != SyntaxKind::BindingStatement {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::Unsupported(HirErrorKind::UnsupportedItem),
        });
    }
    let Some((visibility, name, parameter)) = plain_binding_header(&node) else {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::Unsupported(HirErrorKind::UnsupportedTarget),
        });
    };
    counters.copied_spelling_bytes += name.spelling.len();
    let same_name_ordinal = 0; // assigned after all direct-root headers are known
    let id = Arc::new(DefId {
        module: identity.module.clone(),
        spelling: name.spelling.clone().into_boxed_str(),
        same_name_ordinal,
    });
    Ok(RootPlan {
        ordinal,
        node,
        range,
        kind: RootPlanKind::Binding(Admitted {
            id,
            visibility,
            name,
            parameter,
        }),
    })
}

fn namespace(plans: &mut [RootPlan]) -> Result<HashMap<String, Vec<DefId>>, HirAvailabilityError> {
    let mut seen = HashMap::<String, u32>::new();
    let mut namespace = HashMap::<String, Vec<DefId>>::new();
    for plan in plans {
        let RootPlanKind::Binding(admitted) = &mut plan.kind else {
            continue;
        };
        let ordinal = seen.entry(admitted.name.spelling.clone()).or_default();
        let id = Arc::new(DefId {
            module: admitted.id.module.clone(),
            spelling: admitted.id.spelling.clone(),
            same_name_ordinal: *ordinal,
        });
        *ordinal = ordinal
            .checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        admitted.id = id.clone();
        namespace
            .entry(admitted.name.spelling.clone())
            .or_default()
            .push((*id).clone());
    }
    Ok(namespace)
}

fn lower_plan(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &HashMap<String, Vec<DefId>>,
    mut item_errors: Vec<HirErrorId>,
    value_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    definition_root: Option<DefinitionRootId>,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence_ordinal: &mut u32,
    scope: &mut ScopeStack,
) -> Result<HirItem, HirAvailabilityError> {
    let RootPlanKind::Binding(admitted) = &plan.kind else {
        return match &plan.kind {
            RootPlanKind::DirectExpression => lower_direct_root_expression(
                plan,
                parsed,
                namespace,
                item_errors,
                sink,
                counters,
                occurrence,
                scope,
            ),
            RootPlanKind::Unsupported(kind) => {
                item_errors.push(sink.lowering(
                    *kind,
                    HirErrorAttachment::DirectRootItem(plan.ordinal),
                    plan.range.clone(),
                )?);
                Ok(HirItem::Error {
                    errors: item_errors.into_boxed_slice(),
                    range: plan.range.clone(),
                })
            }
            RootPlanKind::Binding(_) => unreachable!("binding plan matched above"),
        };
    };
    let id = admitted.id.clone();
    let definition_root = definition_root.expect("admitted binding has a definition root");
    let parameters = admitted
        .parameter
        .as_ref()
        .map(|name| {
            vec![HirParameter {
                id: HirParameterId::new(definition_root.clone(), 0),
                name: name.clone(),
                range: name.range.clone(),
            }]
            .into_boxed_slice()
        })
        .unwrap_or_default();
    let body_occurrence = if parameters.is_empty() {
        occurrence.clone()
    } else {
        next_occurrence(artifact, next_occurrence_ordinal)?
    };
    let guard = parameters
        .first()
        .map(|parameter| scope.push_parameter(parameter.clone()))
        .unwrap_or_else(|| scope.root_guard());
    let lowered = lower_body(
        plan,
        parsed,
        namespace,
        &id,
        value_errors,
        sink,
        counters,
        body_occurrence,
        scope,
    );
    scope.restore(guard);
    let (value, body_semantic_error) = lowered?;
    if id.same_name_ordinal > 0 {
        sink.lowering(
            HirErrorKind::DuplicateDefinition,
            HirErrorAttachment::Definition((*id).clone()),
            admitted.name.range.clone(),
        )?;
    }
    if let Some((kind, range)) = body_semantic_error {
        sink.lowering(kind, HirErrorAttachment::Value((*id).clone()), range)?;
    }
    let value = if let Some(parameter) = parameters.first() {
        ResolvedExpr::Lambda {
            occurrence,
            parameter: parameter.id.clone(),
            range: plan.range.clone(),
            body: Box::new(value),
        }
    } else {
        value
    };
    let evaluation_class = evaluation_class(&value);
    Ok(HirItem::Binding(HirBinding {
        id,
        definition_root,
        visibility: admitted.visibility,
        name: admitted.name.clone(),
        parameters,
        evaluation_class,
        value,
        range: plan.range.clone(),
    }))
}

fn lower_direct_root_expression(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &HashMap<String, Vec<DefId>>,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<HirItem, HirAvailabilityError> {
    if !causal_errors.is_empty() {
        return Ok(HirItem::Expression(ResolvedExpr::Error {
            occurrence,
            errors: causal_errors.into_boxed_slice(),
            range: plan.range.clone(),
        }));
    }
    match lower_simple_chain(
        parsed,
        &plan.node,
        namespace,
        counters,
        occurrence.clone(),
        scope,
    )? {
        SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } => {
            if let Some((kind, range)) = semantic_error {
                sink.lowering(
                    kind,
                    HirErrorAttachment::DirectRootItem(plan.ordinal),
                    range,
                )?;
            }
            Ok(HirItem::Expression(expression))
        }
        SimpleChainLowering::Unsupported { range } => {
            causal_errors.push(sink.lowering(
                HirErrorKind::UnsupportedExpression,
                HirErrorAttachment::DirectRootItem(plan.ordinal),
                range.clone(),
            )?);
            Ok(HirItem::Expression(ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range,
            }))
        }
    }
}

fn lower_body(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &HashMap<String, Vec<DefId>>,
    id: &DefId,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<(ResolvedExpr, Option<(HirErrorKind, Range<usize>)>), HirAvailabilityError> {
    let Some(body) = plan
        .node
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
    else {
        causal_errors.push(sink.lowering(
            HirErrorKind::MissingBody,
            HirErrorAttachment::Value(id.clone()),
            plan.range.clone(),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: plan.range.clone(),
            },
            None,
        ));
    };
    let children = body.children().collect::<Vec<_>>();
    if matches!(children.as_slice(), [child] if child.kind() == SyntaxKind::IndentedStatementBlock)
    {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    if has_recovery(&body) {
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    let [chain] = children.as_slice() else {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    };
    if chain.kind() != SyntaxKind::OperatorChain {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            range_of(&body),
        )?);
        return Ok((
            ResolvedExpr::Error {
                occurrence,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    match lower_simple_chain(
        parsed,
        chain,
        namespace,
        counters,
        occurrence.clone(),
        scope,
    )? {
        SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } => Ok((expression, semantic_error)),
        SimpleChainLowering::Unsupported { range } => {
            causal_errors.push(sink.lowering(
                HirErrorKind::UnsupportedExpression,
                HirErrorAttachment::Value(id.clone()),
                range.clone(),
            )?);
            Ok((
                ResolvedExpr::Error {
                    occurrence,
                    errors: causal_errors.into_boxed_slice(),
                    range,
                },
                None,
            ))
        }
    }
}

enum SimpleChainLowering {
    Resolved {
        expression: ResolvedExpr,
        semantic_error: Option<(HirErrorKind, Range<usize>)>,
    },
    Unsupported {
        range: Range<usize>,
    },
}

fn lower_simple_chain(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    let chain_range = range_of(chain);
    let (expression, atom) = associate_chain_owned(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => {
                HirAvailabilityError::ExactOperatorEnvironment
            }
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
        })?
        .into_parts();
    let Some(atom) = atom else {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    };
    if !matches!(expression, HirExpr::Value { children, .. } if children.is_empty()) {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    }
    match atom.kind {
        SyntaxKind::IntegerLiteral => Ok(SimpleChainLowering::Resolved {
            expression: ResolvedExpr::Integer {
                occurrence,
                spelling: {
                    counters.copied_spelling_bytes += atom.spelling.len();
                    atom.spelling
                },
                range: atom.range,
            },
            semantic_error: None,
        }),
        SyntaxKind::IdentifierExpression => {
            counters.copied_spelling_bytes += atom.spelling.len();
            let name = HirName {
                spelling: atom.spelling,
                range: atom.range.clone(),
            };
            let (resolution, kind) = if let Some(parameter) = scope.parameter(&name.spelling) {
                (NameResolution::Parameter(parameter.id.clone()), None)
            } else {
                match namespace.get(&name.spelling) {
                    Some(definitions) if definitions.len() == 1 => {
                        (NameResolution::Resolved(definitions[0].clone()), None)
                    }
                    Some(_) => (NameResolution::Ambiguous, Some(HirErrorKind::AmbiguousName)),
                    None => (
                        NameResolution::Unresolved,
                        Some(HirErrorKind::UnresolvedName),
                    ),
                }
            };
            Ok(SimpleChainLowering::Resolved {
                expression: ResolvedExpr::Name {
                    occurrence,
                    range: name.range.clone(),
                    name: name.clone(),
                    resolution,
                },
                semantic_error: kind.map(|kind| (kind, name.range)),
            })
        }
        _ => Err(HirAvailabilityError::StructuralProjection),
    }
}

fn plain_binding_header(node: &SyntaxNode) -> Option<(HirVisibility, HirName, Option<HirName>)> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::BindingHeader)?;
    let visibility = header.children_with_tokens().find_map(|element| {
        let token = element.into_token()?;
        match token.kind() {
            SyntaxKind::MyKw => Some(HirVisibility::Private),
            SyntaxKind::OurKw => Some(HirVisibility::Our),
            SyntaxKind::PubKw => Some(HirVisibility::Public),
            _ => None,
        }
    })?;
    let patterns = header.children().collect::<Vec<_>>();
    let [target] = patterns.as_slice() else {
        return None;
    };
    if target.kind() != SyntaxKind::Pattern || has_recovery(target) {
        return None;
    }
    let pattern_children = target.children().collect::<Vec<_>>();
    let (head, parameter) = match pattern_children.as_slice() {
        [head] => (identifier_pattern_name(head)?, None),
        [head, tail] if tail.kind() == SyntaxKind::PatternMlApplicationTail => {
            if has_recovery(tail) {
                return None;
            }
            let arguments = tail.children().collect::<Vec<_>>();
            let [argument] = arguments.as_slice() else {
                return None;
            };
            if argument.kind() != SyntaxKind::Pattern || has_recovery(argument) {
                return None;
            }
            let argument_children = argument.children().collect::<Vec<_>>();
            let [argument] = argument_children.as_slice() else {
                return None;
            };
            (
                identifier_pattern_name(head)?,
                Some(identifier_pattern_name(argument)?),
            )
        }
        _ => return None,
    };
    Some((visibility, head, parameter))
}

fn identifier_pattern_name(pattern: &SyntaxNode) -> Option<HirName> {
    if pattern.kind() != SyntaxKind::IdentifierPattern || has_recovery(pattern) {
        return None;
    }
    let tokens = pattern
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .collect::<Vec<_>>();
    let [token] = tokens.as_slice() else {
        return None;
    };
    (token.kind() == SyntaxKind::Identifier).then(|| HirName {
        spelling: token.text().to_owned(),
        range: token_range(token),
    })
}

fn has_recovery(node: &SyntaxNode) -> bool {
    node.descendants_with_tokens().any(|element| {
        element
            .as_node()
            .is_some_and(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
            || element
                .into_token()
                .is_some_and(|token| token.kind() == SyntaxKind::Error)
    })
}

fn token_range(token: &yu_syntax::SyntaxToken) -> Range<usize> {
    let range = token.text_range();
    u32::from(range.start()) as usize..u32::from(range.end()) as usize
}

fn validated_recoveries(
    parsed: &ParsedFile,
) -> Result<Vec<StructuralRecovery>, HirAvailabilityError> {
    let recoveries = parsed
        .try_structural_recoveries()
        .map_err(|_| HirAvailabilityError::StructuralProjection)?;
    for (index, recovery) in recoveries.iter().enumerate() {
        if recovery.ordinal()
            != u32::try_from(index).map_err(|_| HirAvailabilityError::StructuralProjection)?
        {
            return Err(HirAvailabilityError::StructuralProjection);
        }
    }
    Ok(recoveries)
}

#[derive(Default)]
struct ErrorSink {
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
}

impl ErrorSink {
    fn syntax(
        &mut self,
        recovery: &StructuralRecovery,
        attachment: HirErrorAttachment,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        let kind = match recovery.kind() {
            StructuralRecoveryKind::Missing => HirErrorKind::InheritedMissing,
            StructuralRecoveryKind::RawError => HirErrorKind::InheritedRawError,
            StructuralRecoveryKind::Invalid => HirErrorKind::InheritedInvalid,
        };
        self.push(
            HirErrorOrigin::Syntax,
            attachment,
            recovery.range().clone(),
            kind,
            false,
        )
    }

    fn lowering(
        &mut self,
        kind: HirErrorKind,
        attachment: HirErrorAttachment,
        range: Range<usize>,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        self.push(HirErrorOrigin::Lowering, attachment, range, kind, true)
    }

    fn push(
        &mut self,
        origin: HirErrorOrigin,
        attachment: HirErrorAttachment,
        range: Range<usize>,
        kind: HirErrorKind,
        diagnostic: bool,
    ) -> Result<HirErrorId, HirAvailabilityError> {
        let error = HirErrorId(
            u32::try_from(self.errors.len())
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
        );
        let diagnostic = if diagnostic {
            let id = HirDiagnosticId(
                u32::try_from(self.diagnostics.len())
                    .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
            );
            self.diagnostics.push(HirDiagnostic {
                id,
                error,
                kind,
                range: range.clone(),
            });
            Some(id)
        } else {
            None
        };
        self.errors.push(HirError {
            id: error,
            origin,
            attachment,
            range,
            kind,
            diagnostic,
        });
        Ok(error)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    fn identity() -> ModuleIdentity {
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "counters.yu")))
    }

    #[test]
    fn recovery_partition_visits_and_emits_each_occurrence_once() {
        let parsed = parsed("my x = @; my y = (");
        let recoveries = parsed.structural_recoveries();
        let mut counters = LoweringCounters::default();
        let module = lower_module_with_counters(
            identity(),
            &parsed,
            SemanticImports::empty(),
            &mut counters,
        )
        .expect("recovery lowering remains available");

        assert_eq!(counters.recovery_visits, recoveries.len());
        assert_eq!(counters.syntax_emissions, recoveries.len());
        assert_eq!(
            module
                .errors()
                .iter()
                .filter(|error| error.origin() == HirErrorOrigin::Syntax)
                .count(),
            recoveries.len()
        );
        assert_eq!(counters.copied_spelling_bytes, b"xy".len());
    }

    #[test]
    fn occurrence_ids_remain_distinct_for_equal_zero_width_error_ranges() {
        let artifact = mint_artifact_token();
        let first = ResolvedExpr::Error {
            occurrence: HirOccurrenceId::new(artifact.clone(), 0),
            errors: Box::new([]),
            range: 0..0,
        };
        let second = ResolvedExpr::Error {
            occurrence: HirOccurrenceId::new(artifact, 1),
            errors: Box::new([]),
            range: 0..0,
        };
        assert_eq!(first.range(), second.range());
        assert_ne!(first.occurrence(), second.occurrence());
    }

    #[test]
    fn parameter_id_has_the_exact_positive_trait_surface() {
        fn assert_traits<T: Clone + std::fmt::Debug + Eq + Hash>() {}
        assert_traits::<HirParameterId>();
    }

    #[test]
    fn parameter_has_the_exact_positive_trait_surface() {
        fn assert_traits<T: Clone + std::fmt::Debug + Eq>() {}
        assert_traits::<HirParameter>();
    }

    #[test]
    fn evaluation_classification_is_private_and_frozen_on_bindings() {
        let module = lower_module(
            identity(),
            &parsed("my x = 1; my y = x; my f p = p; my missing = nope; my bad = @"),
            SemanticImports::empty(),
        )
        .expect("lowering remains available");
        let [
            HirItem::Binding(x),
            HirItem::Binding(y),
            HirItem::Binding(f),
            HirItem::Binding(missing),
            HirItem::Binding(bad),
        ] = module.items()
        else {
            panic!("five bindings")
        };
        assert_eq!(x.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(y.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(f.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(missing.evaluation_class, None);
        assert_eq!(bad.evaluation_class, None);
    }

    #[test]
    fn def_id_hash_eq_payload_bytes_include_spelling_and_source_root_file_key_text() {
        let realm = "identity-realm";
        let path = "nested/identity-module.yu";
        let module = lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(realm, path))),
            &parsed("my definition = 42"),
            SemanticImports::empty(),
        )
        .expect("simple binding lowers");
        let HirItem::Binding(binding) = &module.items()[0] else {
            panic!("binding");
        };
        assert_eq!(
            binding.id().hash_eq_payload_bytes(),
            realm.len() + path.len() + binding.id().spelling().len()
        );
    }
}
