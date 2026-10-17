use std::{
    alloc::{Layout, alloc},
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

use crate::{AssociationError, AssociationProvenance, HirExpr, associate_chain_owned, associate_chain_owned_with_sources, range_of};

pub(crate) mod local_source;
pub(crate) mod source_annotation;

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

/// An actual direct-root expression, minted only while lowering that item.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExpressionRootId {
    occurrence: HirOccurrenceId,
}
impl ExpressionRootId {
    pub fn occurrence(&self) -> &HirOccurrenceId { &self.occurrence }
}
/// Authentic source ownership without manufacturing a definition.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SourceRootId {
    Definition(DefinitionRootId),
    Expression(ExpressionRootId),
}
impl SourceRootId {
    pub fn definition_root(&self) -> Option<&DefinitionRootId> {
        match self { Self::Definition(root) => Some(root), Self::Expression(_) => None }
    }
    pub fn expression_root(&self) -> Option<&ExpressionRootId> {
        match self { Self::Expression(root) => Some(root), Self::Definition(_) => None }
    }
    fn artifact(&self) -> &Arc<HirArtifactToken> {
        match self {
            Self::Definition(root) => &root.artifact,
            Self::Expression(root) => &root.occurrence.artifact,
        }
    }
}
impl From<DefinitionRootId> for SourceRootId {
    fn from(root: DefinitionRootId) -> Self { Self::Definition(root) }
}
impl From<ExpressionRootId> for SourceRootId {
    fn from(root: ExpressionRootId) -> Self { Self::Expression(root) }
}

/// A local identity anchored to its enclosing artifact root.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct HirLocalId {
    owner: SourceRootId,
    ordinal: u32,
}
impl HirLocalId {
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn ordinal(&self) -> u32 {
        self.ordinal
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
    owner: SourceRootId,
    ordinal: u32,
}

impl HirParameterId {
    fn new(owner: impl Into<SourceRootId>, ordinal: u32) -> Self {
        Self { owner: owner.into(), ordinal }
    }

    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }

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
    /// Structural source application with its associated operands. Ordinary HIR
    /// admission and the opt-in shadow route share this shape; neither occurrence
    /// asserts callability or supplies a Call typing rule. The opt-in route keeps
    /// its pending-structure error attached, while ordinary admission carries only
    /// authentic operand-resolution errors.
    Apply {
        occurrence: HirOccurrenceId,
        source_form: SyntaxKind,
        callee: Box<ResolvedExpr>,
        argument: Box<ResolvedExpr>,
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
    /// Retained parenthesized source structure; no semantic grouping rule is supplied.
    Group {
        occurrence: HirOccurrenceId,
        inner: Box<ResolvedExpr>,
        range: Range<usize>,
    },
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
            Self::Apply { occurrence, .. } => occurrence,
            Self::Group { occurrence, .. }
            | Self::Lambda { occurrence, .. }
            | Self::Integer { occurrence, .. }
            | Self::Name { occurrence, .. }
            | Self::Error { occurrence, .. } => occurrence,
        }
    }

    pub fn range(&self) -> &Range<usize> {
        match self {
            Self::Apply { range, .. } => range,
            Self::Group { range, .. }
            | Self::Lambda { range, .. }
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
                Self::Apply {
                    source_form: left_form,
                    callee: left_callee,
                    argument: left_argument,
                    errors: left_errors,
                    range: left_range,
                    ..
                },
                Self::Apply {
                    source_form: right_form,
                    callee: right_callee,
                    argument: right_argument,
                    errors: right_errors,
                    range: right_range,
                    ..
                },
            ) => {
                left_form == right_form
                    && left_callee == right_callee
                    && left_argument == right_argument
                    && left_errors == right_errors
                    && left_range == right_range
            }
            (
                Self::Group {
                    inner: left,
                    range: left_range,
                    ..
                },
                Self::Group {
                    inner: right,
                    range: right_range,
                    ..
                },
            ) => left == right && left_range == right_range,
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
        ResolvedExpr::Apply { .. } | ResolvedExpr::Group { .. } => None,
        ResolvedExpr::Lambda { body, .. }
            if matches!(body.as_ref(), ResolvedExpr::Apply { .. }) =>
        {
            None
        }
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
    pub(crate) source_identity: Option<crate::source_identity::HirSourceIdentity>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) captured_source: Option<(DefinitionRootId, Arc<crate::shadow::ShadowArtifact>)>,
    pub(crate) local_sources: HashMap<DefinitionRootId, local_source::LocalSource>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) effect_declarations: Vec<source_annotation::SourceEffectDeclaration>,
    expression_roots: HashMap<HirOccurrenceId, ExpressionRootId>,
    source_carriers: Vec<(SourceRootId, local_source::SourceCarrierOutcome)>,
    source_carrier_indices: HashMap<SourceRootId, usize>,
    identity: ModuleIdentity,
    source_revision: SourceRevision,
    items: Vec<HirItem>,
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
}

impl HirModule {
    /// Ordinary binding/expression outcomes in direct-root source order.
    /// The opt-in binding adapter keeps its existing single-owned binding map.
    pub fn source_carrier_outcomes(&self) -> &[(SourceRootId, local_source::SourceCarrierOutcome)] {
        &self.source_carriers
    }
    /// Resolves only the original occurrence of an actual expression item.
    pub fn expression_root(&self, occurrence: &HirOccurrenceId)
        -> Result<Option<&ExpressionRootId>, HirAvailabilityError>
    {
        if !self.owns_occurrence(occurrence) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.expression_roots.get(occurrence))
    }
    pub fn owns_expression_root(&self, root: &ExpressionRootId) -> bool {
        self.expression_roots.get(root.occurrence()) == Some(root)
    }
    pub fn owns_source_root(&self, root: &SourceRootId) -> bool {
        match root {
            SourceRootId::Definition(root) => self.owns_definition_root(root),
            SourceRootId::Expression(root) => self.owns_expression_root(root),
        }
    }
    pub fn source_carrier_for(&self, root: &SourceRootId)
        -> Result<Option<&local_source::SourceCarrierOutcome>, HirAvailabilityError>
    {
        if !self.owns_source_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_carrier_indices.get(root).map(|index| &self.source_carriers[*index].1))
    }
    pub fn source_carrier(&self, root: &DefinitionRootId)
        -> Result<Option<&local_source::SourceCarrierOutcome>, HirAvailabilityError>
    {
        self.source_carrier_for(&SourceRootId::Definition(root.clone()))
    }
    pub fn local_source_for(&self, root: &SourceRootId)
        -> Result<Option<&local_source::LocalSource>, HirAvailabilityError>
    {
        Ok(match self.source_carrier_for(root)? {
            Some(local_source::SourceCarrierOutcome::Supported(source)) => Some(source),
            Some(local_source::SourceCarrierOutcome::Unsupported(_)) => None,
            None => root.definition_root().and_then(|root| self.local_sources.get(root)),
        })
    }
    /// Definition-only compatibility adapter over the authentic source owner.
    pub fn local_source(&self, root: &DefinitionRootId)
        -> Result<Option<&local_source::LocalSource>, HirAvailabilityError>
    {
        self.local_source_for(&SourceRootId::Definition(root.clone()))
    }
    /// Exact parse-owned origin retained for a definition from this artifact.
    pub fn definition_source_key(&self, root: &DefinitionRootId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_definition_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.definitions.get(root)))
    }
    pub fn expression_source_key(&self, root: &ExpressionRootId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_expression_root(root) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.expressions.get(root)))
    }
    pub fn source_root_source_key(&self, root: &SourceRootId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        match root {
            SourceRootId::Definition(root) => self.definition_source_key(root),
            SourceRootId::Expression(root) => self.expression_source_key(root),
        }
    }
    /// Exact source node for an ordinary or retained structural occurrence.
    pub fn occurrence_source_key(&self, occurrence: &HirOccurrenceId)
        -> Result<Option<&yu_syntax::SourceNodeKey>, HirAvailabilityError>
    {
        if !self.owns_occurrence(occurrence) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.occurrences.get(occurrence)))
    }
    /// Retains named and inline parameter origins without reconstructing binders.
    pub fn parameter_source_origin(&self, parameter: &HirParameterId)
        -> Result<Option<&crate::HirParameterSourceOrigin>, HirAvailabilityError>
    {
        if !self.owns_source_root(parameter.source_root()) { return Err(HirAvailabilityError::InconsistentIdentity); }
        Ok(self.source_identity.as_ref().and_then(|identity| identity.parameters.get(parameter)))
    }
    /// Tests whether a branded occurrence was minted by this exact artifact.
    pub fn owns_occurrence(&self, occurrence: &HirOccurrenceId) -> bool {
        Arc::ptr_eq(&self.artifact, &occurrence.artifact)
    }

    /// Tests whether a branded definition root was minted by this exact artifact.
    pub fn owns_definition_root(&self, root: &DefinitionRootId) -> bool {
        Arc::ptr_eq(&self.artifact, &root.artifact)
    }

    pub fn owns_parameter(&self, parameter: &HirParameterId) -> bool {
        Arc::ptr_eq(&self.artifact, parameter.owner.artifact())
            && self.items.iter().any(|item| {
                matches!(item, HirItem::Binding(binding)
                    if Some(&binding.definition_root) == parameter.definition_root()
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
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::try_source_keys(parsed)?;
    counters.ordinary_source_carriers = true;
    lower_module_with_counters(identity, parsed, _imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_source_identity(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_shadow_applications(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.shadow_applications = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn lower_module_with_local_source(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    let mut counters = LoweringCounters::default();
    counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(parsed));
    counters.source_nodes = crate::source_identity::source_keys(parsed);
    counters.local_source = true;
    lower_module_with_counters(identity, parsed, imports, &mut counters)
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
    #[cfg(any(feature = "shadow", test))]
    if counters.local_source {
        counters.effect_declarations =
            source_annotation::declarations(&root, identity.module(), counters)?;
    }
    let mut plans = Vec::new();
    for (index, node) in root.children().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        plans.push(plan_root(node, ordinal, &identity, counters)?);
    }
    let partition = partition_recoveries(&recoveries, plans.len(), counters)?;
    let namespace = namespace(&mut plans)?;
    let mut sink = ErrorSink::default();
    let root_errors = emit_structural_errors(&recoveries, &partition, &plans, &mut sink, counters)?;

    #[cfg(any(feature = "shadow", test))]
    if counters.local_source {
        for (declaration, plan) in counters.effect_declarations.iter().zip(
            plans
                .iter()
                .filter(|plan| plan.node.kind() == SyntaxKind::ActDeclaration),
        ) {
            let ordinal = plan.ordinal;
            if counters
                .effect_namespace
                .get(declaration.spelling.as_ref())
                .is_some_and(|ids| ids.len() > 1)
            {
                sink.lowering(
                    HirErrorKind::DuplicateDefinition,
                    HirErrorAttachment::DirectRootItem(ordinal),
                    declaration.range.clone(),
                )?;
            }
            for member in &declaration.operations {
                if counters
                    .operation_namespace
                    .get(&(declaration.id.clone(), member.spelling.clone()))
                    .is_some_and(|members| members.len() > 1)
                {
                    sink.lowering(
                        HirErrorKind::DuplicateDefinition,
                        HirErrorAttachment::DirectRootItem(ordinal),
                        member.range.clone(),
                    )?;
                }
            }
        }
    }

    let artifact = mint_artifact_token();
    let mut items = Vec::with_capacity(plans.len());
    let mut expression_roots = HashMap::new();
    let mut next_occurrence_ordinal = 0u32;
    let mut scope = ScopeStack::default();
    #[cfg(any(feature = "shadow", test))]
    let mut effect_ordinal = 0usize;
    for (plan, errors) in plans.iter().zip(root_errors) {
        let occurrence = next_occurrence(&artifact, &mut next_occurrence_ordinal)?;
        if matches!(plan.kind, RootPlanKind::DirectExpression) {
            expression_roots.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            let root = ExpressionRootId { occurrence: occurrence.clone() };
            if let Some(source) = &mut counters.source_identity {
                let key = counters.source_nodes.get(&plan.node)
                    .ok_or(HirAvailabilityError::StructuralProjection)?;
                source.expressions.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                source.expressions.insert(root.clone(), key.clone());
            }
            expression_roots.insert(occurrence.clone(), root);
        }
        let definition_root = match &plan.kind {
            RootPlanKind::Binding(admitted) => {
                Some(DefinitionRootId::new(artifact.clone(), admitted.id.clone()))
            }
            RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => None,
        };
        if let (Some(source), Some(definition)) = (&mut counters.source_identity, &definition_root)
        {
            if let Some(key) = counters.source_nodes.get(&plan.node) {
                source.record_definition(definition.clone(), key.clone());
            }
        }
        if definition_root.is_some() {
            counters.definition_root_allocation_bytes += std::mem::size_of::<DefinitionRootId>();
        }
        let item = lower_plan(
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
        )?;
        #[cfg(any(feature = "shadow", test))]
        if counters.local_source && plan.node.kind() == SyntaxKind::ActDeclaration {
            let declaration = counters
                .effect_declarations
                .get_mut(effect_ordinal)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            effect_ordinal += 1;
            if let HirItem::Error { errors, .. } = &item {
                declaration
                    .placeholder_errors
                    .extend(errors.iter().copied().filter(|id| {
                        sink.errors.iter().any(|error| {
                            error.id == *id && error.kind == HirErrorKind::UnsupportedItem
                        })
                    }));
            }
        }
        items.push(item);
    }
    // Binding carrier allocation stays a complete first pass, preserving all
    // previously published binding-carrier ordinals in mixed modules.
    let mut outcomes = Vec::new();
    outcomes.try_reserve_exact(plans.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    outcomes.resize_with(plans.len(), || None);
    if counters.ordinary_source_carriers {
        for (index, (plan, item)) in plans.iter().zip(&items).enumerate() {
            let HirItem::Binding(binding) = item else { continue; };
            let owner = SourceRootId::Definition(binding.definition_root.clone());
            let outcome = local_source::form_ordinary(
                plan, &owner, &binding.parameters, &namespace,
                counters, &artifact, &mut next_occurrence_ordinal,
            )?;
            outcomes[index] = Some((owner, outcome));
        }
    }
    if counters.ordinary_source_carriers || counters.local_source {
        for (index, (plan, item)) in plans.iter().zip(&items).enumerate() {
            let HirItem::Expression(expression) = item else { continue; };
            let root = expression_roots.get(expression.occurrence())
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            let owner = SourceRootId::Expression(root.clone());
            let outcome = local_source::form_ordinary(
                plan, &owner, &[], &namespace, counters, &artifact, &mut next_occurrence_ordinal,
            )?;
            outcomes[index] = Some((owner, outcome));
        }
    }
    finalize_ordinary_admissions(
        &mut items,
        counters,
        &artifact,
        &mut next_occurrence_ordinal,
    )?;
    let source_carriers: Vec<_> = outcomes.into_iter().flatten().collect();
    let mut source_carrier_indices = HashMap::new();
    source_carrier_indices.try_reserve(source_carriers.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for (index, (owner, _)) in source_carriers.iter().enumerate() {
        source_carrier_indices.insert(owner.clone(), index);
    }
    Ok(HirModule {
        expression_roots,
        source_carriers,
        source_carrier_indices,
        artifact,
        source_identity: counters.source_identity.take(),
        #[cfg(any(feature = "shadow", test))]
        captured_source: None,
        local_sources: std::mem::take(&mut counters.local_sources),
        #[cfg(any(feature = "shadow", test))]
        effect_declarations: std::mem::take(&mut counters.effect_declarations),
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
    ordinary_source_carriers: bool,
    local_source: bool,
    local_sources: HashMap<DefinitionRootId, local_source::LocalSource>,
    #[cfg(any(feature = "shadow", test))]
    effect_declarations: Vec<source_annotation::SourceEffectDeclaration>,
    effect_namespace: HashMap<String, Vec<source_annotation::SourceEffectId>>,
    operation_namespace: HashMap<
        (source_annotation::SourceEffectId, Box<str>),
        Vec<Arc<source_annotation::SourceOperationDeclaration>>,
    >,
    shadow_applications: bool,
    source_identity: Option<crate::source_identity::HirSourceIdentity>,
    source_nodes: HashMap<SyntaxNode, yu_syntax::SourceNodeKey>,
    recovery_visits: usize,
    syntax_emissions: usize,
    copied_spelling_bytes: usize,
    definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
    pending_ordinary_admissions: Vec<PendingOrdinaryAdmission>,
    aggregate_error_references: usize,
    aggregate_error_reference_bytes: usize,
    ordinary_admission_item_visits: usize,
}

struct PendingOrdinaryAdmission {
    root: HirOccurrenceId,
    owner_item_index: usize,
    nodes: Vec<PendingProjectionNode>,
}

struct PendingProjectionNode {
    kind: PendingProjectionKind,
    source_atom: Option<crate::OwnedAtom>,
    range: Range<usize>,
    key: yu_syntax::SourceNodeKey,
    children: Vec<usize>,
    atom: Option<ResolvedExpr>,
    staged_error: Option<(HirErrorKind, Range<usize>)>,
    error: Option<HirErrorId>,
    descendant_errors: usize,
}

#[derive(Clone, Copy)]
enum PendingProjectionKind { Apply(SyntaxKind), Group, Atom }

fn lower_ordinary_admission(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &HashMap<String, Vec<DefId>>,
    causal_errors: &[HirErrorId],
    counters: &mut LoweringCounters,
    root_occurrence: HirOccurrenceId,
    owner_item_index: usize,
    scope: &ScopeStack,
) -> Result<Option<ResolvedExpr>, HirAvailabilityError> {
    if !causal_errors.is_empty() { return Ok(None); }
    let associated = associate_chain_owned_with_sources(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => HirAvailabilityError::ExactOperatorEnvironment,
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?;
    let (hir, provenance, _) = associated.into_projection_parts();
    let mut nodes = Vec::new();
    let mut tasks = Vec::new();
    tasks.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    tasks.push((&hir, &provenance, None::<usize>));
    while let Some((expression, source_shape, parent)) = tasks.pop() {
        let (kind, range, children) = match expression {
            HirExpr::Value { kind, range, children } => (*kind, range.clone(), children.as_slice()),
            HirExpr::Error { .. } | HirExpr::Apply { .. } => return Ok(None),
        };
        let AssociationProvenance::Node { source, children: source_children } = source_shape else {
            return Ok(None);
        };
        if source.kind() != kind || children.len() != source_children.len() { return Ok(None); }
        let projection_kind = match kind {
            SyntaxKind::IdentifierExpression | SyntaxKind::IntegerLiteral if children.is_empty() => PendingProjectionKind::Atom,
            SyntaxKind::ParenthesizedExpression if children.len() == 1 => {
                if has_direct_comma_or_separator(source) { return Ok(None); }
                PendingProjectionKind::Group
            }
            SyntaxKind::MlArgument | SyntaxKind::CallTail if children.len() == 2 => {
                if kind == SyntaxKind::CallTail && has_direct_comma_or_separator(source) { return Ok(None); }
                PendingProjectionKind::Apply(kind)
            }
            _ => return Ok(None),
        };
        let source_atom = if matches!(projection_kind, PendingProjectionKind::Atom) {
            let mut tokens = source.children_with_tokens().filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Identifier | SyntaxKind::Integer));
            let Some(token) = tokens.next() else { return Ok(None); };
            if tokens.next().is_some() { return Ok(None); }
            Some(crate::OwnedAtom { source: source.clone(), kind, spelling: token.text().to_owned(), range: crate::range_of_token(&token) })
        } else { None };
        let key = counters.source_nodes.get(source).cloned().ok_or(HirAvailabilityError::StructuralProjection)?;
        let index = nodes.len();
        index.checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
        nodes.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        nodes.push(PendingProjectionNode { kind: projection_kind, source_atom, range, key, children: Vec::new(), atom: None, staged_error: None, error: None, descendant_errors: 0 });
        if let Some(parent) = parent {
            let parent_node = nodes.get_mut(parent).ok_or(HirAvailabilityError::StructuralProjection)?;
            parent_node.children.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            parent_node.children.push(index);
        }
        for (child, child_source) in children.iter().zip(source_children).rev() {
            tasks.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            tasks.push((child, child_source, Some(index)));
        }
    }
    if nodes.is_empty() { return Ok(None); }

    // Preflight has fully accepted the source grammar before any operand is resolved.
    // Diagnostics are only staged here; `lower_plan` assigns dense IDs after the
    // existing duplicate-definition event at its established scheduling seam.
    for node in &mut nodes {
        if !matches!(node.kind, PendingProjectionKind::Atom) { continue; }
        let atom = node.source_atom.take().ok_or(HirAvailabilityError::StructuralProjection)?;
        let lowered = lower_leaf_with_identity(atom, namespace, counters, root_occurrence.clone(), scope, false)?;
        let SimpleChainLowering::Resolved { expression, semantic_error } = lowered else { return Ok(None); };
        node.staged_error = semantic_error;
        node.atom = Some(expression);
    }
    counters.pending_ordinary_admissions.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    counters.pending_ordinary_admissions.push(PendingOrdinaryAdmission { root: root_occurrence.clone(), owner_item_index, nodes });
    Ok(Some(ResolvedExpr::Error { occurrence: root_occurrence, errors: Vec::new().into_boxed_slice(), range: range_of(chain) }))
}

fn emit_ordinary_admission_errors(
    counters: &mut LoweringCounters,
    admission_start: usize,
    owner_item_index: usize,
    id: &Arc<DefId>,
    sink: &mut ErrorSink,
) -> Result<(), HirAvailabilityError> {
    let admissions = counters.pending_ordinary_admissions.get_mut(admission_start..)
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    for admission in admissions {
        if admission.owner_item_index != owner_item_index { return Err(HirAvailabilityError::StructuralProjection); }
        for node in &mut admission.nodes {
            let Some((kind, range)) = node.staged_error.take() else { continue; };
            node.error = Some(sink.lowering(kind, HirErrorAttachment::Value((**id).clone()), range)?);
        }
    }
    Ok(())
}

fn has_direct_comma_or_separator(source: &SyntaxNode) -> bool {
    source.children_with_tokens().any(|element| matches!(element.kind(), SyntaxKind::Comma | SyntaxKind::ExpressionDelimitedSeparator))
}

fn finalize_ordinary_admissions(
    items: &mut [HirItem],
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_ordinal: &mut u32,
) -> Result<(), HirAvailabilityError> {
    if counters.pending_ordinary_admissions.is_empty() {
        return Ok(());
    }
    let identity = counters.source_identity.as_mut().ok_or(HirAvailabilityError::StructuralProjection)?;
    for mut admission in counters.pending_ordinary_admissions.drain(..) {
        let node_count = admission.nodes.len();
        for index in (0..node_count).rev() {
            let child_errors = admission.nodes[index].children.iter().try_fold(0usize, |sum, child| {
                sum.checked_add(admission.nodes.get(*child)?.descendant_errors)
            }).ok_or(HirAvailabilityError::IdentityExhausted)?;
            let own_error = usize::from(admission.nodes[index].error.is_some());
            admission.nodes[index].descendant_errors = match admission.nodes[index].kind {
                PendingProjectionKind::Atom => own_error,
                PendingProjectionKind::Group => child_errors,
                PendingProjectionKind::Apply(_) => child_errors,
            };
        }

        let mut occurrences = Vec::new();
        occurrences.try_reserve_exact(node_count).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let mut stage = identity.empty_stage();
        let existing_root = validate_admission_root_mapping(identity, &admission.root, &admission.nodes[0].key)?;
        let staged_count = node_count.checked_sub(usize::from(existing_root.is_some()))
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        stage.occurrences.try_reserve(staged_count)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for (index, node) in admission.nodes.iter().enumerate() {
            let occurrence = if index == 0 {
                admission.root.clone()
            } else {
                next_occurrence(artifact, next_ordinal)?
            };
            if index != 0 || existing_root.is_none() {
                if !stage.record_unique_occurrence(occurrence.clone(), node.key.clone()) {
                    return Err(HirAvailabilityError::InconsistentIdentity);
                }
            }
            occurrences.push(occurrence);
        }

        let mut lowered: Vec<Option<ResolvedExpr>> = Vec::new();
        lowered.try_reserve_exact(node_count).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        lowered.resize_with(node_count, || None);
        for index in (0..node_count).rev() {
            let occurrence = occurrences[index].clone();
            let expression = match admission.nodes[index].kind {
                PendingProjectionKind::Atom => {
                    let mut expression = admission.nodes[index].atom.take()
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    set_expression_occurrence(&mut expression, occurrence)?;
                    expression
                }
                PendingProjectionKind::Group => {
                    let child = *admission.nodes[index].children.first()
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    if admission.nodes[index].children.len() != 1 {
                        return Err(HirAvailabilityError::StructuralProjection);
                    }
                    let inner = lowered.get_mut(child).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    ResolvedExpr::Group {
                        occurrence,
                        inner: try_box(inner)?,
                        range: admission.nodes[index].range.clone(),
                    }
                }
                PendingProjectionKind::Apply(source_form) => {
                    if admission.nodes[index].children.len() != 2 {
                        return Err(HirAvailabilityError::StructuralProjection);
                    }
                    let [callee_index, argument_index] = admission.nodes[index].children.as_slice() else {
                        return Err(HirAvailabilityError::StructuralProjection);
                    };
                    let count = admission.nodes[index].descendant_errors;
                    let bytes = count.checked_mul(std::mem::size_of::<HirErrorId>())
                        .ok_or(HirAvailabilityError::IdentityExhausted)?;
                    counters.aggregate_error_references = counters.aggregate_error_references
                        .checked_add(count).ok_or(HirAvailabilityError::IdentityExhausted)?;
                    counters.aggregate_error_reference_bytes = counters.aggregate_error_reference_bytes
                        .checked_add(bytes).ok_or(HirAvailabilityError::IdentityExhausted)?;
                    let callee_expr = lowered.get(*callee_index).and_then(Option::as_ref)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let argument_expr = lowered.get(*argument_index).and_then(Option::as_ref)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let errors = build_projection_error_list(
                        [(*callee_index, callee_expr), (*argument_index, argument_expr)],
                        &admission.nodes,
                        count,
                    )?;
                    let callee = lowered.get_mut(*callee_index).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    let argument = lowered.get_mut(*argument_index).and_then(Option::take)
                        .ok_or(HirAvailabilityError::StructuralProjection)?;
                    ResolvedExpr::Apply {
                        occurrence,
                        source_form,
                        callee: try_box(callee)?,
                        argument: try_box(argument)?,
                        errors,
                        range: admission.nodes[index].range.clone(),
                    }
                }
            };
            lowered[index] = Some(expression);
        }
        let root_expression = lowered.get_mut(0).and_then(Option::take)
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        let next_item_visits = counters.ordinary_admission_item_visits
            .checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
        let item = items.get_mut(admission.owner_item_index)
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        let HirItem::Binding(binding) = item else {
            return Err(HirAvailabilityError::StructuralProjection);
        };
        if !admission_root_placeholder_matches(&binding.value, &admission.root) {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        identity.append_stage(stage)?;
        replace_validated_admission_root(&mut binding.value, &admission.root, root_expression);
        counters.ordinary_admission_item_visits = next_item_visits;
        binding.evaluation_class = evaluation_class(&binding.value);
    }
    Ok(())
}

fn try_box<T>(value: T) -> Result<Box<T>, HirAvailabilityError> {
    let layout = Layout::new::<T>();
    if layout.size() == 0 {
        return Ok(Box::new(value));
    }
    let pointer = std::ptr::NonNull::new(unsafe { alloc(layout).cast::<T>() })
        .ok_or(HirAvailabilityError::IdentityExhausted)?;
    // SAFETY: `pointer` is a unique allocation from the global allocator with
    // exactly `layout`; it is initialized once and transferred to `Box`.
    unsafe {
        pointer.as_ptr().write(value);
        Ok(Box::from_raw(pointer.as_ptr()))
    }
}

fn validate_admission_root_mapping<'a>(
    identity: &'a crate::source_identity::HirSourceIdentity,
    root: &HirOccurrenceId,
    key: &yu_syntax::SourceNodeKey,
) -> Result<Option<&'a yu_syntax::SourceNodeKey>, HirAvailabilityError> {
    match identity.occurrences.get(root) {
        Some(existing) if existing != key => Err(HirAvailabilityError::InconsistentIdentity),
        existing => Ok(existing),
    }
}

fn build_projection_error_list(
    children: [(usize, &ResolvedExpr); 2],
    nodes: &[PendingProjectionNode],
    expected: usize,
) -> Result<Box<[HirErrorId]>, HirAvailabilityError> {
    if expected == 0 { return Ok(Box::new([])); }
    let layout = Layout::array::<HirErrorId>(expected)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    let raw = unsafe { alloc(layout).cast::<HirErrorId>() };
    if raw.is_null() { return Err(HirAvailabilityError::IdentityExhausted); }
    let mut written = 0usize;
    let result = children.into_iter().try_for_each(|(index, expr)| {
        append_projection_errors(index, expr, nodes, raw, expected, &mut written)
    });
    if result.is_err() || written != expected {
        // HirErrorId is Copy and no value owns a destructor in this raw buffer.
        unsafe { std::alloc::dealloc(raw.cast(), layout); }
        return result.and(Err(HirAvailabilityError::StructuralProjection));
    }
    // SAFETY: every slot in the exact-sized allocation has been initialized by
    // append_projection_errors, and Box now owns the matching global allocation.
    Ok(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(raw, expected)) })
}

fn append_projection_errors(
    root: usize,
    expression: &ResolvedExpr,
    nodes: &[PendingProjectionNode],
    output: *mut HirErrorId,
    capacity: usize,
    written: &mut usize,
) -> Result<(), HirAvailabilityError> {
    let node = nodes.get(root).ok_or(HirAvailabilityError::StructuralProjection)?;
    match (&node.kind, expression) {
        (PendingProjectionKind::Atom, ResolvedExpr::Integer { .. } | ResolvedExpr::Name { .. }) => {
            if let Some(error) = node.error {
                if *written >= capacity { return Err(HirAvailabilityError::StructuralProjection); }
                unsafe { output.add(*written).write(error); }
                *written = written.checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
            }
        }
        (PendingProjectionKind::Group, ResolvedExpr::Group { inner, .. }) => {
            let [child] = node.children.as_slice() else { return Err(HirAvailabilityError::StructuralProjection); };
            append_projection_errors(*child, inner.as_ref(), nodes, output, capacity, written)?;
        }
        (PendingProjectionKind::Apply(_), ResolvedExpr::Apply { errors, .. }) => {
            let end = written.checked_add(errors.len()).ok_or(HirAvailabilityError::IdentityExhausted)?;
            if end > capacity { return Err(HirAvailabilityError::StructuralProjection); }
            unsafe { std::ptr::copy_nonoverlapping(errors.as_ptr(), output.add(*written), errors.len()); }
            *written = end;
        }
        _ => return Err(HirAvailabilityError::StructuralProjection),
    }
    Ok(())
}

fn set_expression_occurrence(
    expression: &mut ResolvedExpr,
    occurrence: HirOccurrenceId,
) -> Result<(), HirAvailabilityError> {
    match expression {
        ResolvedExpr::Integer { occurrence: current, .. }
        | ResolvedExpr::Name { occurrence: current, .. } => *current = occurrence,
        _ => return Err(HirAvailabilityError::StructuralProjection),
    }
    Ok(())
}

fn replace_admission_root(
    expression: &mut ResolvedExpr,
    target: &HirOccurrenceId,
    replacement: &mut Option<ResolvedExpr>,
) -> Result<bool, HirAvailabilityError> {
    let mut current = expression;
    loop {
        if current.occurrence() == target {
            if matches!(current, ResolvedExpr::Error { errors, .. } if errors.is_empty()) {
                *current = replacement.take().ok_or(HirAvailabilityError::StructuralProjection)?;
                return Ok(true);
            }
            return Ok(false);
        }
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            _ => return Ok(false),
        }
    }
}

fn admission_root_placeholder_matches(
    expression: &ResolvedExpr,
    target: &HirOccurrenceId,
) -> bool {
    let mut current = expression;
    loop {
        if current.occurrence() == target {
            return matches!(current, ResolvedExpr::Error { errors, .. } if errors.is_empty());
        }
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            _ => return false,
        }
    }
}

fn replace_validated_admission_root(
    expression: &mut ResolvedExpr,
    target: &HirOccurrenceId,
    replacement: ResolvedExpr,
) {
    let mut current = expression;
    loop {
        if current.occurrence() == target {
            *current = replacement;
            return;
        }
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            _ => unreachable!("validated admission root path changed"),
        }
    }
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
    parameters: Vec<AdmittedParameter>,
}

#[derive(Clone)]
struct AdmittedParameter {
    name: HirName,
    source: Option<yu_syntax::SourceNodeKey>,
    annotation: Option<SyntaxNode>,
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
    let Some((visibility, name, parameters)) = plain_binding_header(&node, counters) else {
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
            parameters,
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
                next_occurrence_ordinal,
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
    #[cfg(any(feature = "shadow", test))]
    if (counters.shadow_applications || counters.local_source) && admitted.parameters.len() > 127 {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    let mut parameters = Vec::with_capacity(admitted.parameters.len());
    for (ordinal, admitted) in admitted.parameters.iter().enumerate() {
        let ordinal =
            u32::try_from(ordinal).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let parameter = HirParameter {
            id: HirParameterId::new(definition_root.clone(), ordinal),
            name: admitted.name.clone(),
            range: admitted.name.range.clone(),
        };
        if let (Some(source), Some(key)) = (&mut counters.source_identity, &admitted.source) {
            source.record_parameter(parameter.id.clone(), key.clone());
        }
        parameters.push(parameter);
    }
    let parameters = parameters.into_boxed_slice();
    #[cfg(any(feature = "shadow", test))]
    let simple_body_projection = if counters.local_source {
        let (carrier, projection) = local_source::form(
            plan,
            &SourceRootId::Definition(definition_root.clone()),
            &parameters,
            namespace,
            counters,
            artifact,
            next_occurrence_ordinal,
        )?;
        counters
            .local_sources
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        counters
            .local_sources
            .insert(definition_root.clone(), carrier);
        Some(projection)
    } else {
        None
    };
    let mut lambda_occurrences = Vec::with_capacity(parameters.len());
    for ordinal in 0..parameters.len() {
        lambda_occurrences.push(if ordinal == 0 {
            occurrence.clone()
        } else {
            next_occurrence(artifact, next_occurrence_ordinal)?
        });
    }
    let body_occurrence = if parameters.is_empty() {
        occurrence
    } else {
        next_occurrence(artifact, next_occurrence_ordinal)?
    };
    let guard = scope.root_guard();
    for parameter in &parameters {
        scope.push_parameter(parameter.clone());
    }
    let owner_item_index = usize::try_from(plan.ordinal)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    let admission_start = counters.pending_ordinary_admissions.len();
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
        next_occurrence_ordinal,
        128 - parameters.len(),
        #[cfg(any(feature = "shadow", test))]
        simple_body_projection,
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
    emit_ordinary_admission_errors(counters, admission_start, owner_item_index, &id, sink)?;
    if let Some((kind, range)) = body_semantic_error {
        sink.lowering(kind, HirErrorAttachment::Value((*id).clone()), range)?;
    }
    let mut value = value;
    for (parameter, occurrence) in parameters.iter().zip(lambda_occurrences).rev() {
        value = ResolvedExpr::Lambda {
            occurrence,
            parameter: parameter.id.clone(),
            range: plan.range.clone(),
            body: Box::new(value),
        };
    }
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
    _next_occurrence_ordinal: &mut u32,
) -> Result<HirItem, HirAvailabilityError> {
    if !causal_errors.is_empty() {
        return Ok(HirItem::Expression(ResolvedExpr::Error {
            occurrence,
            errors: causal_errors.into_boxed_slice(),
            range: plan.range.clone(),
        }));
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.shadow_applications {
        if let Some(expression) = lower_shadow_application(
            parsed,
            &plan.node,
            namespace,
            counters,
            occurrence.clone(),
            scope,
            _next_occurrence_ordinal,
            sink,
            HirErrorAttachment::DirectRootItem(plan.ordinal),
            128,
        )? {
            return Ok(HirItem::Expression(expression));
        }
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
    _next_occurrence_ordinal: &mut u32,
    _body_depth_budget: usize,
    #[cfg(any(feature = "shadow", test))]
    simple_body_projection: Option<local_source::SimpleBodyProjection>,
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
    if counters.ordinary_source_carriers {
        let owner_item_index = usize::try_from(plan.ordinal)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        if let Some(expression) = lower_ordinary_admission(
            parsed,
            chain,
            namespace,
            &causal_errors,
            counters,
            occurrence.clone(),
            owner_item_index,
            scope,
        )? {
            return Ok((expression, None));
        }
    }
    #[cfg(any(feature = "shadow", test))]
    if counters.shadow_applications {
        if let Some(expression) = lower_shadow_application(
            parsed,
            chain,
            namespace,
            counters,
            occurrence.clone(),
            scope,
            _next_occurrence_ordinal,
            sink,
            HirErrorAttachment::Value(id.clone()),
            _body_depth_budget,
        )? {
            return Ok((expression, None));
        }
    }
    #[cfg(any(feature = "shadow", test))]
    let lowered = match simple_body_projection {
        Some(local_source::SimpleBodyProjection::Atom(atom)) => {
            lower_leaf(atom, namespace, counters, occurrence.clone(), scope)?
        }
        Some(local_source::SimpleBodyProjection::Unsupported) => {
            SimpleChainLowering::Unsupported {
                range: range_of(chain),
            }
        }
        None => lower_simple_chain(
            parsed,
            chain,
            namespace,
            counters,
            occurrence.clone(),
            scope,
        )?,
    };
    #[cfg(not(any(feature = "shadow", test)))]
    let lowered = lower_simple_chain(
        parsed,
        chain,
        namespace,
        counters,
        occurrence.clone(),
        scope,
    )?;
    match lowered {
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

#[cfg(any(feature = "shadow", test))]
fn lower_shadow_application(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    next_occurrence_ordinal: &mut u32,
    sink: &mut ErrorSink,
    attachment: HirErrorAttachment,
    depth_budget: usize,
) -> Result<Option<ResolvedExpr>, HirAvailabilityError> {
    // Preflight the whole bounded tree before publishing occurrences or errors.
    let Some(plan) = shadow_application_plan(parsed, chain, true)? else {
        return Ok(None);
    };
    if plan.height > depth_budget {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    lower_shadow_application_plan(
        parsed,
        plan,
        namespace,
        counters,
        occurrence,
        scope,
        next_occurrence_ordinal,
        sink,
        attachment,
    )
    .map(Some)
}

#[cfg(any(feature = "shadow", test))]
struct ShadowApplicationPlan {
    height: usize,
    callee: SyntaxNode,
    tail: SyntaxNode,
    argument: SyntaxNode,
    nested: Option<Box<ShadowApplicationPlan>>,
    nested_callee: Option<Box<ShadowApplicationPlan>>,
    grouped: bool,
    range: Range<usize>,
}

#[cfg(any(feature = "shadow", test))]
fn shadow_application_plan(
    parsed: &ParsedFile,
    chain: &SyntaxNode,
    allow_nested: bool,
) -> Result<Option<ShadowApplicationPlan>, HirAvailabilityError> {
    let associated = associate_chain_owned(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => {
                HirAvailabilityError::ExactOperatorEnvironment
            }
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?
        .into_hir();
    let HirExpr::Value {
        kind: source_form,
        children: operands,
        range,
    } = associated
    else {
        return Ok(None);
    };
    if !matches!(source_form, SyntaxKind::MlArgument | SyntaxKind::CallTail) {
        return Ok(None);
    }
    let [callee_shape, argument_shape] = operands.as_slice() else {
        return Ok(None);
    };
    let leaf = |shape: &HirExpr| matches!(shape, HirExpr::Value { kind: SyntaxKind::IdentifierExpression | SyntaxKind::IntegerLiteral, children, .. } if children.is_empty());
    let children = chain.children().collect::<Vec<_>>();
    if allow_nested && source_form == SyntaxKind::MlArgument && leaf(argument_shape) {
        if let (
            HirExpr::Value {
                kind: SyntaxKind::MlArgument,
                children: inner,
                range: inner_range,
            },
            [head, first_tail, second_tail],
        ) = (callee_shape, children.as_slice())
        {
            if let [first_callee, first_argument] = inner.as_slice() {
                if leaf(first_callee)
                    && leaf(first_argument)
                    && range_of(head) == *first_callee.range()
                    && first_tail.kind() == SyntaxKind::MlArgument
                    && second_tail.kind() == SyntaxKind::MlArgument
                {
                    let operand_node = |tail: &SyntaxNode, shape: &HirExpr| {
                        let HirExpr::Value { kind, .. } = shape else {
                            return None;
                        };
                        let nodes = tail
                            .descendants()
                            .filter(|node| node.kind() == *kind && range_of(node) == *shape.range())
                            .collect::<Vec<_>>();
                        match nodes.as_slice() {
                            [node] => Some(node.clone()),
                            _ => None,
                        }
                    };
                    if let (Some(first_argument), Some(argument)) = (
                        operand_node(first_tail, first_argument),
                        operand_node(second_tail, argument_shape),
                    ) {
                        return Ok(Some(ShadowApplicationPlan {
                            height: 3,
                            callee: head.clone(),
                            tail: second_tail.clone(),
                            argument,
                            nested: None,
                            grouped: false,
                            range,
                            nested_callee: Some(Box::new(ShadowApplicationPlan {
                                height: 2,
                                callee: head.clone(),
                                tail: first_tail.clone(),
                                argument: first_argument,
                                nested: None,
                                nested_callee: None,
                                grouped: false,
                                range: inner_range.clone(),
                            })),
                        }));
                    }
                }
            }
        }
    }
    if !leaf(callee_shape) {
        return Ok(None);
    }
    let [callee_node, tail] = children.as_slice() else {
        return Ok(None);
    };
    if tail.kind() != source_form || range_of(callee_node) != *callee_shape.range() {
        return Ok(None);
    }
    let grouped = allow_nested
        && source_form == SyntaxKind::MlArgument
        && matches!(argument_shape, HirExpr::Value { kind: SyntaxKind::ParenthesizedExpression, children, .. }
            if matches!(children.as_slice(), [HirExpr::Value { kind: SyntaxKind::MlArgument | SyntaxKind::CallTail, .. }]));
    let argument_kind = if grouped {
        SyntaxKind::ParenthesizedExpression
    } else if leaf(argument_shape) {
        match argument_shape {
            HirExpr::Value { kind, .. } => *kind,
            _ => unreachable!(),
        }
    } else if allow_nested
        && source_form == SyntaxKind::CallTail
        && matches!(
            argument_shape,
            HirExpr::Value {
                kind: SyntaxKind::MlArgument | SyntaxKind::CallTail,
                ..
            }
        )
    {
        SyntaxKind::OperatorChain
    } else {
        return Ok(None);
    };
    let argument_nodes = tail
        .descendants()
        .filter(|node| node.kind() == argument_kind && range_of(node) == *argument_shape.range())
        .collect::<Vec<_>>();
    let [argument_node] = argument_nodes.as_slice() else {
        return Ok(None);
    };
    // Association retains element expressions but omits tuple punctuation.
    // A direct trailing comma still makes a one-tuple, rather than a Group.
    if grouped
        && argument_node.children_with_tokens().any(|element| {
            element
                .into_token()
                .is_some_and(|token| token.kind() == SyntaxKind::Comma)
        })
    {
        return Ok(None);
    }
    let nested = if grouped || argument_kind == SyntaxKind::OperatorChain {
        let nested_chain = if grouped {
            let mut stack = argument_node.children().collect::<Vec<_>>();
            let mut chains = Vec::new();
            while let Some(node) = stack.pop() {
                if node.kind() == SyntaxKind::OperatorChain {
                    chains.push(node);
                } else {
                    stack.extend(node.children());
                }
            }
            let [chain] = chains.as_slice() else {
                return Ok(None);
            };
            chain.clone()
        } else {
            argument_node.clone()
        };
        let Some(plan) = shadow_application_plan(parsed, &nested_chain, false)? else {
            return Ok(None);
        };
        Some(Box::new(plan))
    } else {
        None
    };
    let argument_height = nested.as_ref().map_or(1, |plan| plan.height);
    let height = 1 + argument_height + usize::from(grouped);
    Ok(Some(ShadowApplicationPlan {
        height,
        callee: callee_node.clone(),
        tail: tail.clone(),
        argument: argument_node.clone(),
        nested,
        nested_callee: None,
        grouped,
        range,
    }))
}

#[cfg(any(feature = "shadow", test))]
fn lower_shadow_application_plan(
    parsed: &ParsedFile,
    plan: ShadowApplicationPlan,
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    next_occurrence_ordinal: &mut u32,
    sink: &mut ErrorSink,
    attachment: HirErrorAttachment,
) -> Result<ResolvedExpr, HirAvailabilityError> {
    let ShadowApplicationPlan {
        height: _,
        callee: callee_node,
        tail,
        argument: argument_node,
        nested,
        nested_callee,
        grouped,
        range,
    } = plan;
    let source_form = tail.kind();
    let Some(key) = counters.source_nodes.get(&tail).cloned() else {
        return Err(HirAvailabilityError::StructuralProjection);
    };
    let mut errors = vec![sink.lowering(
        HirErrorKind::UnsupportedExpression,
        attachment.clone(),
        range.clone(),
    )?];
    let computed_callee = if let Some(plan) = nested_callee {
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let callee = lower_shadow_application_plan(
            parsed,
            *plan,
            namespace,
            counters,
            child_occurrence,
            scope,
            next_occurrence_ordinal,
            sink,
            attachment.clone(),
        )?;
        if let ResolvedExpr::Apply {
            errors: nested_errors,
            ..
        } = &callee
        {
            errors.extend(nested_errors.iter().copied());
        }
        Some(callee)
    } else {
        None
    };
    let mut lower_operand = |node: &SyntaxNode| -> Result<ResolvedExpr, HirAvailabilityError> {
        let mut tokens = node
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(token.kind(), SyntaxKind::Identifier | SyntaxKind::Integer));
        let token = tokens
            .next()
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        if tokens.next().is_some() {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let atom = crate::OwnedAtom {
            source: node.clone(),
            kind: node.kind(),
            spelling: token.text().to_owned(),
            range: crate::range_of_token(&token),
        };
        let SimpleChainLowering::Resolved {
            expression,
            semantic_error,
        } = lower_leaf(atom, namespace, counters, child_occurrence, scope)?
        else {
            return Err(HirAvailabilityError::StructuralProjection);
        };
        if let Some((kind, range)) = semantic_error {
            errors.push(sink.lowering(kind, attachment.clone(), range)?);
        }
        Ok(expression)
    };
    let callee = match computed_callee {
        Some(callee) => callee,
        None => lower_operand(&callee_node)?,
    };
    let argument = if let Some(nested) = nested {
        let child_occurrence = next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?;
        let nested_occurrence = if grouped {
            next_occurrence(&occurrence.artifact, next_occurrence_ordinal)?
        } else {
            child_occurrence.clone()
        };
        let argument = lower_shadow_application_plan(
            parsed,
            *nested,
            namespace,
            counters,
            nested_occurrence,
            scope,
            next_occurrence_ordinal,
            sink,
            attachment,
        )?;
        if let ResolvedExpr::Apply {
            errors: nested_errors,
            ..
        } = &argument
        {
            errors.extend(nested_errors.iter().copied());
        }
        if grouped {
            let key = counters
                .source_nodes
                .get(&argument_node)
                .ok_or(HirAvailabilityError::StructuralProjection)?
                .clone();
            counters
                .source_identity
                .as_mut()
                .expect("shadow route retains source identity")
                .record_occurrence(child_occurrence.clone(), key);
            ResolvedExpr::Group {
                occurrence: child_occurrence,
                inner: Box::new(argument),
                range: range_of(&argument_node),
            }
        } else {
            argument
        }
    } else {
        lower_operand(&argument_node)?
    };
    counters
        .source_identity
        .as_mut()
        .expect("shadow route retains source identity")
        .record_occurrence(occurrence.clone(), key);
    Ok(ResolvedExpr::Apply {
        occurrence,
        source_form,
        callee: Box::new(callee),
        argument: Box::new(argument),
        errors: errors.into_boxed_slice(),
        range,
    })
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
            AssociationError::Allocation => HirAvailabilityError::IdentityExhausted,
        })?
        .into_parts();
    let Some(atom) = atom else {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    };
    if !matches!(expression, HirExpr::Value { children, .. } if children.is_empty()) {
        return Ok(SimpleChainLowering::Unsupported { range: chain_range });
    }
    lower_leaf(atom, namespace, counters, occurrence, scope)
}

fn lower_leaf(
    atom: crate::OwnedAtom,
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    lower_leaf_with_identity(atom, namespace, counters, occurrence, scope, true)
}

fn lower_leaf_with_identity(
    atom: crate::OwnedAtom,
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    occurrence: HirOccurrenceId,
    scope: &ScopeStack,
    record_identity: bool,
) -> Result<SimpleChainLowering, HirAvailabilityError> {
    if record_identity {
        if let Some(source) = &mut counters.source_identity {
        if let Some(key) = counters.source_nodes.get(&atom.source) {
            source.record_occurrence(occurrence.clone(), key.clone());
        }
        }
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

fn plain_binding_header(
    node: &SyntaxNode,
    _counters: &LoweringCounters,
) -> Option<(HirVisibility, HirName, Vec<AdmittedParameter>)> {
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
    let pattern_children = target
        .children()
        .filter(|_child| {
            if _counters.local_source && _child.kind() == SyntaxKind::PatternTypeAnnotation {
                return false;
            }
            true
        })
        .collect::<Vec<_>>();
    let (head, tails) = pattern_children.split_first()?;
    let head = identifier_pattern_name(head)?;
    let multiple_parameters = _counters.shadow_applications || _counters.local_source;
    if tails.len() > 1 && !multiple_parameters {
        return None;
    }
    let mut parameters = Vec::with_capacity(tails.len());
    for tail in tails {
        if _counters.local_source && tail.kind() == SyntaxKind::PatternCallTail {
            if tails.len() != 1 || has_recovery(tail) {
                return None;
            }
            let arguments = tail.children().collect::<Vec<_>>();
            let [argument] = arguments.as_slice() else {
                return None;
            };
            if argument.kind() != SyntaxKind::Pattern || has_recovery(argument) {
                return None;
            }
            let children = argument.children().collect::<Vec<_>>();
            let (identifier, annotation) = match children.as_slice() {
                [identifier] => (identifier, None),
                [identifier, annotation]
                    if annotation.kind() == SyntaxKind::PatternTypeAnnotation =>
                {
                    (identifier, Some(annotation.clone()))
                }
                _ => return None,
            };
            parameters.push(AdmittedParameter {
                name: identifier_pattern_name(identifier)?,
                source: _counters.source_nodes.get(identifier).cloned(),
                annotation,
            });
            continue;
        }
        if tail.kind() != SyntaxKind::PatternMlApplicationTail || has_recovery(tail) {
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
        let (argument, annotation) =
            if _counters.local_source && argument.kind() == SyntaxKind::ParenthesizedPattern {
                if argument
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| {
                        !matches!(
                            token.kind(),
                            SyntaxKind::LParen
                                | SyntaxKind::RParen
                                | SyntaxKind::Whitespace
                                | SyntaxKind::Newline
                                | SyntaxKind::LineComment
                                | SyntaxKind::BlockComment
                        )
                    })
                {
                    return None;
                }
                let children = argument.children().collect::<Vec<_>>();
                let [pattern] = children.as_slice() else {
                    return None;
                };
                if pattern.kind() != SyntaxKind::Pattern {
                    return None;
                }
                let children = pattern.children().collect::<Vec<_>>();
                let [identifier, annotation] = children.as_slice() else {
                    return None;
                };
                if annotation.kind() != SyntaxKind::PatternTypeAnnotation {
                    return None;
                }
                (identifier.clone(), Some(annotation.clone()))
            } else {
                ((*argument).clone(), None)
            };
        parameters.push(AdmittedParameter {
            name: identifier_pattern_name(&argument)?,
            source: _counters.source_nodes.get(&argument).cloned(),
            annotation,
        });
    }
    Some((visibility, head, parameters))
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
        self.errors.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        if diagnostic {
            self.diagnostics.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        }
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
    fn admission_root_collision_is_rejected_without_overwriting_or_publishing() {
        let parsed = parsed("my first = 1; my second = 2");
        let roots: Vec<_> = parsed.source_root().children().collect();
        let original_key = roots[0].key();
        let conflicting_key = roots[1].key();
        let artifact = mint_artifact_token();
        let mut ordinal = 0;
        let root = next_occurrence(&artifact, &mut ordinal).unwrap();
        let mut source = crate::source_identity::HirSourceIdentity::new(&parsed);
        source.record_occurrence(root.clone(), original_key.clone());

        assert_eq!(
            validate_admission_root_mapping(&source, &root, &conflicting_key),
            Err(HirAvailabilityError::InconsistentIdentity),
        );
        assert_eq!(source.occurrences.get(&root), Some(&original_key));

        let mut stage = source.empty_stage();
        stage.record_unique_occurrence(root.clone(), conflicting_key);
        assert_eq!(
            source.append_stage(stage),
            Err(HirAvailabilityError::StructuralProjection),
        );
        assert_eq!(source.occurrences.get(&root), Some(&original_key));
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
            &parsed("my x = 1; my y = x; my f p = p; my missing = nope; my bad = @; my app = f 1; my group = (1); my lambda_app p = p 1; my lambda_plain p = p"),
            SemanticImports::empty(),
        )
        .expect("lowering remains available");
        let bindings: Vec<_> = module.items().iter().filter_map(|item| match item { HirItem::Binding(binding) => Some(binding), _ => None }).collect();
        assert_eq!(bindings.len(), 9);
        let [x, y, f, missing, bad, app, group, lambda_app, lambda_plain] = bindings.as_slice() else { panic!("nine bindings") };
        assert_eq!(x.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(y.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(f.evaluation_class, Some(EvaluationClass::FetchValue));
        assert_eq!(missing.evaluation_class, None);
        assert_eq!(bad.evaluation_class, None);
        assert_eq!(app.evaluation_class, None);
        assert_eq!(group.evaluation_class, None);
        assert_eq!(lambda_app.evaluation_class, None);
        assert_eq!(lambda_plain.evaluation_class, Some(EvaluationClass::FetchValue));
    }

    #[test]
    fn many_simple_admissions_finalize_at_their_exact_item_indices() {
        let count = 64usize;
        let source = (0..count).map(|index| format!("my v{index} = {index}")).collect::<Vec<_>>().join("; ");
        let parsed = parsed(&source);
        let mut counters = LoweringCounters::default();
        counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(&parsed));
        counters.source_nodes = crate::source_identity::try_source_keys(&parsed).unwrap();
        counters.ordinary_source_carriers = true;
        let module = lower_module_with_counters(identity(), &parsed, SemanticImports::empty(), &mut counters).unwrap();
        assert_eq!(module.items().len(), count);
        assert_eq!(counters.ordinary_admission_item_visits, count,
            "one indexed owning-item access per admitted body, independent of module length");
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

#[cfg(any(feature = "shadow", test))]
pub(crate) fn retain_shadow_local_binding(
    mut hir: HirModule,
    artifact: &crate::shadow::ShadowArtifact,
) -> Result<HirModule, HirAvailabilityError> {
    use crate::shadow::Form;
    let invalid = || HirAvailabilityError::StructuralProjection;
    let (root, _) = hir.captured_source.as_ref().ok_or_else(invalid)?;
    let binding = hir
        .items
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.definition_root() == root => Some(binding),
            _ => None,
        })
        .ok_or_else(invalid)?;
    let declaration = artifact
        .definition_source_position(&hir, root)
        .map_err(|_| invalid())?;
    let skeleton = artifact
        .declaration_skeleton(&declaration)
        .map_err(|_| invalid())?;
    let input = skeleton.captured_call_input().ok_or_else(invalid)?;
    let ResolvedExpr::Lambda {
        parameter: outer,
        body: old_body,
        ..
    } = &binding.value
    else {
        return Err(invalid());
    };
    let errors = match old_body.as_ref() {
        ResolvedExpr::Error { errors, .. } => errors.clone(),
        _ => return Err(invalid()),
    };
    let local = HirLocalId {
        owner: SourceRootId::Definition(binding.definition_root.clone()),
        ordinal: u32::try_from(0usize).map_err(|_| invalid())?,
    };
    let x = HirParameterId::new(
        binding.definition_root.clone(),
        u32::try_from(binding.parameters.len()).map_err(|_| invalid())?,
    );
    let root = skeleton
        .expression(skeleton.body())
        .map_err(|_| invalid())?;
    let Form::Lambda { body: bind_id, .. } = root.form() else {
        return Err(invalid());
    };
    let bound = skeleton.expression(bind_id).map_err(|_| invalid())?;
    let Form::Bind {
        value,
        body: returned,
        ..
    } = bound.form()
    else {
        return Err(invalid());
    };
    let lambda = skeleton.expression(value).map_err(|_| invalid())?;
    let Form::Lambda {
        parameter,
        body: call_id,
        ..
    } = lambda.form()
    else {
        return Err(invalid());
    };
    let call = skeleton.expression(call_id).map_err(|_| invalid())?;
    let Form::Apply {
        source_form,
        callee,
        argument,
    } = call.form()
    else {
        return Err(invalid());
    };
    let mut pending = Vec::new();
    for item in &hir.items {
        match item {
            HirItem::Binding(binding) => pending.push(&binding.value),
            HirItem::Expression(expression) => pending.push(expression),
            HirItem::Error { .. } => {}
        }
    }
    let mut maximum = None;
    while let Some(expression) = pending.pop() {
        maximum = Some(
            maximum.map_or(expression.occurrence().ordinal(), |current: u32| {
                current.max(expression.occurrence().ordinal())
            }),
        );
        match expression {
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                pending.push(argument);
                pending.push(callee);
            }
            ResolvedExpr::Lambda { body, .. } => pending.push(body),
            ResolvedExpr::Group { inner, .. } => pending.push(inner),
            ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name { .. }
            | ResolvedExpr::Error { .. } => {}
        }
    }
    let retained_maximum = hir
        .source_identity
        .as_ref()
        .and_then(|source| source.maximum_occurrence_ordinal());
    let mut next = maximum
        .into_iter()
        .chain(retained_maximum)
        .max()
        .ok_or_else(invalid)?
        .checked_add(1)
        .ok_or_else(invalid)?;
    // Identity minting stays in HIR. Each exact-position crosswalk is checked
    // before the candidate tree can escape this cold opt-in constructor.
    let mut source = hir.source_identity.clone().ok_or_else(invalid)?;
    let mut occurrence =
        |expression: &crate::shadow::Expression| -> Result<HirOccurrenceId, HirAvailabilityError> {
            let id = HirOccurrenceId::new(hir.artifact.clone(), next);
            next = next.checked_add(1).ok_or_else(invalid)?;
            if !source.record_unique_occurrence(
                id.clone(),
                artifact
                    .exact_source_key(expression.position())
                    .map_err(|_| invalid())?,
            ) {
                return Err(invalid());
            }
            Ok(id)
        };
    let mut name = |id: &crate::shadow::ExprId,
                    resolution: NameResolution|
     -> Result<ResolvedExpr, HirAvailabilityError> {
        let expression = skeleton.expression(id).map_err(|_| invalid())?;
        let Form::Use { binder, .. } = expression.form() else {
            return Err(invalid());
        };
        let binder = skeleton.binder(binder).map_err(|_| invalid())?;
        Ok(ResolvedExpr::Name {
            occurrence: occurrence(expression)?,
            name: HirName {
                spelling: binder.name().to_owned(),
                range: expression.range().clone(),
            },
            resolution,
            range: expression.range().clone(),
        })
    };
    let callee = name(callee, NameResolution::Parameter(outer.clone()))?;
    let argument = name(argument, NameResolution::Parameter(x.clone()))?;
    let returned = skeleton.expression(returned).map_err(|_| invalid())?;
    let continuation = crate::shadow::ShadowLocalUse {
        occurrence: occurrence(returned)?,
        local: local.clone(),
        range: returned.range().clone(),
    };
    let apply = ResolvedExpr::Apply {
        occurrence: occurrence(call)?,
        source_form: *source_form,
        callee: Box::new(callee),
        argument: Box::new(argument),
        errors,
        range: call.range().clone(),
    };
    let initializer = ResolvedExpr::Lambda {
        occurrence: occurrence(lambda)?,
        parameter: x.clone(),
        body: Box::new(apply),
        range: lambda.range().clone(),
    };
    let body = crate::shadow::ShadowLocalBind {
        occurrence: occurrence(bound)?,
        local: local.clone(),
        initializer,
        continuation,
        captures: vec![outer.clone()].into_boxed_slice(),
        range: bound.range().clone(),
    };
    source.record_parameter(
        x.clone(),
        artifact
            .exact_source_key(
                skeleton
                    .binder(parameter)
                    .map_err(|_| invalid())?
                    .position(),
            )
            .map_err(|_| invalid())?,
    );
    source.record_local(
        local.clone(),
        artifact
            .exact_source_key(
                skeleton
                    .binder(input.local_binding())
                    .map_err(|_| invalid())?
                    .position(),
            )
            .map_err(|_| invalid())?,
    );
    source.local_parameter_owners.insert(x, local);
    source.local_binding = Some(body);
    hir.source_identity = Some(source);
    Ok(hir)
}
