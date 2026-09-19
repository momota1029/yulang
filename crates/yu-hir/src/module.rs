use std::{collections::HashMap, ops::Range};

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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HirVisibility {
    Private,
    Our,
    Public,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NameResolution {
    Resolved(DefId),
    Ambiguous,
    Unresolved,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedExpr {
    Integer {
        spelling: String,
        range: Range<usize>,
    },
    Name {
        name: HirName,
        resolution: NameResolution,
        range: Range<usize>,
    },
    Error {
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

impl ResolvedExpr {
    pub fn range(&self) -> &Range<usize> {
        match self {
            Self::Integer { range, .. } | Self::Name { range, .. } | Self::Error { range, .. } => {
                range
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirBinding {
    id: DefId,
    visibility: HirVisibility,
    name: HirName,
    value: ResolvedExpr,
    range: Range<usize>,
}

impl HirBinding {
    pub fn id(&self) -> &DefId {
        &self.id
    }
    pub fn visibility(&self) -> HirVisibility {
        self.visibility
    }
    pub fn name(&self) -> &HirName {
        &self.name
    }
    pub fn value(&self) -> &ResolvedExpr {
        &self.value
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirItem {
    Binding(HirBinding),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirModule {
    identity: ModuleIdentity,
    source_revision: SourceRevision,
    items: Vec<HirItem>,
    errors: Vec<HirError>,
    diagnostics: Vec<HirDiagnostic>,
}

impl HirModule {
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirAvailabilityError {
    InconsistentIdentity,
    StructuralProjection,
    ExactOperatorEnvironment,
    IdentityExhausted,
}

/// Lowers direct-root ordinary bindings against one complete local namespace.
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

    let mut items = Vec::with_capacity(plans.len());
    for (plan, errors) in plans.iter().zip(root_errors) {
        items.push(lower_plan(
            plan,
            parsed,
            &namespace,
            errors.item,
            errors.value,
            &mut sink,
            counters,
        )?);
    }
    Ok(HirModule {
        identity,
        source_revision: parsed.revision(),
        items,
        errors: sink.errors,
        diagnostics: sink.diagnostics,
    })
}

#[derive(Default)]
struct LoweringCounters {
    recovery_visits: usize,
    syntax_emissions: usize,
    copied_spelling_bytes: usize,
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
    admitted: Option<Admitted>,
    failure: Option<HirErrorKind>,
}

#[derive(Clone)]
struct Admitted {
    id: DefId,
    visibility: HirVisibility,
    name: HirName,
}

impl RootPlan {
    fn recovery_attachment(&self, recovery: &StructuralRecovery) -> HirErrorAttachment {
        let Some(admitted) = &self.admitted else {
            return HirErrorAttachment::DirectRootItem(self.ordinal);
        };
        if recovery.path().contains(&SyntaxKind::BindingBody) {
            HirErrorAttachment::Value(admitted.id.clone())
        } else {
            HirErrorAttachment::Definition(admitted.id.clone())
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
    if node.kind() != SyntaxKind::BindingStatement {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            admitted: None,
            failure: Some(HirErrorKind::UnsupportedItem),
        });
    }
    let Some((visibility, name)) = plain_binding_header(&node) else {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            admitted: None,
            failure: Some(HirErrorKind::UnsupportedTarget),
        });
    };
    counters.copied_spelling_bytes += name.spelling.len();
    let same_name_ordinal = 0; // assigned after all direct-root headers are known
    let id = DefId {
        module: identity.module.clone(),
        spelling: name.spelling.clone().into_boxed_str(),
        same_name_ordinal,
    };
    Ok(RootPlan {
        ordinal,
        node,
        range,
        admitted: Some(Admitted {
            id,
            visibility,
            name,
        }),
        failure: None,
    })
}

fn namespace(plans: &mut [RootPlan]) -> Result<HashMap<String, Vec<DefId>>, HirAvailabilityError> {
    let mut seen = HashMap::<String, u32>::new();
    let mut namespace = HashMap::<String, Vec<DefId>>::new();
    for plan in plans {
        let Some(admitted) = &mut plan.admitted else {
            continue;
        };
        let ordinal = seen.entry(admitted.name.spelling.clone()).or_default();
        let id = DefId {
            module: admitted.id.module.clone(),
            spelling: admitted.id.spelling.clone(),
            same_name_ordinal: *ordinal,
        };
        *ordinal = ordinal
            .checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        admitted.id = id.clone();
        namespace
            .entry(admitted.name.spelling.clone())
            .or_default()
            .push(id);
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
) -> Result<HirItem, HirAvailabilityError> {
    let Some(admitted) = &plan.admitted else {
        item_errors.push(
            sink.lowering(
                plan.failure
                    .ok_or(HirAvailabilityError::StructuralProjection)?,
                HirErrorAttachment::DirectRootItem(plan.ordinal),
                plan.range.clone(),
            )?,
        );
        return Ok(HirItem::Error {
            errors: item_errors.into_boxed_slice(),
            range: plan.range.clone(),
        });
    };
    let id = admitted.id.clone();
    let (value, body_semantic_error) =
        lower_body(plan, parsed, namespace, &id, value_errors, sink, counters)?;
    if id.same_name_ordinal > 0 {
        sink.lowering(
            HirErrorKind::DuplicateDefinition,
            HirErrorAttachment::Definition(id.clone()),
            admitted.name.range.clone(),
        )?;
    }
    if let Some((kind, range)) = body_semantic_error {
        sink.lowering(kind, HirErrorAttachment::Value(id.clone()), range)?;
    }
    Ok(HirItem::Binding(HirBinding {
        id,
        visibility: admitted.visibility,
        name: admitted.name.clone(),
        value,
        range: plan.range.clone(),
    }))
}

fn lower_body(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &HashMap<String, Vec<DefId>>,
    id: &DefId,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    counters: &mut LoweringCounters,
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
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    if has_recovery(&body) {
        return Ok((
            ResolvedExpr::Error {
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
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    let chain_range = range_of(&chain);
    let (expression, atom) = associate_chain_owned(parsed, chain.clone())
        .map_err(|error| match error {
            AssociationError::ExactOperatorEnvironment => {
                HirAvailabilityError::ExactOperatorEnvironment
            }
            AssociationError::StructuralInvariant => HirAvailabilityError::StructuralProjection,
        })?
        .into_parts();
    let Some(atom) = atom else {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            chain_range.clone(),
        )?);
        return Ok((
            ResolvedExpr::Error {
                errors: causal_errors.into_boxed_slice(),
                range: chain_range,
            },
            None,
        ));
    };
    if !matches!(expression, HirExpr::Value { children, .. } if children.is_empty()) {
        causal_errors.push(sink.lowering(
            HirErrorKind::UnsupportedExpression,
            HirErrorAttachment::Value(id.clone()),
            chain_range.clone(),
        )?);
        return Ok((
            ResolvedExpr::Error {
                errors: causal_errors.into_boxed_slice(),
                range: chain_range,
            },
            None,
        ));
    }
    match atom.kind {
        SyntaxKind::IntegerLiteral => Ok((
            ResolvedExpr::Integer {
                spelling: {
                    counters.copied_spelling_bytes += atom.spelling.len();
                    atom.spelling
                },
                range: atom.range,
            },
            None,
        )),
        SyntaxKind::IdentifierExpression => {
            counters.copied_spelling_bytes += atom.spelling.len();
            let name = HirName {
                spelling: atom.spelling,
                range: atom.range.clone(),
            };
            let (resolution, kind) = match namespace.get(&name.spelling) {
                Some(definitions) if definitions.len() == 1 => {
                    (NameResolution::Resolved(definitions[0].clone()), None)
                }
                Some(_) => (NameResolution::Ambiguous, Some(HirErrorKind::AmbiguousName)),
                None => (
                    NameResolution::Unresolved,
                    Some(HirErrorKind::UnresolvedName),
                ),
            };
            Ok((
                ResolvedExpr::Name {
                    range: name.range.clone(),
                    name: name.clone(),
                    resolution,
                },
                kind.map(|kind| (kind, name.range)),
            ))
        }
        _ => Err(HirAvailabilityError::StructuralProjection),
    }
}

fn plain_binding_header(node: &SyntaxNode) -> Option<(HirVisibility, HirName)> {
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
    let [pattern] = pattern_children.as_slice() else {
        return None;
    };
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
    (token.kind() == SyntaxKind::Identifier).then(|| {
        (
            visibility,
            HirName {
                spelling: token.text().to_owned(),
                range: token_range(token),
            },
        )
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
}
