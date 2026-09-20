use std::{collections::HashMap, ops::Range, sync::Arc};

#[cfg(test)]
use std::{cell::RefCell, rc::Rc};

use yu_syntax::{
    ParsedFile, SourceRevision, StructuralRecovery, StructuralRecoveryKind, SyntaxKind, SyntaxNode,
};

use crate::{AssociationError, HirExpr, associate_chain_owned, range_of};

#[cfg(test)]
macro_rules! count_lowering {
    ($field:ident += $value:expr) => {
        LOWERING_COUNTERS.with(|active| {
            if let Some(counters) = active.borrow().as_ref() {
                counters.borrow_mut().$field += $value;
            }
        });
    };
}

#[cfg(not(test))]
macro_rules! count_lowering {
    ($field:ident += $value:expr) => {};
}

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
#[derive(Debug, Eq, Hash, PartialEq)]
pub struct DefId(Arc<DefIdPayload>);

#[derive(Debug, Eq, Hash, PartialEq)]
struct DefIdPayload {
    module: ModuleId,
    spelling: Box<str>,
    same_name_ordinal: u32,
}

impl Clone for DefId {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl DefId {
    fn new(module: ModuleId, spelling: Box<str>, same_name_ordinal: u32) -> Self {
        Self(Arc::new(DefIdPayload {
            module,
            spelling,
            same_name_ordinal,
        }))
    }

    pub fn module(&self) -> &ModuleId {
        &self.0.module
    }

    pub fn spelling(&self) -> &str {
        &self.0.spelling
    }

    pub fn same_name_ordinal(&self) -> u32 {
        self.0.same_name_ordinal
    }
}

/// A dense expression identity within one exact immutable [`HirModule`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HirExprId(u32);

impl HirExprId {
    pub fn index(self) -> u32 {
        self.0
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
        id: HirExprId,
        spelling: String,
        range: Range<usize>,
    },
    Name {
        id: HirExprId,
        name: HirName,
        resolution: NameResolution,
        range: Range<usize>,
    },
    Error {
        id: HirExprId,
        errors: Box<[HirErrorId]>,
        range: Range<usize>,
    },
}

impl ResolvedExpr {
    pub fn id(&self) -> HirExprId {
        match self {
            Self::Integer { id, .. } | Self::Name { id, .. } | Self::Error { id, .. } => *id,
        }
    }

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

/// Lowers direct-root bindings and expressions against one complete local namespace.
pub fn lower_module(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    _imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    lower_module_impl(identity, parsed, _imports)
}

fn lower_module_impl(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    _imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    if identity.file != *identity.module.file() {
        return Err(HirAvailabilityError::InconsistentIdentity);
    }
    let recoveries = validated_recoveries(parsed)?;
    let root = SyntaxNode::new_root(parsed.green().clone());
    let mut plans = Vec::new();
    for (index, node) in root.children().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        plans.push(plan_root(node, ordinal)?);
    }
    let partition = partition_recoveries(&recoveries, plans.len())?;
    let namespace = namespace(&mut plans, identity.module())?;
    let mut sink = ErrorSink::default();
    let root_errors = emit_structural_errors(&recoveries, &partition, &plans, &mut sink)?;

    let mut items = Vec::with_capacity(plans.len());
    let mut expression_ids = ExprIdAllocator::default();
    for (plan, errors) in plans.iter().zip(root_errors) {
        items.push(lower_plan(
            plan,
            parsed,
            &namespace,
            errors.item,
            errors.value,
            &mut sink,
            &mut expression_ids,
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

#[cfg(test)]
#[derive(Default)]
struct LoweringCounters {
    recovery_visits: usize,
    syntax_emissions: usize,
    copied_spelling_bytes: usize,
    expression_id_assignments: usize,
}

#[cfg(test)]
thread_local! {
    static LOWERING_COUNTERS: RefCell<Option<Rc<RefCell<LoweringCounters>>>> = const { RefCell::new(None) };
}

#[cfg(test)]
struct LoweringCounterScope {
    previous: Option<Rc<RefCell<LoweringCounters>>>,
}

#[cfg(test)]
impl LoweringCounterScope {
    fn enter(counters: Rc<RefCell<LoweringCounters>>) -> Self {
        let previous = LOWERING_COUNTERS.with(|active| active.replace(Some(counters)));
        Self { previous }
    }
}

#[cfg(test)]
impl Drop for LoweringCounterScope {
    fn drop(&mut self) {
        LOWERING_COUNTERS.with(|active| {
            active.replace(self.previous.take());
        });
    }
}

#[cfg(test)]
fn lower_module_with_counters(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<(HirModule, LoweringCounters), HirAvailabilityError> {
    let counters = Rc::new(RefCell::new(LoweringCounters::default()));
    let scope = LoweringCounterScope::enter(Rc::clone(&counters));
    let module = lower_module_impl(identity, parsed, imports);
    drop(scope);
    let counters = Rc::into_inner(counters)
        .expect("the test-only counter scope releases its sole handle")
        .into_inner();
    module.map(|module| (module, counters))
}

#[derive(Default)]
struct ExprIdAllocator {
    next: u32,
}

impl ExprIdAllocator {
    fn allocate(&mut self) -> Result<HirExprId, HirAvailabilityError> {
        let id = HirExprId(self.next);
        self.next = self
            .next
            .checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        count_lowering!(expression_id_assignments += 1);
        Ok(id)
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
) -> Result<RecoveryPartition, HirAvailabilityError> {
    let mut partition = RecoveryPartition {
        module: Vec::new(),
        roots: (0..root_count).map(|_| Vec::new()).collect(),
    };
    for (index, recovery) in recoveries.iter().enumerate() {
        count_lowering!(recovery_visits += 1);
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
        count_lowering!(syntax_emissions += 1);
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
    id: Option<DefId>,
    visibility: HirVisibility,
    name: HirName,
}

impl Admitted {
    fn id(&self) -> &DefId {
        self.id.as_ref().expect(
            "namespace assigns every admitted binding identity before recovery and body lowering",
        )
    }
}

impl RootPlan {
    fn recovery_attachment(&self, recovery: &StructuralRecovery) -> HirErrorAttachment {
        match &self.kind {
            RootPlanKind::Binding(admitted) => {
                if recovery.path().contains(&SyntaxKind::BindingBody) {
                    HirErrorAttachment::Value(admitted.id().clone())
                } else {
                    HirErrorAttachment::Definition(admitted.id().clone())
                }
            }
            RootPlanKind::DirectExpression | RootPlanKind::Unsupported(_) => {
                HirErrorAttachment::DirectRootItem(self.ordinal)
            }
        }
    }
}

fn plan_root(node: SyntaxNode, ordinal: u32) -> Result<RootPlan, HirAvailabilityError> {
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
    let Some((visibility, name)) = plain_binding_header(&node) else {
        return Ok(RootPlan {
            ordinal,
            node,
            range,
            kind: RootPlanKind::Unsupported(HirErrorKind::UnsupportedTarget),
        });
    };
    count_lowering!(copied_spelling_bytes += name.spelling.len());
    Ok(RootPlan {
        ordinal,
        node,
        range,
        kind: RootPlanKind::Binding(Admitted {
            id: None,
            visibility,
            name,
        }),
    })
}

fn namespace(
    plans: &mut [RootPlan],
    module: &ModuleId,
) -> Result<HashMap<String, Vec<DefId>>, HirAvailabilityError> {
    let mut seen = HashMap::<String, u32>::new();
    let mut namespace = HashMap::<String, Vec<DefId>>::new();
    for plan in plans {
        let RootPlanKind::Binding(admitted) = &mut plan.kind else {
            continue;
        };
        let ordinal = seen.entry(admitted.name.spelling.clone()).or_default();
        let id = DefId::new(
            module.clone(),
            admitted.name.spelling.clone().into_boxed_str(),
            *ordinal,
        );
        *ordinal = ordinal
            .checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?;
        admitted.id = Some(id.clone());
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
    expression_ids: &mut ExprIdAllocator,
) -> Result<HirItem, HirAvailabilityError> {
    let RootPlanKind::Binding(admitted) = &plan.kind else {
        return match &plan.kind {
            RootPlanKind::DirectExpression => lower_direct_root_expression(
                plan,
                parsed,
                namespace,
                item_errors,
                sink,
                expression_ids,
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
    let id = admitted.id().clone();
    let (value, body_semantic_error) = lower_body(
        plan,
        parsed,
        namespace,
        &id,
        value_errors,
        sink,
        expression_ids,
    )?;
    if id.same_name_ordinal() > 0 {
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

fn lower_direct_root_expression(
    plan: &RootPlan,
    parsed: &ParsedFile,
    namespace: &HashMap<String, Vec<DefId>>,
    mut causal_errors: Vec<HirErrorId>,
    sink: &mut ErrorSink,
    expression_ids: &mut ExprIdAllocator,
) -> Result<HirItem, HirAvailabilityError> {
    if !causal_errors.is_empty() {
        return Ok(HirItem::Expression(ResolvedExpr::Error {
            id: expression_ids.allocate()?,
            errors: causal_errors.into_boxed_slice(),
            range: plan.range.clone(),
        }));
    }
    match lower_simple_chain(parsed, &plan.node, namespace, expression_ids)? {
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
                id: expression_ids.allocate()?,
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
    expression_ids: &mut ExprIdAllocator,
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
                id: expression_ids.allocate()?,
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
                id: expression_ids.allocate()?,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    if has_recovery(&body) {
        return Ok((
            ResolvedExpr::Error {
                id: expression_ids.allocate()?,
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
                id: expression_ids.allocate()?,
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
                id: expression_ids.allocate()?,
                errors: causal_errors.into_boxed_slice(),
                range: range_of(&body),
            },
            None,
        ));
    }
    match lower_simple_chain(parsed, chain, namespace, expression_ids)? {
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
                    id: expression_ids.allocate()?,
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
    expression_ids: &mut ExprIdAllocator,
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
                id: expression_ids.allocate()?,
                spelling: {
                    count_lowering!(copied_spelling_bytes += atom.spelling.len());
                    atom.spelling
                },
                range: atom.range,
            },
            semantic_error: None,
        }),
        SyntaxKind::IdentifierExpression => {
            count_lowering!(copied_spelling_bytes += atom.spelling.len());
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
            Ok(SimpleChainLowering::Resolved {
                expression: ResolvedExpr::Name {
                    id: expression_ids.allocate()?,
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
        let (module, counters) =
            lower_module_with_counters(identity(), &parsed, SemanticImports::empty())
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
    fn expression_ids_are_dense_in_source_order_including_errors() {
        let parsed = parsed("42; my x = @; missing; f 1");
        let (module, counters) =
            lower_module_with_counters(identity(), &parsed, SemanticImports::empty())
                .expect("expression identity allocation remains available");

        let expression_ids = module
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Binding(binding) => Some(binding.value().id()),
                HirItem::Expression(expression) => Some(expression.id()),
                HirItem::Error { .. } => None,
            })
            .map(HirExprId::index)
            .collect::<Vec<_>>();
        assert_eq!(expression_ids, vec![0, 1, 2, 3]);
        assert_eq!(counters.expression_id_assignments, expression_ids.len());
    }

    #[test]
    fn def_id_clone_shares_its_immutable_payload() {
        let module = lower_module(
            identity(),
            &parsed("my repeated = 1"),
            SemanticImports::empty(),
        )
        .expect("definition identity remains available");
        let [HirItem::Binding(binding)] = module.items() else {
            panic!("one binding");
        };

        let clone = binding.id().clone();
        assert!(Arc::ptr_eq(&binding.id().0, &clone.0));
    }
}
