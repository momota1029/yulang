//! Opt-in immutable source artifact. Syntax provenance carries no type or role judgment.
use crate::{
    DefinitionRootId, HirAvailabilityError, HirModule, HirOccurrenceId, HirParameterId,
    ModuleIdentity, SemanticImports,
};
use crate::{range_of, range_of_token};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    ops::Range,
    sync::Arc,
};
use yu_syntax::{ParsedFile, SourceNodeKey, SyntaxKind, SyntaxNode, SyntaxToken};

/// Experimental identity retention during the existing lowering path.
/// This adds no inference or source-role judgment.
pub fn lower_module_with_source_identity(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    crate::module::lower_module_with_source_identity(identity, parsed, imports)
}

/// Retains one leaf-only application with source identity and explicit pending errors.
/// This opt-in route supplies no semantic call judgment or inference acceptance.
pub fn lower_module_with_shadow_applications(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
) -> Result<HirModule, HirAvailabilityError> {
    crate::module::lower_module_with_shadow_applications(identity, parsed, imports)
}

/// Retains the approved nested source carrier without lowering its local call.
/// Validation finishes before the immutable HIR module is published. Removing
/// this opt-in boundary leaves ordinary lowering and collection unchanged.
pub fn lower_module_with_captured_source(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
    artifact: Arc<ShadowArtifact>,
) -> Result<HirModule, HirAvailabilityError> {
    let mut hir = lower_module_with_source_identity(identity, parsed, imports)?;
    let invalid = || HirAvailabilityError::StructuralProjection;
    let [crate::HirItem::Binding(binding)] = hir.items() else {
        return Err(invalid());
    };
    let skeleton = artifact.skeleton().map_err(|_| invalid())?;
    let input = skeleton.captured_call_input().ok_or_else(invalid)?;
    let root = skeleton
        .expression(skeleton.body())
        .map_err(|_| invalid())?;
    let Form::Lambda { parameter, .. } = root.form() else {
        return Err(invalid());
    };
    let declaration = artifact
        .definition_source_position(&hir, binding.definition_root())
        .map_err(|_| invalid())?;
    if root.position() != &declaration
        || skeleton
            .root_declaration_header()
            .ok_or_else(invalid)?
            .statement()
            != &declaration
        || parameter != input.outer_parameter()
    {
        return Err(invalid());
    }
    let crate::ResolvedExpr::Lambda {
        parameter: hir_parameter,
        ..
    } = binding.value()
    else {
        return Err(invalid());
    };
    let parameter_position = artifact
        .parameter_source_position(&hir, hir_parameter)
        .map_err(|_| invalid())?;
    if skeleton
        .binder(parameter)
        .map_err(|_| invalid())?
        .position()
        != &parameter_position
    {
        return Err(invalid());
    }
    hir.captured_source = Some((binding.definition_root().clone(), artifact));
    Ok(hir)
}

/// Retains the exact approved local binding and its unresolved inner application.
pub fn lower_module_with_shadow_local_binding(
    identity: ModuleIdentity,
    parsed: &ParsedFile,
    imports: SemanticImports,
    artifact: Arc<ShadowArtifact>,
) -> Result<HirModule, HirAvailabilityError> {
    let hir = lower_module_with_captured_source(identity, parsed, imports, artifact.clone())?;
    crate::module::retain_shadow_local_binding(hir, &artifact)
}

/// Cold sequential source carrier; its initializer never enters semantic collection.
#[derive(Clone, Debug)]
pub struct ShadowLocalBind {
    pub occurrence: HirOccurrenceId,
    pub local: crate::HirLocalId,
    pub initializer: crate::ResolvedExpr,
    pub continuation: ShadowLocalUse,
    pub captures: Box<[HirParameterId]>,
    pub range: Range<usize>,
}

#[derive(Clone, Debug)]
pub struct ShadowLocalUse {
    pub occurrence: HirOccurrenceId,
    pub local: crate::HirLocalId,
    pub range: Range<usize>,
}

impl HirModule {
    pub fn shadow_local_binding(
        &self,
        root: &DefinitionRootId,
    ) -> Result<Option<&ShadowLocalBind>, SourceIdentityError> {
        if !self.owns_definition_root(root) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        Ok(self
            .source_identity
            .as_ref()
            .and_then(|source| source.local_binding.as_ref())
            .filter(|binding| binding.local.definition_root() == root))
    }

    pub fn shadow_parameter_local_owner(
        &self,
        parameter: &HirParameterId,
    ) -> Result<Option<&crate::HirLocalId>, SourceIdentityError> {
        if !self.owns_definition_root(parameter.definition_root()) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        Ok(self
            .source_identity
            .as_ref()
            .and_then(|source| source.local_parameter_owners.get(parameter)))
    }

    /// Borrows the validated carrier for this exact HIR root. Artifact-local
    /// call premises remain separate from solver pending-application rows.
    pub fn shadow_captured_source(
        &self,
        root: &DefinitionRootId,
    ) -> Result<Option<&Arc<ShadowArtifact>>, SourceIdentityError> {
        if !self.owns_definition_root(root) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        Ok(self
            .captured_source
            .as_ref()
            .and_then(|(owner, artifact)| (owner == root).then_some(artifact)))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceIdentityError {
    ForeignHirArtifact,
    ForeignParse,
    MissingSource,
    AmbiguousSource,
}

#[derive(Clone, Debug)]
pub(crate) struct HirSourceIdentity {
    parse_root: SourceNodeKey,
    definitions: HashMap<DefinitionRootId, SourceNodeKey>,
    occurrences: HashMap<HirOccurrenceId, SourceNodeKey>,
    parameters: HashMap<HirParameterId, SourceNodeKey>,
    locals: HashMap<crate::HirLocalId, SourceNodeKey>,
    pub(crate) local_binding: Option<ShadowLocalBind>,
    pub(crate) local_parameter_owners: HashMap<HirParameterId, crate::HirLocalId>,
}

pub(crate) fn source_keys(parsed: &ParsedFile) -> HashMap<SyntaxNode, SourceNodeKey> {
    let mut keys = HashMap::new();
    let mut stack = vec![parsed.source_root()];
    while let Some(node) = stack.pop() {
        keys.insert(node.syntax().clone(), node.key());
        stack.extend(node.children());
    }
    keys
}

impl HirSourceIdentity {
    pub(crate) fn new(parsed: &ParsedFile) -> Self {
        Self {
            parse_root: parsed.source_root().key(),
            definitions: HashMap::new(),
            occurrences: HashMap::new(),
            parameters: HashMap::new(),
            locals: HashMap::new(),
            local_binding: None,
            local_parameter_owners: HashMap::new(),
        }
    }
    pub(crate) fn record_local(&mut self, id: crate::HirLocalId, key: SourceNodeKey) {
        self.locals.insert(id, key);
    }
    pub(crate) fn maximum_occurrence_ordinal(&self) -> Option<u32> {
        self.occurrences.keys().map(HirOccurrenceId::ordinal).max()
    }
    pub(crate) fn record_unique_occurrence(
        &mut self,
        id: HirOccurrenceId,
        key: SourceNodeKey,
    ) -> bool {
        let std::collections::hash_map::Entry::Vacant(entry) = self.occurrences.entry(id) else {
            return false;
        };
        entry.insert(key);
        true
    }
    pub(crate) fn record_definition(&mut self, id: DefinitionRootId, key: SourceNodeKey) {
        self.definitions.insert(id, key);
    }
    pub(crate) fn record_parameter(&mut self, id: HirParameterId, key: SourceNodeKey) {
        self.parameters.insert(id, key);
    }
    pub(crate) fn record_occurrence(&mut self, id: HirOccurrenceId, key: SourceNodeKey) {
        self.occurrences.insert(id, key);
    }
}

/// Complete caller-selected parse snapshot and its bounded structural projections.
#[derive(Debug)]
pub struct ShadowArtifact {
    identity: Arc<()>,
    parsed: ParsedFile,
    source_positions: HashMap<SourceNodeKey, Option<PositionId>>,
    positions: Vec<Position>,
    annotations: Vec<AnnotationOccurrence>,
    skeleton: Result<Skeleton, ShadowError>,
}

pub const MAX_SYNTAX_DEPTH: usize = 128;
pub const MAX_RAW_ELEMENTS: usize = 65_536;

/// Borrowed exact-position index of the existing structural projection.
/// Presence supplies neither module membership nor a semantic judgment.
pub struct SkeletonSourceCrosswalk<'a> {
    artifact: &'a ShadowArtifact,
    definitions: HashMap<usize, (&'a Expression, &'a BinderId)>,
    parameters: HashMap<usize, (&'a Expression, &'a BinderId)>,
    uses: HashMap<usize, &'a UseId>,
    applications: HashMap<usize, &'a Expression>,
}

impl<'a> SkeletonSourceCrosswalk<'a> {
    pub fn artifact(&self) -> &'a ShadowArtifact {
        self.artifact
    }

    pub fn definition_at_position(
        &self,
        position: &PositionId,
    ) -> Result<Option<(&'a Expression, &'a BinderId)>, ShadowError> {
        self.artifact.position(position)?;
        Ok(self.definitions.get(&position.0.index).copied())
    }

    pub fn parameter_at_position(
        &self,
        position: &PositionId,
    ) -> Result<Option<(&'a Expression, &'a BinderId)>, ShadowError> {
        self.artifact.position(position)?;
        Ok(self.parameters.get(&position.0.index).copied())
    }

    pub fn use_at_position(&self, position: &PositionId) -> Result<Option<&'a UseId>, ShadowError> {
        self.artifact.position(position)?;
        Ok(self.uses.get(&position.0.index).copied())
    }

    /// Borrow the retained Apply at its exact CST call-tail position.
    /// This shadow lexical/source lookup is not production NameResolution and
    /// supplies no typed path, owner, receiver, beta, slot, profile, role,
    /// annotation meaning, Q result or semantic evidence.
    pub fn application_at_position(
        &self,
        position: &PositionId,
    ) -> Result<Option<&'a Expression>, ShadowError> {
        self.artifact.position(position)?;
        Ok(self.applications.get(&position.0.index).copied())
    }

    /// Return only the already retained direct Use callee's lexical links.
    /// Grouped and computed callees do not acquire a resolution through this lookup.
    pub fn application_direct_use_at_position(
        &self,
        position: &PositionId,
    ) -> Result<Option<(&'a UseId, &'a BinderId)>, ShadowError> {
        let Some(expression) = self.application_at_position(position)? else {
            return Ok(None);
        };
        let Form::Apply { callee, .. } = expression.form() else {
            unreachable!("validated crosswalk application");
        };
        let skeleton = self
            .artifact
            .skeleton()
            .expect("application index requires validated skeleton");
        let Form::Use { occurrence, binder } = skeleton.expression(callee)?.form() else {
            return Ok(None);
        };
        Ok(Some((occurrence, binder)))
    }
}

impl ShadowArtifact {
    /// Build once per borrowed observation, including an empty index when the
    /// bounded skeleton is unavailable. Raw source identities remain queryable.
    pub fn skeleton_source_crosswalk(&self) -> SkeletonSourceCrosswalk<'_> {
        let mut crosswalk = SkeletonSourceCrosswalk {
            artifact: self,
            definitions: HashMap::new(),
            parameters: HashMap::new(),
            uses: HashMap::new(),
            applications: HashMap::new(),
        };
        if let Ok(skeleton) = self.skeleton() {
            for expression in skeleton.expressions() {
                match expression.form() {
                    Form::Lambda {
                        binding, parameter, ..
                    } => {
                        crosswalk
                            .definitions
                            .insert(expression.position().0.index, (expression, binding));
                        crosswalk.parameters.insert(
                            skeleton
                                .binder(parameter)
                                .expect("validated skeleton parameter")
                                .position()
                                .0
                                .index,
                            (expression, parameter),
                        );
                    }
                    Form::Bind {
                        binder: binding, ..
                    } => {
                        crosswalk
                            .definitions
                            .insert(expression.position().0.index, (expression, binding));
                    }
                    Form::Use { occurrence, .. } => {
                        crosswalk.uses.insert(
                            skeleton
                                .use_position(occurrence)
                                .expect("validated skeleton use position")
                                .0
                                .index,
                            occurrence,
                        );
                    }
                    Form::Apply { .. } => {
                        crosswalk
                            .applications
                            .insert(expression.position().0.index, expression);
                    }
                    _ => {}
                }
            }
        }
        crosswalk
    }
    /// Publishes atomically after iterative structural preflight. Unsupported
    /// lexical/application projection remains an error inside the complete snapshot.
    pub fn from_parsed(parsed: ParsedFile) -> Result<Self, ShadowError> {
        let root = SyntaxNode::new_root(parsed.green().clone());
        preflight(&root)?;
        if !parsed
            .syntax_diagnostics()
            .map_err(|_| ShadowError::MalformedSource)?
            .is_empty()
        {
            return Err(ShadowError::MalformedSource);
        }
        let identity = Arc::new(());
        let mut artifact = Self {
            identity: identity.clone(),
            parsed,
            source_positions: HashMap::new(),
            positions: Vec::new(),
            annotations: Vec::new(),
            skeleton: Err(ShadowError::MalformedSource),
        };
        let positions = artifact.retain(root.clone());
        artifact.skeleton = build_skeleton(
            &artifact.parsed,
            identity,
            root,
            &positions,
            &artifact.positions,
            &artifact.annotations,
        );
        Ok(artifact)
    }
    /// Joins an admitted HIR declaration to its exact raw-CST position.
    pub fn definition_source_position(
        &self,
        hir: &HirModule,
        id: &DefinitionRootId,
    ) -> Result<PositionId, SourceIdentityError> {
        if !hir.owns_definition_root(id) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        let source = hir
            .source_identity
            .as_ref()
            .ok_or(SourceIdentityError::MissingSource)?;
        self.check_source_parse(source)?;
        self.source_position(
            source
                .definitions
                .get(id)
                .ok_or(SourceIdentityError::MissingSource)?,
        )
    }
    /// Joins a retained HIR occurrence to its exact raw-CST position.
    /// Shadow applications identify their CallTail or MlArgument; synthesized
    /// or error occurrences without exact source identity report MissingSource.
    pub fn occurrence_source_position(
        &self,
        hir: &HirModule,
        id: &HirOccurrenceId,
    ) -> Result<PositionId, SourceIdentityError> {
        if !hir.owns_occurrence(id) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        let source = hir
            .source_identity
            .as_ref()
            .ok_or(SourceIdentityError::MissingSource)?;
        self.check_source_parse(source)?;
        self.source_position(
            source
                .occurrences
                .get(id)
                .ok_or(SourceIdentityError::MissingSource)?,
        )
    }
    /// Joins an admitted HIR parameter to its exact IdentifierPattern node.
    /// This source identity carries no typed slot or role judgment.
    pub fn parameter_source_position(
        &self,
        hir: &HirModule,
        id: &HirParameterId,
    ) -> Result<PositionId, SourceIdentityError> {
        if !hir.owns_parameter(id)
            && !(hir.owns_definition_root(id.definition_root())
                && hir
                    .source_identity
                    .as_ref()
                    .is_some_and(|source| source.local_parameter_owners.contains_key(id)))
        {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        let source = hir
            .source_identity
            .as_ref()
            .ok_or(SourceIdentityError::MissingSource)?;
        self.check_source_parse(source)?;
        self.source_position(
            source
                .parameters
                .get(id)
                .ok_or(SourceIdentityError::MissingSource)?,
        )
    }
    pub fn local_source_position(
        &self,
        hir: &HirModule,
        id: &crate::HirLocalId,
    ) -> Result<PositionId, SourceIdentityError> {
        if !hir.owns_definition_root(id.definition_root()) {
            return Err(SourceIdentityError::ForeignHirArtifact);
        }
        let source = hir
            .source_identity
            .as_ref()
            .ok_or(SourceIdentityError::MissingSource)?;
        self.check_source_parse(source)?;
        self.source_position(
            source
                .locals
                .get(id)
                .ok_or(SourceIdentityError::MissingSource)?,
        )
    }

    pub(crate) fn exact_source_key(
        &self,
        position: &PositionId,
    ) -> Result<SourceNodeKey, SourceIdentityError> {
        self.position(position)
            .map_err(|_| SourceIdentityError::ForeignParse)?;
        let mut keys = self
            .source_positions
            .iter()
            .filter_map(|(key, candidate)| (candidate.as_ref() == Some(position)).then_some(key));
        let key = keys.next().ok_or(SourceIdentityError::MissingSource)?;
        if keys.next().is_some() {
            return Err(SourceIdentityError::AmbiguousSource);
        }
        Ok(key.clone())
    }

    fn check_source_parse(&self, source: &HirSourceIdentity) -> Result<(), SourceIdentityError> {
        if self.parsed.owns_source_key(&source.parse_root) {
            Ok(())
        } else {
            Err(SourceIdentityError::ForeignParse)
        }
    }
    /// Exact parse-owned node lookup, rejecting reused zero-width node keys.
    pub fn source_position(&self, key: &SourceNodeKey) -> Result<PositionId, SourceIdentityError> {
        if !self.parsed.owns_source_key(key) {
            return Err(SourceIdentityError::ForeignParse);
        }
        match self.source_positions.get(key) {
            Some(Some(id)) => Ok(id.clone()),
            Some(None) => Err(SourceIdentityError::AmbiguousSource),
            None => Err(SourceIdentityError::MissingSource),
        }
    }
    pub fn parsed(&self) -> &ParsedFile {
        &self.parsed
    }
    pub fn source(&self) -> &str {
        self.parsed.source()
    }
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }
    pub fn root(&self) -> PositionId {
        self.position_id(0)
    }
    /// Direct-root binding syntax in source order, independently of `skeleton()`.
    /// Header, pattern, name and body syntax remain accessible through the
    /// retained children; no component membership or declaration role is inferred.
    pub fn raw_declaration_positions(&self) -> impl Iterator<Item = PositionId> + '_ {
        self.positions[0].children.iter().filter_map(|id| {
            let position = &self.positions[id.0.index];
            (position.is_node && position.kind == SyntaxKind::BindingStatement).then(|| id.clone())
        })
    }
    /// Exact identifier-expression occurrences in retained source order.
    /// These are syntax positions, with resolution and use classification pending.
    pub fn raw_identifier_expression_positions(&self) -> impl Iterator<Item = PositionId> + '_ {
        self.positions
            .iter()
            .enumerate()
            .filter_map(|(index, position)| {
                (position.is_node && position.kind == SyntaxKind::IdentifierExpression)
                    .then(|| self.position_id(index))
            })
    }
    pub fn annotations(&self) -> &[AnnotationOccurrence] {
        &self.annotations
    }
    pub fn annotation(&self, id: &AnnotationId) -> Result<&AnnotationOccurrence, ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.0.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        self.annotations
            .get(id.0.index)
            .ok_or(ShadowError::MissingReference { index: id.0.index })
    }
    /// Structural/lexical result only; success makes no semantic judgment.
    pub fn skeleton(&self) -> Result<&Skeleton, &ShadowError> {
        self.skeleton.as_ref()
    }
    pub fn position(&self, id: &PositionId) -> Result<&Position, ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.0.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        self.positions
            .get(id.0.index)
            .ok_or(ShadowError::MissingReference { index: id.0.index })
    }
    fn position_id(&self, index: usize) -> PositionId {
        PositionId(LocalId {
            artifact: self.identity.clone(),
            index,
        })
    }
    fn retain_source_position(&mut self, key: SourceNodeKey, id: PositionId) {
        self.source_positions
            .entry(key)
            .and_modify(|position| *position = None)
            .or_insert(Some(id));
    }
    fn retain(&mut self, root: SyntaxNode) -> HashMap<SyntaxNode, Option<PositionId>> {
        // CST handles identify occurrences in this exact root, including equal text.
        // This temporary index is dropped once lexical projection is complete.
        let mut nodes = HashMap::new();
        let source_keys = source_keys(&self.parsed);
        let mut stack = vec![(RawElement::Node(root), None, 0)];
        while let Some((element, parent, ordinal)) = stack.pop() {
            let id = self.position_id(self.positions.len());
            if let Some(node) = element.as_node() {
                if let Some(key) = source_keys.get(node) {
                    self.retain_source_position(key.clone(), id.clone());
                }
            }
            if let Some(node) = element.as_node()
                && matches!(
                    node.kind(),
                    SyntaxKind::IdentifierPattern
                        | SyntaxKind::IdentifierExpression
                        | SyntaxKind::IntegerLiteral
                        | SyntaxKind::ParenthesizedExpression
                        | SyntaxKind::MlArgument
                        | SyntaxKind::CallTail
                        | SyntaxKind::PatternTypeAnnotation
                        | SyntaxKind::BindingStatement
                        | SyntaxKind::BindingHeader
                        | SyntaxKind::BracedStatementBlockExpression
                )
            {
                // Rowan keys include a green handle and offset. Synthetic zero-width
                // duplicate nodes can share that key: reject ambiguous projection
                // rather than selecting one retained structural occurrence.
                nodes
                    .entry(node.clone())
                    .and_modify(|position| *position = None)
                    .or_insert(Some(id.clone()));
            }
            let range = element.range();
            let children = element
                .as_node()
                .map(|node| raw_children(node))
                .unwrap_or_default();
            self.positions.push(Position {
                kind: element.kind(),
                range,
                is_node: element.as_node().is_some(),
                parent: parent.clone(),
                ordinal,
                children: Vec::new(),
            });
            if let Some(parent) = parent {
                self.positions[parent.0.index].children.push(id.clone());
            }
            if matches!(
                element.kind(),
                SyntaxKind::PatternTypeAnnotation | SyntaxKind::TypeAnnotationTail
            ) {
                self.annotations.push(AnnotationOccurrence {
                    id: AnnotationId(LocalId {
                        artifact: self.identity.clone(),
                        index: self.annotations.len(),
                    }),
                    position: id.clone(),
                    correspondence: Correspondence::PendingTypedPortAndProfile,
                });
            }
            for (ordinal, child) in children.into_iter().enumerate().rev() {
                stack.push((child, Some(id.clone()), ordinal));
            }
        }
        nodes
    }
}

fn preflight(root: &SyntaxNode) -> Result<(), ShadowError> {
    let mut stack = vec![(root.clone(), 0)];
    let mut count = 1;
    while let Some((node, depth)) = stack.pop() {
        for child in node.children_with_tokens() {
            if depth + 1 > MAX_SYNTAX_DEPTH {
                return Err(ShadowError::SyntaxDepthLimit);
            }
            count += 1;
            if count > MAX_RAW_ELEMENTS {
                return Err(ShadowError::ElementLimit);
            }
            if let Some(child) = child.as_node() {
                stack.push((child.clone(), depth + 1));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PositionId(LocalId);

/// Artifact-local source-occurrence identity only, distinct from raw syntax identity.
/// This is not beta, a typed port/profile, permission, owner, or evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnnotationId(LocalId);

#[derive(Debug)]
pub struct Position {
    kind: SyntaxKind,
    range: Range<usize>,
    is_node: bool,
    parent: Option<PositionId>,
    ordinal: usize,
    children: Vec<PositionId>,
}
impl Position {
    pub fn kind(&self) -> SyntaxKind {
        self.kind
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn is_node(&self) -> bool {
        self.is_node
    }
    pub fn parent(&self) -> Option<&PositionId> {
        self.parent.as_ref()
    }
    /// Counts every raw child, including punctuation and trivia. Syntax only.
    pub fn ordinal(&self) -> usize {
        self.ordinal
    }
    pub fn children(&self) -> &[PositionId] {
        &self.children
    }
}
#[derive(Debug, Eq, PartialEq)]
pub enum Correspondence {
    PendingTypedPortAndProfile,
}
#[derive(Debug)]
pub struct AnnotationOccurrence {
    id: AnnotationId,
    position: PositionId,
    correspondence: Correspondence,
}
impl AnnotationOccurrence {
    pub fn id(&self) -> &AnnotationId {
        &self.id
    }
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn correspondence(&self) -> &Correspondence {
        &self.correspondence
    }
}
/// Structural association only; it supplies no typed port or annotation permission.
#[derive(Debug)]
pub struct ParameterAnnotationIncidence {
    parameter: BinderId,
    annotation: AnnotationId,
}
impl ParameterAnnotationIncidence {
    pub fn parameter(&self) -> &BinderId {
        &self.parameter
    }
    pub fn annotation(&self) -> &AnnotationId {
        &self.annotation
    }
}

/// Ordered root header syntax only; no callable stages or parameter roles.
#[derive(Debug)]
pub struct RootDeclarationHeader {
    statement: PositionId,
    header: PositionId,
    name: PositionId,
    parameters: Vec<BinderId>,
    body: ExprId,
}
impl RootDeclarationHeader {
    pub fn statement(&self) -> &PositionId {
        &self.statement
    }
    pub fn header(&self) -> &PositionId {
        &self.header
    }
    pub fn name(&self) -> &PositionId {
        &self.name
    }
    pub fn parameters(&self) -> &[BinderId] {
        &self.parameters
    }
    pub fn body(&self) -> &ExprId {
        &self.body
    }
}

#[derive(Debug)]
pub struct Skeleton {
    root_header: Option<RootDeclarationHeader>,
    identity: Arc<()>,
    pub(crate) binders: Vec<Binder>,
    pub(crate) expressions: Vec<Expression>,
    pub(crate) uses: Vec<ExprId>,
    use_positions: Vec<PositionId>,
    capture_uses: Vec<CaptureUseIncidence>,
    parameter_annotations: Vec<ParameterAnnotationIncidence>,
    pub(crate) body: ExprId,
    pub(crate) pending: Vec<PendingPremise>,
}

#[derive(Clone, Debug)]
struct LocalId {
    artifact: Arc<()>,
    index: usize,
}

impl PartialEq for LocalId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.index == other.index
    }
}

impl Eq for LocalId {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExprId(LocalId);

/// Read-only source incidence of an already retained `Form::Apply`.
/// The expression identity is unchanged; this supplies no semantic call view.
#[derive(Debug)]
pub struct ApplicationSourceOccurrence<'a> {
    expression: ExprId,
    position: &'a PositionId,
    source_form: SyntaxKind,
    callee: &'a ExprId,
    argument: &'a ExprId,
}

impl ApplicationSourceOccurrence<'_> {
    pub fn expression(&self) -> &ExprId {
        &self.expression
    }
    pub fn position(&self) -> &PositionId {
        self.position
    }
    pub fn source_form(&self) -> SyntaxKind {
        self.source_form
    }
    pub fn callee(&self) -> &ExprId {
        self.callee
    }
    pub fn argument(&self) -> &ExprId {
        self.argument
    }
}

/// Existing Apply-to-direct-Use incidence; no callable role or typed call view.
#[derive(Debug)]
pub struct ResolvedCallIncidence<'a> {
    application: ApplicationSourceOccurrence<'a>,
    occurrence: &'a UseId,
    binder: &'a BinderId,
}

impl<'a> ResolvedCallIncidence<'a> {
    pub fn application(&self) -> &ApplicationSourceOccurrence<'a> {
        &self.application
    }
    pub fn occurrence(&self) -> &UseId {
        self.occurrence
    }
    pub fn binder(&self) -> &BinderId {
        self.binder
    }
}

/// Read-only source references for one application of an already resolved direct Use.
/// This does not classify the binder as a formal or supply any source/semantic
/// judgment. Retained annotation incidences make no completeness or absence claim.
#[derive(Debug)]
pub struct SourceCallUseInput<'a> {
    call: ResolvedCallIncidence<'a>,
    parameter_annotations: &'a [ParameterAnnotationIncidence],
}

impl<'a> SourceCallUseInput<'a> {
    pub fn application(&self) -> &ApplicationSourceOccurrence<'a> {
        self.call.application()
    }
    pub fn occurrence(&self) -> &UseId {
        self.call.occurrence()
    }
    pub fn binder(&self) -> &BinderId {
        self.call.binder()
    }
    /// Whole retained argument expression, without value/computation typing.
    pub fn argument(&self) -> &ExprId {
        self.call.application().argument()
    }
    /// Only existing incidences for this exact binder. An empty iterator does
    /// not establish that the source binder has no annotation.
    pub fn parameter_annotations(
        &self,
    ) -> impl Iterator<Item = &'a ParameterAnnotationIncidence> + '_ {
        self.parameter_annotations
            .iter()
            .filter(|incidence| incidence.parameter() == self.binder())
    }
}

/// Borrowed references along the retained root-Lambda/local-Bind/captured-call
/// topology. This structural projection leaves every pending premise unchanged.
#[derive(Debug)]
pub struct CapturedCallInput<'a> {
    outer_parameter: &'a BinderId,
    local_lambda: &'a ExprId,
    local_binding: &'a BinderId,
    returned_use: &'a UseId,
    call: &'a ExprId,
    callee_use: &'a UseId,
    capture_position: &'a PositionId,
}

impl CapturedCallInput<'_> {
    /// Locates unresolved theorem inputs for this already validated topology.
    /// This does not supply any of those inputs or change pending premises.
    pub fn source_view_premise_locator(&self) -> SourceViewPremiseLocator<'_, '_> {
        SourceViewPremiseLocator { input: self }
    }
    pub fn outer_parameter(&self) -> &BinderId {
        self.outer_parameter
    }
    pub fn local_lambda(&self) -> &ExprId {
        self.local_lambda
    }
    pub fn local_binding(&self) -> &BinderId {
        self.local_binding
    }
    pub fn returned_use(&self) -> &UseId {
        self.returned_use
    }
    pub fn call(&self) -> &ExprId {
        self.call
    }
    pub fn callee_use(&self) -> &UseId {
        self.callee_use
    }
    pub fn capture_position(&self) -> &PositionId {
        self.capture_position
    }
}

/// Unresolved upstream inputs of the scoped SourceViewInst construction.
/// These categories are requirements for future producers, never judgments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedSourceViewPremise {
    CompatibleCompleteOriginalRoleIndexedProfile,
    IndependentlyTypedOriginalInvocationAndWholeRowCarrierPrefixResumptionInterpretation,
    JointlyScopedOriginalConstraints,
    SourceSlotCallbackBoundaryInputsAndCorrespondingTypedPaths,
    IndependentInitialCallerProviderWorldAdmission,
    SourceSeedRefinedRelationExistenceAndCoverage,
    /// Requires exhaustive original applicable-slot/contribution formation
    /// and its inversion; this does not supply either judgment.
    OriginalSignatureApplicabilityAndContributionFormation,
}

/// Borrows only the validated structural input. No invocation/profile identity,
/// typed evidence, receipt, receiver, Flow, Q result, source acceptance, or
/// SourceViewInst is constructed or asserted, including input existence.
#[derive(Debug)]
pub struct SourceViewPremiseLocator<'input, 'artifact> {
    input: &'input CapturedCallInput<'artifact>,
}

impl<'input, 'artifact> SourceViewPremiseLocator<'input, 'artifact> {
    pub fn input(&self) -> &'input CapturedCallInput<'artifact> {
        self.input
    }

    /// Exact upstream inventory for the scoped construction, separate from
    /// the existing seven PendingPremise rows and from broader production gates.
    pub fn unresolved_premises(&self) -> &'static [UnresolvedSourceViewPremise] {
        Self::unresolved_premise_inventory()
    }

    /// Enumerates requirements without asserting topology, applicability,
    /// input existence, semantic evidence, a Q result or source acceptance.
    pub fn unresolved_premise_inventory() -> &'static [UnresolvedSourceViewPremise] {
        use UnresolvedSourceViewPremise::*;
        &[
            CompatibleCompleteOriginalRoleIndexedProfile,
            IndependentlyTypedOriginalInvocationAndWholeRowCarrierPrefixResumptionInterpretation,
            JointlyScopedOriginalConstraints,
            SourceSlotCallbackBoundaryInputsAndCorrespondingTypedPaths,
            IndependentInitialCallerProviderWorldAdmission,
            SourceSeedRefinedRelationExistenceAndCoverage,
            OriginalSignatureApplicabilityAndContributionFormation,
        ]
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinderId(LocalId);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UseId(LocalId);

/// Lexical source incidence only; this is not typed capture transport or receipt.
#[derive(Debug)]
pub struct CaptureUseIncidence {
    lambda: ExprId,
    captured: BinderId,
    occurrence: UseId,
    position: PositionId,
}

impl CaptureUseIncidence {
    pub fn lambda(&self) -> &ExprId {
        &self.lambda
    }
    pub fn captured(&self) -> &BinderId {
        &self.captured
    }
    pub fn occurrence(&self) -> &UseId {
        &self.occurrence
    }
    pub fn position(&self) -> &PositionId {
        &self.position
    }
}

#[derive(Debug)]
pub struct Binder {
    position: PositionId,
    pub(crate) name: String,
    pub(crate) range: Range<usize>,
}

#[derive(Debug)]
pub struct Expression {
    position: PositionId,
    pub(crate) range: Range<usize>,
    pub(crate) form: Form,
}

#[derive(Debug)]
pub enum Form {
    /// Header/body correspondence only; captures are resolved lexical identities.
    /// Neither this node nor its source binding selects a runtime closure policy.
    Lambda {
        binding: BinderId,
        parameter: BinderId,
        body: ExprId,
        captures: Vec<BinderId>,
        correspondence: ClosureCorrespondence,
    },
    /// The selected block's sequential local binding and final expression.
    Bind {
        binder: BinderId,
        value: ExprId,
        body: ExprId,
    },
    IntegerLiteral {
        spelling: String,
    },
    Use {
        binder: BinderId,
        occurrence: UseId,
    },
    Group {
        inner: ExprId,
    },
    Apply {
        source_form: SyntaxKind,
        callee: ExprId,
        argument: ExprId,
    },
}

/// Structural lexical retention does not discharge typed capture transport,
/// provider/receiver realization, or source/semantic adequacy.
#[derive(Debug, Eq, PartialEq)]
pub enum ClosureCorrespondence {
    PendingTypedCaptureProviderReceiverAndSemanticDischarge,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Premise {
    CallableRole,
    FullFunctionMembership,
    CallViewRealization,
    /// Unmet source producer obligation: original query-independent shared-component
    /// contract/receipt formation, referenced by this call. Typed capture attachment
    /// is a separate obligation. Pending `Q`/comparison success cannot discharge
    /// this premise; recording it supplies no fact or semantic acceptance.
    QIndependentSourceCallViewFormation,
    /// Pending source event-contribution, exact original upper complete-invocation
    /// output correspondence and typed receipt/receiver observation obligation.
    /// Original beta, source scope and whole xi = (nu, K, D) remain unresolved.
    /// This asserts no event, upper view, output, receipt or receiver existence,
    /// Flow, protection, admission, Q independence discharge or semantics.
    SourceEventContributionAndTypedOutputObservation,
    /// Named source-producer stub only: both rule applicability and interpretation
    /// remain pending. A direct resolved use need not denote a formal. Formal status,
    /// the relevant component, annotation status and ordinary-Value typing are
    /// unresolved, as is interpretation of the whole original xi = (nu, K, D).
    /// Actual role/entry, typed paths, profiles, receipts and independent admission
    /// remain unresolved. No semantic judgment or Q success discharges this stub.
    SourceFormalUseRuleApplicabilityAndInterpretation,
    /// Pending directional source-producer obligation only: seed applicability,
    /// original upper-use, exact typed output-effect occurrence/source correspondence,
    /// original scope and whole xi = (nu, K, D) remain unresolved. This records no
    /// formal applicability, annotation absence, seed, upper use, output port,
    /// profile membership, no-backflow property, receipt, Flow, admission or
    /// semantic discharge; shape or Q success supplies none of these facts.
    SourceDirectionalOutputEffectProtectionIntroduction,
}

#[derive(Debug)]
pub struct PendingPremise {
    pub(crate) call: ExprId,
    pub(crate) premise: Premise,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShadowError {
    MalformedSource,
    SyntaxDepthLimit,
    ElementLimit,
    UnsupportedExpression {
        kind: SyntaxKind,
        range: Range<usize>,
    },
    InvalidRange {
        range: Range<usize>,
    },
    DuplicateBinder {
        range: Range<usize>,
    },
    UnboundName {
        range: Range<usize>,
    },
    ForeignArtifact,
    MissingReference {
        index: usize,
    },
    InvalidUseReference,
    InvalidCallReference,
    InvalidExpressionReference,
}

fn build_skeleton(
    parsed: &ParsedFile,
    identity: Arc<()>,
    root: SyntaxNode,
    positions: &HashMap<SyntaxNode, Option<PositionId>>,
    raw_positions: &[Position],
    annotations: &[AnnotationOccurrence],
) -> Result<Skeleton, ShadowError> {
    let source = parsed.source();
    // The shared envelope is one direct root binding. Root trivia (the four
    // syntax trivia kinds) and the root parser's semicolon separators may
    // surround it; no sibling or enclosing semantic node is discarded.
    let mut statements = Vec::new();
    for element in root.children_with_tokens() {
        if let Some(node) = element.as_node() {
            if node.kind() != SyntaxKind::BindingStatement {
                return Err(ShadowError::MalformedSource);
            }
            statements.push(node.clone());
        } else if !matches!(
            element.kind(),
            SyntaxKind::Whitespace
                | SyntaxKind::Newline
                | SyntaxKind::LineComment
                | SyntaxKind::BlockComment
                | SyntaxKind::Semicolon
        ) {
            return Err(ShadowError::MalformedSource);
        }
    }
    let [statement] = statements.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let header = only_child(statement, SyntaxKind::BindingHeader)?;
    let target = only_child(&header, SyntaxKind::Pattern)?;
    let parts = target.children().collect::<Vec<_>>();
    let Some((name, parameters)) = parts.split_first() else {
        return Err(ShadowError::MalformedSource);
    };
    identifier(name, source)?;
    if parameters.is_empty() {
        return Err(ShadowError::MalformedSource);
    }

    let annotation_ids = annotations
        .iter()
        .map(|annotation| (annotation.position.0.index, annotation.id.clone()))
        .collect::<HashMap<_, _>>();
    let mut parameter_annotations = Vec::new();
    let mut binders = Vec::<Binder>::new();
    let mut names = BTreeSet::new();
    for parameter in parameters {
        if parameter.kind() != SyntaxKind::PatternMlApplicationTail {
            return Err(ShadowError::MalformedSource);
        }
        let pattern = only_child(parameter, SyntaxKind::Pattern)?;
        let (binder_node, annotation_node) = parameter_pattern(&pattern)?;
        if let Some(annotation_node) = annotation_node {
            let position = positions
                .get(&annotation_node)
                .and_then(Option::as_ref)
                .ok_or(ShadowError::MalformedSource)?;
            let annotation = annotation_ids
                .get(&position.0.index)
                .cloned()
                .ok_or(ShadowError::MalformedSource)?;
            parameter_annotations.push(ParameterAnnotationIncidence {
                parameter: BinderId(LocalId {
                    artifact: identity.clone(),
                    index: binders.len(),
                }),
                annotation,
            });
        }
        let (name, range) = identifier(&binder_node, source)?;
        if !names.insert(name.clone()) {
            return Err(ShadowError::DuplicateBinder { range });
        }
        binders.push(Binder {
            name,
            range,
            position: positions
                .get(&binder_node)
                .and_then(Option::as_ref)
                .cloned()
                .ok_or(ShadowError::MalformedSource)?,
        });
    }
    let body = only_child(statement, SyntaxKind::BindingBody)?;
    let chain = only_child(&body, SyntaxKind::OperatorChain)?;
    let mut artifact = Skeleton {
        root_header: None,
        body: ExprId(LocalId {
            artifact: identity.clone(),
            index: 0,
        }),
        identity,
        binders,
        expressions: Vec::new(),
        uses: Vec::new(),
        use_positions: Vec::new(),
        capture_uses: Vec::new(),
        parameter_annotations,
        pending: Vec::new(),
    };
    artifact.body = if chain
        .children()
        .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    {
        if !artifact.parameter_annotations.is_empty() {
            return Err(ShadowError::MalformedSource);
        }
        artifact.project_selected_nested(statement, chain, source, positions)?
    } else {
        artifact.project(chain, source, positions)?
    };
    // Publish the declaration identity after projection so it cannot resolve in
    // its body. Annotation-bearing sources retain their direct-body eligibility.
    let header_elements = header
        .children_with_tokens()
        .filter(|element| {
            !matches!(
                element.kind(),
                SyntaxKind::Whitespace
                    | SyntaxKind::Newline
                    | SyntaxKind::LineComment
                    | SyntaxKind::BlockComment
            )
        })
        .map(|element| element.kind())
        .collect::<Vec<_>>();
    let direct_body = match artifact.expression(&artifact.body)?.form() {
        Form::Use { .. } | Form::IntegerLiteral { .. } => true,
        Form::Apply {
            callee, argument, ..
        } => [callee, argument].into_iter().all(|id| {
            matches!(
                artifact.expression(id).map(Expression::form),
                Ok(Form::Use { .. } | Form::IntegerLiteral { .. })
            )
        }),
        _ => false,
    };
    if parameters.len() == 1
        && header_elements == [SyntaxKind::MyKw, SyntaxKind::Pattern, SyntaxKind::Equals]
        && (direct_body
            || (artifact.parameter_annotations.is_empty()
                && artifact.expressions.iter().all(|expression| {
                    matches!(
                        expression.form(),
                        Form::Use { .. }
                            | Form::IntegerLiteral { .. }
                            | Form::Group { .. }
                            | Form::Apply { .. }
                    )
                })))
    {
        let (name_text, range) = identifier(name, source)?;
        let binding = BinderId(artifact.id(artifact.binders.len()));
        artifact.binders.push(Binder {
            name: name_text,
            range,
            position: retained_position(positions, name)?,
        });
        let root = artifact.push_expression(
            retained_position(positions, statement)?,
            range_of(statement),
            Form::Lambda {
                binding,
                parameter: BinderId(artifact.id(0)),
                body: artifact.body.clone(),
                captures: Vec::new(),
                correspondence:
                    ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge,
            },
        );
        artifact.validate_nested_scope(&root)?;
    }
    let source_use_stubs = artifact
        .resolved_call_incidences()
        .flat_map(|incidence| {
            [
                Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
                Premise::SourceDirectionalOutputEffectProtectionIntroduction,
            ]
            .map(|premise| PendingPremise {
                call: incidence.application().expression().clone(),
                premise,
            })
        })
        .collect::<Vec<_>>();
    artifact.root_header = Some(RootDeclarationHeader {
        statement: retained_position(positions, statement)?,
        header: retained_position(positions, &header)?,
        name: retained_position(positions, name)?,
        parameters: (0..parameters.len())
            .map(|index| BinderId(artifact.id(index)))
            .collect(),
        body: artifact.body.clone(),
    });
    artifact.pending.extend(source_use_stubs);
    artifact.validate()?;
    artifact.validate_positions(raw_positions)?;
    Ok(artifact)
}
fn parameter_pattern(
    pattern: &SyntaxNode,
) -> Result<(SyntaxNode, Option<SyntaxNode>), ShadowError> {
    let children = pattern.children().collect::<Vec<_>>();
    match children.as_slice() {
        [identifier] if identifier.kind() == SyntaxKind::IdentifierPattern => {
            Ok((identifier.clone(), None))
        }
        [group] if group.kind() == SyntaxKind::ParenthesizedPattern => {
            let inner = only_child(group, SyntaxKind::Pattern)?;
            if group.children().count() != 1 {
                return Err(ShadowError::MalformedSource);
            }
            let children = inner.children().collect::<Vec<_>>();
            match children.as_slice() {
                [identifier, annotation]
                    if identifier.kind() == SyntaxKind::IdentifierPattern
                        && annotation.kind() == SyntaxKind::PatternTypeAnnotation =>
                {
                    Ok((identifier.clone(), Some(annotation.clone())))
                }
                _ => Err(ShadowError::MalformedSource),
            }
        }
        _ => Err(ShadowError::MalformedSource),
    }
}

fn only_child(node: &SyntaxNode, kind: SyntaxKind) -> Result<SyntaxNode, ShadowError> {
    let children = node.children().collect::<Vec<_>>();
    let matching = children
        .iter()
        .filter(|child| child.kind() == kind)
        .collect::<Vec<_>>();
    let [child] = matching.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    // Header and statement contain other structural nodes; atomic patterns and
    // the bounded body must not hide additional source operands.
    if matches!(
        node.kind(),
        SyntaxKind::Pattern | SyntaxKind::PatternMlApplicationTail | SyntaxKind::BindingBody
    ) && children.len() != 1
    {
        return Err(ShadowError::MalformedSource);
    }
    Ok((*child).clone())
}

fn identifier(node: &SyntaxNode, source: &str) -> Result<(String, Range<usize>), ShadowError> {
    if node.kind() != SyntaxKind::IdentifierPattern {
        return Err(ShadowError::MalformedSource);
    }
    let tokens = raw_children(node);
    let [token] = tokens.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let RawElement::Token(token) = token else {
        return Err(ShadowError::MalformedSource);
    };
    if token.kind() != SyntaxKind::Identifier {
        return Err(ShadowError::MalformedSource);
    }
    let range = range_of_token(token);
    let text = source
        .get(range.clone())
        .ok_or_else(|| ShadowError::InvalidRange {
            range: range.clone(),
        })?;
    Ok((text.to_owned(), range))
}

impl Skeleton {
    pub fn root_declaration_header(&self) -> Option<&RootDeclarationHeader> {
        self.root_header.as_ref()
    }

    fn id(&self, index: usize) -> LocalId {
        LocalId {
            artifact: self.identity.clone(),
            index,
        }
    }

    fn check_id(&self, id: &LocalId, length: usize) -> Result<(), ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        if id.index >= length {
            return Err(ShadowError::MissingReference { index: id.index });
        }
        Ok(())
    }

    pub fn expression(&self, id: &ExprId) -> Result<&Expression, ShadowError> {
        self.check_id(&id.0, self.expressions.len())?;
        Ok(&self.expressions[id.0.index])
    }

    /// Every retained expression, including declarations outside the designated body.
    pub fn retained_expressions(&self) -> impl ExactSizeIterator<Item = (ExprId, &Expression)> {
        self.expressions
            .iter()
            .enumerate()
            .map(|(index, expression)| (ExprId(self.id(index)), expression))
    }

    /// Checked storage address for joins; the address is not a lexical identity.
    pub fn expression_offset(&self, id: &ExprId) -> Result<usize, ShadowError> {
        self.check_id(&id.0, self.expressions.len())?;
        Ok(id.0.index)
    }

    /// Joins an existing capture record to its exact retained direct call.
    pub fn capture_call(&self, capture: &CaptureUseIncidence) -> Result<&ExprId, ShadowError> {
        let Form::Lambda { body, captures, .. } = self.expression(capture.lambda())?.form() else {
            return Err(ShadowError::InvalidExpressionReference);
        };
        self.binder(capture.captured())?;
        let Form::Apply { callee, .. } = self.expression(body)?.form() else {
            return Err(ShadowError::InvalidCallReference);
        };
        let Form::Use { binder, occurrence } = self.expression(callee)?.form() else {
            return Err(ShadowError::InvalidUseReference);
        };
        if captures.as_slice() != std::slice::from_ref(capture.captured())
            || binder != capture.captured()
            || occurrence != capture.occurrence()
            || self.use_position(occurrence)? != capture.position()
            || !std::ptr::eq(self.use_expression(occurrence)?, self.expression(callee)?)
        {
            return Err(ShadowError::InvalidUseReference);
        }
        Ok(body)
    }

    fn validate(&self) -> Result<(), ShadowError> {
        self.expression(&self.body)?;
        for (index, expression) in self.expressions.iter().enumerate() {
            match &expression.form {
                Form::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    ..
                } => {
                    self.check_id(&binding.0, self.binders.len())?;
                    self.check_id(&parameter.0, self.binders.len())?;
                    for capture in captures {
                        self.check_id(&capture.0, self.binders.len())?;
                    }
                    self.check_child(body, index)?;
                }
                Form::Bind {
                    binder,
                    value,
                    body,
                } => {
                    self.check_id(&binder.0, self.binders.len())?;
                    self.check_child(value, index)?;
                    self.check_child(body, index)?;
                }
                Form::IntegerLiteral { .. } => {}
                Form::Use { binder, occurrence } => {
                    self.check_id(&binder.0, self.binders.len())?;
                    self.check_id(&occurrence.0, self.uses.len())?;
                    if self.uses[occurrence.0.index] != ExprId(self.id(index)) {
                        return Err(ShadowError::InvalidUseReference);
                    }
                }
                Form::Group { inner } => {
                    self.check_child(inner, index)?;
                }
                Form::Apply {
                    callee, argument, ..
                } => {
                    self.check_child(callee, index)?;
                    self.check_child(argument, index)?;
                }
            }
        }
        if matches!(self.expression(&self.body)?.form, Form::Lambda { .. }) {
            self.validate_nested_scope(&self.body)?;
        }
        self.validate_capture_uses()?;
        for pending in &self.pending {
            if !matches!(self.expression(&pending.call)?.form, Form::Apply { .. }) {
                return Err(ShadowError::InvalidCallReference);
            }
        }
        Ok(())
    }

    fn validate_capture_uses(&self) -> Result<(), ShadowError> {
        let mut recorded = BTreeSet::new();
        for incidence in &self.capture_uses {
            self.check_id(&incidence.captured.0, self.binders.len())?;
            let Form::Lambda { body, captures, .. } = &self.expression(&incidence.lambda)?.form
            else {
                return Err(ShadowError::InvalidExpressionReference);
            };
            let Form::Apply { callee, .. } = &self.expression(body)?.form else {
                return Err(ShadowError::InvalidCallReference);
            };
            let Form::Use { binder, occurrence } = &self.expression(callee)?.form else {
                return Err(ShadowError::InvalidUseReference);
            };
            if captures.as_slice() != std::slice::from_ref(&incidence.captured)
                || binder != &incidence.captured
                || occurrence != &incidence.occurrence
                || self.use_position(&incidence.occurrence)? != &incidence.position
                || !recorded.insert(incidence.lambda.0.index)
            {
                return Err(ShadowError::InvalidUseReference);
            }
        }
        for (index, expression) in self.expressions.iter().enumerate() {
            if matches!(&expression.form, Form::Lambda { captures, .. } if !captures.is_empty())
                && !recorded.contains(&index)
            {
                return Err(ShadowError::InvalidUseReference);
            }
        }
        Ok(())
    }

    fn validate_nested_scope(&self, root: &ExprId) -> Result<(), ShadowError> {
        // Declaration identities are not visible in their initializer bodies.
        let mut tasks = vec![(root.clone(), BTreeSet::<usize>::new())];
        while let Some((id, scope)) = tasks.pop() {
            match &self.expression(&id)?.form {
                Form::Use { binder, .. } => {
                    if !scope.contains(&binder.0.index) {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                }
                Form::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    ..
                } => {
                    if binding == parameter {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                    let mut local = BTreeSet::from([parameter.0.index]);
                    for capture in captures {
                        if !scope.contains(&capture.0.index) || !local.insert(capture.0.index) {
                            return Err(ShadowError::InvalidExpressionReference);
                        }
                    }
                    tasks.push((body.clone(), local));
                }
                Form::Bind {
                    binder,
                    value,
                    body,
                } => {
                    if !matches!(&self.expression(value)?.form,
                        Form::Lambda { binding, .. } if binding == binder)
                    {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                    let mut after = scope.clone();
                    after.insert(binder.0.index);
                    tasks.push((body.clone(), after));
                    tasks.push((value.clone(), scope));
                }
                Form::Apply {
                    callee, argument, ..
                } => {
                    tasks.push((argument.clone(), scope.clone()));
                    tasks.push((callee.clone(), scope));
                }
                Form::Group { inner } => tasks.push((inner.clone(), scope)),
                Form::IntegerLiteral { .. } => {}
            }
        }
        Ok(())
    }

    fn validate_positions(&self, positions: &[Position]) -> Result<(), ShadowError> {
        for expression in &self.expressions {
            self.check_id(&expression.position.0, positions.len())?;
            let position = &positions[expression.position.0.index];
            let kind = match &expression.form {
                Form::Lambda { .. } => SyntaxKind::BindingStatement,
                Form::Bind { .. } => SyntaxKind::BracedStatementBlockExpression,
                Form::IntegerLiteral { .. } => SyntaxKind::IntegerLiteral,
                Form::Use { occurrence, .. } => {
                    if self.use_position(occurrence)? != &expression.position {
                        return Err(ShadowError::InvalidUseReference);
                    }
                    SyntaxKind::IdentifierExpression
                }
                Form::Group { .. } => SyntaxKind::ParenthesizedExpression,
                Form::Apply { source_form, .. } => *source_form,
            };
            if !position.is_node || position.kind != kind {
                return Err(ShadowError::InvalidExpressionReference);
            }
        }
        Ok(())
    }

    fn check_child(&self, child: &ExprId, parent: usize) -> Result<(), ShadowError> {
        self.expression(child)?;
        // Construction publishes children first. This rejects cyclic or forward
        // references before any recursive structural comparison can consume them.
        if child.0.index >= parent {
            return Err(ShadowError::InvalidExpressionReference);
        }
        Ok(())
    }
}

#[derive(Clone)]
enum RawElement {
    Node(SyntaxNode),
    Token(SyntaxToken),
}
impl RawElement {
    fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(n) => n.kind(),
            Self::Token(t) => t.kind(),
        }
    }
    fn as_node(&self) -> Option<&SyntaxNode> {
        match self {
            Self::Node(n) => Some(n),
            _ => None,
        }
    }
    fn range(&self) -> Range<usize> {
        match self {
            Self::Node(n) => range_of(n),
            Self::Token(t) => range_of_token(t),
        }
    }
}
fn raw_children(node: &SyntaxNode) -> Vec<RawElement> {
    node.children_with_tokens()
        .map(|e| {
            if let Some(n) = e.as_node() {
                RawElement::Node(n.clone())
            } else {
                RawElement::Token(e.into_token().expect("raw element token"))
            }
        })
        .collect()
}

impl ShadowArtifact {
    #[cfg(test)]
    pub(crate) fn into_skeleton(self) -> Result<Skeleton, ShadowError> {
        self.skeleton
    }
}
impl Binder {
    /// Exact retained IdentifierPattern occurrence; no typed slot is implied.
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}
impl Expression {
    /// Exact retained source node; applications identify their CST call tail.
    /// This syntax occurrence carries no typed slot or call-view judgment.
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn form(&self) -> &Form {
        &self.form
    }
}
impl PendingPremise {
    pub fn call(&self) -> &ExprId {
        &self.call
    }
    pub fn premise(&self) -> Premise {
        self.premise
    }
}
impl Skeleton {
    pub fn parameter_annotations(&self) -> &[ParameterAnnotationIncidence] {
        &self.parameter_annotations
    }

    pub fn capture_uses(&self) -> &[CaptureUseIncidence] {
        &self.capture_uses
    }

    /// Lazily scans retained expressions without forming or discharging a call view.
    pub fn application_source_occurrences(
        &self,
    ) -> impl Iterator<Item = ApplicationSourceOccurrence<'_>> + '_ {
        self.expressions
            .iter()
            .enumerate()
            .filter_map(|(index, expression)| {
                let Form::Apply {
                    source_form,
                    callee,
                    argument,
                } = &expression.form
                else {
                    return None;
                };
                Some(ApplicationSourceOccurrence {
                    expression: ExprId(self.id(index)),
                    position: &expression.position,
                    source_form: *source_form,
                    callee,
                    argument,
                })
            })
    }

    /// Filters the lazy source scan to applications with an already resolved direct Use.
    /// Grouped or computed callees are not traversed to infer a callee identity.
    pub fn resolved_call_incidences(&self) -> impl Iterator<Item = ResolvedCallIncidence<'_>> + '_ {
        self.application_source_occurrences()
            .filter_map(|application| {
                let Form::Use { binder, occurrence } =
                    &self.expressions[application.callee.0.index].form
                else {
                    return None;
                };
                Some(ResolvedCallIncidence {
                    application,
                    occurrence,
                    binder,
                })
            })
    }

    /// Lazily joins retained direct-call references and same-binder annotation
    /// incidences. This supplies no judgment and leaves every premise pending;
    /// comparison Q cannot discharge any premise through this projection.
    pub fn source_call_use_inputs(&self) -> impl Iterator<Item = SourceCallUseInput<'_>> + '_ {
        self.resolved_call_incidences()
            .map(|call| SourceCallUseInput {
                call,
                parameter_annotations: &self.parameter_annotations,
            })
    }

    /// Joins only exact retained structural edges. Different topology or an
    /// invalid/foreign reference produces absence, without following wrappers.
    pub fn captured_call_input(&self) -> Option<CapturedCallInput<'_>> {
        let Form::Lambda {
            parameter, body, ..
        } = self.expression(&self.body).ok()?.form()
        else {
            return None;
        };
        self.binder(parameter).ok()?;
        let Form::Bind {
            binder,
            value,
            body: returned,
        } = self.expression(body).ok()?.form()
        else {
            return None;
        };
        self.binder(binder).ok()?;
        let Form::Lambda {
            binding,
            parameter: local_parameter,
            body: call,
            captures,
            ..
        } = self.expression(value).ok()?.form()
        else {
            return None;
        };
        if binding != binder || captures.as_slice() != std::slice::from_ref(parameter) {
            return None;
        }
        let returned_expression = self.expression(returned).ok()?;
        let Form::Use {
            binder: returned_binder,
            occurrence: returned_use,
        } = returned_expression.form()
        else {
            return None;
        };
        if returned_binder != binder
            || !std::ptr::eq(self.use_expression(returned_use).ok()?, returned_expression)
            || self.use_position(returned_use).ok()? != returned_expression.position()
        {
            return None;
        }
        let Form::Apply {
            callee, argument, ..
        } = self.expression(call).ok()?.form()
        else {
            return None;
        };
        self.binder(local_parameter).ok()?;
        let argument_expression = self.expression(argument).ok()?;
        let Form::Use {
            binder: argument_binder,
            occurrence: argument_use,
        } = argument_expression.form()
        else {
            return None;
        };
        if argument_binder != local_parameter
            || !std::ptr::eq(self.use_expression(argument_use).ok()?, argument_expression)
            || self.use_position(argument_use).ok()? != argument_expression.position()
        {
            return None;
        }
        let callee_expression = self.expression(callee).ok()?;
        let Form::Use {
            binder: callee_binder,
            occurrence,
        } = callee_expression.form()
        else {
            return None;
        };
        if callee_binder != parameter
            || !std::ptr::eq(self.use_expression(occurrence).ok()?, callee_expression)
            || self.use_position(occurrence).ok()? != callee_expression.position()
        {
            return None;
        }
        let capture = self.capture_uses.iter().find(|capture| {
            capture.lambda() == value
                && capture.captured() == parameter
                && capture.occurrence() == occurrence
                && capture.position() == callee_expression.position()
        })?;
        Some(CapturedCallInput {
            outer_parameter: parameter,
            local_lambda: value,
            local_binding: binder,
            returned_use,
            call,
            callee_use: occurrence,
            capture_position: capture.position(),
        })
    }

    pub fn body(&self) -> &ExprId {
        &self.body
    }
    pub fn expressions(&self) -> &[Expression] {
        &self.expressions
    }
    pub fn binders(&self) -> &[Binder] {
        &self.binders
    }
    pub fn uses(&self) -> &[ExprId] {
        &self.uses
    }
    pub fn pending(&self) -> &[PendingPremise] {
        &self.pending
    }
    pub fn binder(&self, id: &BinderId) -> Result<&Binder, ShadowError> {
        self.check_id(&id.0, self.binders.len())?;
        Ok(&self.binders[id.0.index])
    }
    /// Exact retained IdentifierExpression occurrence for this resolved use.
    pub fn use_position(&self, id: &UseId) -> Result<&PositionId, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        self.use_positions
            .get(id.0.index)
            .ok_or(ShadowError::InvalidUseReference)
    }
    pub fn use_expression(&self, id: &UseId) -> Result<&Expression, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        self.expression(&self.uses[id.0.index])
    }
    #[cfg(test)]
    pub(crate) fn binder_index(&self, id: &BinderId) -> Result<usize, ShadowError> {
        self.check_id(&id.0, self.binders.len())?;
        Ok(id.0.index)
    }
    #[cfg(test)]
    pub(crate) fn use_index(&self, id: &UseId) -> Result<usize, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        Ok(id.0.index)
    }
    #[cfg(test)]
    pub(crate) fn binder_ids(&self) -> Vec<BinderId> {
        (0..self.binders.len())
            .map(|i| BinderId(self.id(i)))
            .collect()
    }
    fn push_expression(&mut self, position: PositionId, range: Range<usize>, form: Form) -> ExprId {
        let id = ExprId(self.id(self.expressions.len()));
        if matches!(form, Form::Apply { .. }) {
            for premise in [
                Premise::CallableRole,
                Premise::FullFunctionMembership,
                Premise::CallViewRealization,
                Premise::QIndependentSourceCallViewFormation,
                Premise::SourceEventContributionAndTypedOutputObservation,
            ] {
                self.pending.push(PendingPremise {
                    call: id.clone(),
                    premise,
                });
            }
        }
        if matches!(form, Form::Use { .. }) {
            self.uses.push(id.clone());
        }
        self.expressions.push(Expression {
            position,
            range,
            form,
        });
        id
    }
    fn project_selected_nested(
        &mut self,
        outer: &SyntaxNode,
        chain: SyntaxNode,
        source: &str,
        positions: &HashMap<SyntaxNode, Option<PositionId>>,
    ) -> Result<ExprId, ShadowError> {
        // This recognizer owns only the approved lambda/bind/lambda/call/use
        // correspondence. It is not a general interpretation of brace blocks.
        let blocks = chain.children().collect::<Vec<_>>();
        let Some(block) = blocks
            .iter()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        else {
            return Err(unsupported(&chain));
        };
        let reject = || unsupported(block);
        if blocks.len() != 1 || self.binders.len() != 1 {
            return Err(reject());
        }
        let children = block.children().collect::<Vec<_>>();
        let [local_statement, separator, final_statement] = children.as_slice() else {
            return Err(reject());
        };
        if local_statement.kind() != SyntaxKind::Statement
            || separator.kind() != SyntaxKind::BlockStatementSeparator
            || final_statement.kind() != SyntaxKind::Statement
            || separator.children().next().is_some()
        {
            return Err(reject());
        }
        let separator_tokens = separator
            .children_with_tokens()
            .filter(|element| !matches!(element.kind(), SyntaxKind::Whitespace))
            .collect::<Vec<_>>();
        if separator_tokens.len() != 1 || separator_tokens[0].kind() != SyntaxKind::Semicolon {
            return Err(reject());
        }
        let local =
            only_child(local_statement, SyntaxKind::BindingStatement).map_err(|_| reject())?;
        if local_statement.children().count() != 1 || final_statement.children().count() != 1 {
            return Err(reject());
        }
        let header_nodes =
            |statement: &SyntaxNode| -> Result<(SyntaxNode, SyntaxNode), ShadowError> {
                let children = statement
                    .children()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>();
                if children != [SyntaxKind::BindingHeader, SyntaxKind::BindingBody] {
                    return Err(reject());
                }
                let header = only_child(statement, SyntaxKind::BindingHeader)?;
                let header_elements = header
                    .children_with_tokens()
                    .filter(|element| {
                        !matches!(
                            element.kind(),
                            SyntaxKind::Whitespace
                                | SyntaxKind::Newline
                                | SyntaxKind::LineComment
                                | SyntaxKind::BlockComment
                        )
                    })
                    .map(|element| element.kind())
                    .collect::<Vec<_>>();
                if header_elements != [SyntaxKind::MyKw, SyntaxKind::Pattern, SyntaxKind::Equals] {
                    return Err(reject());
                }
                let pattern = only_child(&header, SyntaxKind::Pattern)?;
                let nodes = pattern.children().collect::<Vec<_>>();
                let [name, tail] = nodes.as_slice() else {
                    return Err(reject());
                };
                identifier(name, source)?;
                if tail.kind() != SyntaxKind::PatternMlApplicationTail {
                    return Err(reject());
                }
                let parameter = only_child(tail, SyntaxKind::Pattern)?;
                let parameter = only_child(&parameter, SyntaxKind::IdentifierPattern)?;
                Ok((name.clone(), parameter))
            };
        let (outer_name, _) = header_nodes(outer).map_err(|_| reject())?;
        let (local_name, local_parameter) = header_nodes(&local).map_err(|_| reject())?;
        let local_body = only_child(&local, SyntaxKind::BindingBody).map_err(|_| reject())?;
        let local_chain =
            only_child(&local_body, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let call_nodes = local_chain.children().collect::<Vec<_>>();
        let [callee, argument] = call_nodes.as_slice() else {
            return Err(reject());
        };
        if callee.kind() != SyntaxKind::IdentifierExpression
            || argument.kind() != SyntaxKind::MlArgument
        {
            return Err(reject());
        }
        let argument_chain =
            only_child(argument, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let arguments = argument_chain.children().collect::<Vec<_>>();
        let final_chain =
            only_child(final_statement, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let returns = final_chain.children().collect::<Vec<_>>();
        let ([argument_use], [returned_use]) = (arguments.as_slice(), returns.as_slice()) else {
            return Err(reject());
        };
        if argument_use.kind() != SyntaxKind::IdentifierExpression
            || returned_use.kind() != SyntaxKind::IdentifierExpression
        {
            return Err(reject());
        }
        let (step_name, _) = identifier(&local_name, source)?;
        let (x_name, _) = identifier(&local_parameter, source)?;
        let f_name = &self.binders[0].name;
        // Admission is deliberately bounded to the approved named source
        // candidate. These spellings select no inference or runtime behavior.
        if identifier(&outer_name, source)?.0 != "apply"
            || f_name != "f"
            || step_name != "step"
            || x_name != "x"
            || source.get(range_of(callee)) != Some(f_name.as_str())
            || source.get(range_of(argument_use)) != Some(x_name.as_str())
            || source.get(range_of(returned_use)) != Some(step_name.as_str())
            || x_name == *f_name
            || step_name == *f_name
            || step_name == x_name
        {
            return Err(reject());
        }
        let add_binder =
            |artifact: &mut Self, node: &SyntaxNode| -> Result<BinderId, ShadowError> {
                let (name, range) = identifier(node, source)?;
                let id = BinderId(artifact.id(artifact.binders.len()));
                artifact.binders.push(Binder {
                    name,
                    range,
                    position: retained_position(positions, node)?,
                });
                Ok(id)
            };
        let f = BinderId(self.id(0));
        let x = add_binder(self, &local_parameter)?;
        // Project the local initializer before publishing the sequential local
        // binder: step is unavailable in its own body. Only f and x are in scope.
        let call = self.project(local_chain, source, positions)?;
        let step = add_binder(self, &local_name)?;
        let local_lambda = self.push_expression(
            retained_position(positions, &local)?,
            range_of(&local),
            Form::Lambda {
                binding: step.clone(),
                parameter: x,
                body: call.clone(),
                captures: vec![f.clone()],
                correspondence:
                    ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge,
            },
        );
        let Form::Apply { callee, .. } = &self.expression(&call)?.form else {
            return Err(ShadowError::InvalidCallReference);
        };
        let Form::Use { occurrence, .. } = &self.expression(callee)?.form else {
            return Err(ShadowError::InvalidUseReference);
        };
        self.capture_uses.push(CaptureUseIncidence {
            lambda: local_lambda.clone(),
            captured: f.clone(),
            occurrence: occurrence.clone(),
            position: self.use_position(occurrence)?.clone(),
        });
        // The recognizer requires the final use to be step; x has no use here.
        let returned = self.project(final_chain, source, positions)?;
        let bound = self.push_expression(
            retained_position(positions, block)?,
            range_of(block),
            Form::Bind {
                binder: step,
                value: local_lambda,
                body: returned,
            },
        );
        let apply = add_binder(self, &outer_name)?;
        Ok(self.push_expression(
            retained_position(positions, outer)?,
            range_of(outer),
            Form::Lambda {
                binding: apply,
                parameter: f,
                body: bound,
                captures: Vec::new(),
                correspondence:
                    ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge,
            },
        ))
    }
    fn project(
        &mut self,
        root: SyntaxNode,
        source: &str,
        positions: &HashMap<SyntaxNode, Option<PositionId>>,
    ) -> Result<ExprId, ShadowError> {
        // Tasks/results hold IDs and CST handles, never recursively owned expressions.
        enum Task {
            Visit(SyntaxNode),
            Group(PositionId, Range<usize>),
            Chain(Vec<(PositionId, SyntaxKind, Range<usize>)>),
        }
        let names = self
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| (b.name.clone(), i))
            .collect::<BTreeMap<_, _>>();
        let mut tasks = vec![Task::Visit(root)];
        let mut results = Vec::<ExprId>::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    match node.kind() {
                        SyntaxKind::IntegerLiteral => {
                            if node.children().next().is_some() {
                                return Err(unsupported(&node));
                            }
                            let range = range_of(&node);
                            let spelling = source.get(range.clone()).ok_or_else(|| {
                                ShadowError::InvalidRange {
                                    range: range.clone(),
                                }
                            })?;
                            results.push(self.push_expression(
                                retained_position(positions, &node)?,
                                range,
                                Form::IntegerLiteral {
                                    spelling: spelling.to_owned(),
                                },
                            ));
                        }
                        SyntaxKind::IdentifierExpression => {
                            if node.children().next().is_some() {
                                return Err(unsupported(&node));
                            }
                            let range = range_of(&node);
                            let name = source.get(range.clone()).ok_or_else(|| {
                                ShadowError::InvalidRange {
                                    range: range.clone(),
                                }
                            })?;
                            let index = names.get(name).copied().ok_or_else(|| {
                                ShadowError::UnboundName {
                                    range: range.clone(),
                                }
                            })?;
                            let position = positions
                                .get(&node)
                                .and_then(Option::as_ref)
                                .cloned()
                                .ok_or(ShadowError::MalformedSource)?;
                            self.use_positions.push(position.clone());
                            let occurrence = UseId(self.id(self.uses.len()));
                            let binder = BinderId(self.id(index));
                            results.push(self.push_expression(
                                position,
                                range,
                                Form::Use { binder, occurrence },
                            ));
                        }
                        SyntaxKind::ParenthesizedExpression => {
                            let inner = nested_chain(&node)?;
                            tasks.push(Task::Group(
                                retained_position(positions, &node)?,
                                range_of(&node),
                            ));
                            tasks.push(Task::Visit(inner));
                        }
                        SyntaxKind::OperatorChain => {
                            let children = node.children().collect::<Vec<_>>();
                            let Some((first, tails)) = children.split_first() else {
                                return Err(unsupported(&node));
                            };
                            if !matches!(
                                first.kind(),
                                SyntaxKind::IdentifierExpression
                                    | SyntaxKind::ParenthesizedExpression
                                    | SyntaxKind::IntegerLiteral
                            ) {
                                return Err(unsupported(first));
                            }
                            let mut arguments = Vec::new();
                            let mut forms = Vec::new();
                            for tail in tails {
                                if !matches!(
                                    tail.kind(),
                                    SyntaxKind::MlArgument | SyntaxKind::CallTail
                                ) {
                                    return Err(unsupported(tail));
                                }
                                arguments.push(nested_chain(tail)?);
                                forms.push((
                                    retained_position(positions, tail)?,
                                    tail.kind(),
                                    range_of(tail),
                                ));
                            }
                            tasks.push(Task::Chain(forms));
                            for argument in arguments.into_iter().rev() {
                                tasks.push(Task::Visit(argument));
                            }
                            tasks.push(Task::Visit(first.clone()));
                        }
                        _ => return Err(unsupported(&node)),
                    }
                }
                Task::Group(position, range) => {
                    let inner = results.pop().ok_or(ShadowError::MalformedSource)?;
                    results.push(self.push_expression(position, range, Form::Group { inner }));
                }
                Task::Chain(forms) => {
                    let start = results
                        .len()
                        .checked_sub(forms.len() + 1)
                        .ok_or(ShadowError::MalformedSource)?;
                    let operands = results.split_off(start);
                    let mut operands = operands.into_iter();
                    let mut callee = operands.next().ok_or(ShadowError::MalformedSource)?;
                    for ((position, source_form, tail_range), argument) in
                        forms.into_iter().zip(operands)
                    {
                        let range = self.expression(&callee)?.range.start.min(tail_range.start)
                            ..self.expression(&callee)?.range.end.max(tail_range.end);
                        callee = self.push_expression(
                            position,
                            range,
                            Form::Apply {
                                source_form,
                                callee,
                                argument,
                            },
                        );
                    }
                    results.push(callee);
                }
            }
        }
        if results.len() != 1 {
            return Err(ShadowError::MalformedSource);
        }
        Ok(results.pop().expect("one projection"))
    }
}
fn retained_position(
    positions: &HashMap<SyntaxNode, Option<PositionId>>,
    node: &SyntaxNode,
) -> Result<PositionId, ShadowError> {
    positions
        .get(node)
        .and_then(Option::as_ref)
        .cloned()
        .ok_or(ShadowError::MalformedSource)
}

fn unsupported(node: &SyntaxNode) -> ShadowError {
    ShadowError::UnsupportedExpression {
        kind: node.kind(),
        range: range_of(node),
    }
}
fn nested_chain(node: &SyntaxNode) -> Result<SyntaxNode, ShadowError> {
    // Match the existing narrow associator's nested-chain collection, without recursion.
    let mut stack = node.children().collect::<Vec<_>>();
    let mut chains = Vec::new();
    while let Some(child) = stack.pop() {
        if child.kind() == SyntaxKind::OperatorChain {
            chains.push(child);
        } else {
            stack.extend(child.children());
        }
    }
    if chains.len() != 1 {
        return Err(unsupported(node));
    }
    Ok(chains.pop().expect("one nested chain"))
}

#[cfg(test)]
#[path = "tests/shadow_raw_source_inventory.rs"]
mod raw_source_inventory_tests;

#[cfg(test)]
#[path = "tests/shadow_resolved_application_identity.rs"]
mod shadow_resolved_application_identity;

#[cfg(test)]
mod tests {
    use super::*;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    fn hir_identity() -> ModuleIdentity {
        ModuleIdentity::source_root(crate::FileId::new(crate::FileKey::new(
            "test",
            "source-identity.yu",
        )))
    }

    #[test]
    fn source_identity_correspondence_joins_exact_declaration_and_use() {
        let parsed = parsed("my f x = x; my same = f; my another = f");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        let mut uses = Vec::new();
        for item in hir.items() {
            let crate::HirItem::Binding(binding) = item else {
                panic!("binding")
            };
            let declaration = shadow
                .definition_source_position(&hir, binding.definition_root())
                .unwrap();
            assert_eq!(
                shadow.position(&declaration).unwrap().kind(),
                SyntaxKind::BindingStatement
            );
            let body = match binding.value() {
                crate::ResolvedExpr::Lambda { body, .. } => body.as_ref(),
                body => body,
            };
            let position = shadow
                .occurrence_source_position(&hir, body.occurrence())
                .unwrap();
            assert_eq!(
                shadow.position(&position).unwrap().kind(),
                SyntaxKind::IdentifierExpression
            );
            uses.push(position);
        }
        assert_eq!(uses.len(), 3);
        assert_ne!(uses[1], uses[2]);
        assert_eq!(
            hir,
            crate::lower_module(hir_identity(), &parsed, SemanticImports::empty()).unwrap()
        );
        fn send_sync<T: Send + Sync>() {}
        send_sync::<HirModule>();
        send_sync::<ShadowArtifact>();
        send_sync::<SourceNodeKey>();
    }

    #[test]
    fn source_identity_correspondence_rejects_foreign_hir_parse_and_missing_sidecar() {
        let parsed = parsed("my x = 1");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let foreign_hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let default_hir =
            crate::lower_module(hir_identity(), &parsed, SemanticImports::empty()).unwrap();
        let root = |hir: &HirModule| match &hir.items()[0] {
            crate::HirItem::Binding(binding) => binding.definition_root().clone(),
            _ => panic!("binding"),
        };
        let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        assert_eq!(
            shadow.definition_source_position(&hir, &root(&foreign_hir)),
            Err(SourceIdentityError::ForeignHirArtifact)
        );
        assert_eq!(
            shadow.definition_source_position(&default_hir, &root(&default_hir)),
            Err(SourceIdentityError::MissingSource)
        );
        let foreign_shadow = ShadowArtifact::from_parsed(self::parsed("my x = 1")).unwrap();
        assert_eq!(
            foreign_shadow.definition_source_position(&hir, &root(&hir)),
            Err(SourceIdentityError::ForeignParse)
        );
        assert_eq!(
            foreign_shadow.source_position(&parsed.source_root().key()),
            Err(SourceIdentityError::ForeignParse)
        );
    }

    #[test]
    fn source_identity_correspondence_reports_missing_and_ambiguous_keys() {
        let parsed = parsed("my x = 1");
        let key = parsed.source_root().key();
        let mut shadow = ShadowArtifact::from_parsed(parsed).unwrap();
        shadow.retain_source_position(key.clone(), shadow.root());
        assert_eq!(
            shadow.source_position(&key),
            Err(SourceIdentityError::AmbiguousSource)
        );
        shadow.source_positions.remove(&key);
        assert_eq!(
            shadow.source_position(&key),
            Err(SourceIdentityError::MissingSource)
        );
    }

    #[test]
    fn source_identity_correspondence_rejects_foreign_occurrence_and_missing_synthetic_source() {
        let parsed = parsed("my f x = x");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let foreign =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let shadow = ShadowArtifact::from_parsed(parsed).unwrap();
        let value = |hir: &HirModule| match &hir.items()[0] {
            crate::HirItem::Binding(binding) => binding.value().occurrence().clone(),
            _ => panic!("binding"),
        };
        assert_eq!(
            shadow.occurrence_source_position(&hir, &value(&foreign)),
            Err(SourceIdentityError::ForeignHirArtifact)
        );
        assert_eq!(
            shadow.occurrence_source_position(&hir, &value(&hir)),
            Err(SourceIdentityError::MissingSource)
        );
    }

    #[test]
    fn source_identity_correspondence_joins_exact_parameters_with_repeated_names() {
        let parsed = parsed("my f x = x; my g x = x");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let ordinary =
            crate::lower_module(hir_identity(), &parsed, SemanticImports::empty()).unwrap();
        assert_eq!(hir, ordinary);
        assert!(ordinary.source_identity.is_none());
        let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        let mut positions = Vec::new();
        for item in hir.items() {
            let crate::HirItem::Binding(binding) = item else {
                panic!("binding")
            };
            let parameter = &binding.parameters()[0];
            let position = shadow
                .parameter_source_position(&hir, parameter.id())
                .unwrap();
            assert_eq!(
                shadow.position(&position).unwrap().kind(),
                SyntaxKind::IdentifierPattern
            );
            assert_eq!(
                shadow.position(&position).unwrap().range(),
                parameter.range()
            );
            positions.push(position);
        }
        assert_ne!(positions[0], positions[1]);

        // The skeleton's smaller admitted envelope retains the same exact node.
        let parsed = self::parsed("my f x = x");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let shadow = ShadowArtifact::from_parsed(parsed).unwrap();
        let crate::HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let skeleton = shadow.skeleton().unwrap();
        let parameter = skeleton
            .expressions()
            .iter()
            .find_map(|expression| match expression.form() {
                Form::Lambda { parameter, .. } => Some(parameter),
                _ => None,
            })
            .expect("lambda parameter");
        assert_eq!(
            shadow
                .parameter_source_position(&hir, binding.parameters()[0].id())
                .unwrap(),
            *skeleton.binder(parameter).unwrap().position()
        );
    }

    #[test]
    fn source_identity_correspondence_rejects_foreign_parameters_and_missing_source() {
        let parsed = parsed("my f x = x");
        let mut hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let foreign =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let ordinary =
            crate::lower_module(hir_identity(), &parsed, SemanticImports::empty()).unwrap();
        let parameter = |hir: &HirModule| match &hir.items()[0] {
            crate::HirItem::Binding(binding) => binding.parameters()[0].id().clone(),
            _ => panic!("binding"),
        };
        let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        assert_eq!(
            shadow.parameter_source_position(&hir, &parameter(&foreign)),
            Err(SourceIdentityError::ForeignHirArtifact)
        );
        assert_eq!(
            shadow.parameter_source_position(&ordinary, &parameter(&ordinary)),
            Err(SourceIdentityError::MissingSource)
        );
        let foreign_shadow = ShadowArtifact::from_parsed(self::parsed("my f x = x")).unwrap();
        assert_eq!(
            foreign_shadow.parameter_source_position(&hir, &parameter(&hir)),
            Err(SourceIdentityError::ForeignParse)
        );
        let id = parameter(&hir);
        hir.source_identity.as_mut().unwrap().parameters.remove(&id);
        assert_eq!(
            shadow.parameter_source_position(&hir, &id),
            Err(SourceIdentityError::MissingSource)
        );
    }

    const NESTED: &str = "my apply f = { my step x = f x; step }";

    #[test]
    fn shadow_source_crosswalk_joins_exact_hir_parameter_to_retained_lambda() {
        let parsed = parsed("my f x = x x");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let pending_before = skeleton.pending().len();
        assert_eq!(pending_before, 7);
        let crosswalk = artifact.skeleton_source_crosswalk();
        let crate::HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let position = artifact
            .parameter_source_position(&hir, binding.parameters()[0].id())
            .unwrap();
        let (lambda, parameter) = crosswalk.parameter_at_position(&position).unwrap().unwrap();
        let Form::Lambda {
            binding: declaration,
            parameter: expected,
            ..
        } = lambda.form()
        else {
            panic!("lambda")
        };
        assert!(std::ptr::eq(parameter, expected));
        assert_eq!(skeleton.binder(parameter).unwrap().position(), &position);
        let (represented, retained_declaration) = crosswalk
            .definition_at_position(lambda.position())
            .unwrap()
            .unwrap();
        assert!(std::ptr::eq(represented, lambda));
        assert!(std::ptr::eq(retained_declaration, declaration));
        for expression in skeleton.expressions() {
            if let Form::Use { occurrence, .. } = expression.form() {
                assert!(std::ptr::eq(
                    crosswalk
                        .use_at_position(skeleton.use_position(occurrence).unwrap())
                        .unwrap()
                        .unwrap(),
                    occurrence,
                ));
            }
        }
        assert!(
            crosswalk
                .parameter_at_position(&artifact.root())
                .unwrap()
                .is_none()
        );
        assert_eq!(skeleton.pending().len(), pending_before);

        // Equal spellings in separate artifacts retain separate binder identities.
        let foreign = ShadowArtifact::from_parsed(self::parsed("my f x = x x")).unwrap();
        let foreign_crosswalk = foreign.skeleton_source_crosswalk();
        let foreign_skeleton = foreign.skeleton().unwrap();
        let foreign_parameter = foreign_skeleton
            .expressions()
            .iter()
            .find_map(|expression| match expression.form() {
                Form::Lambda { parameter, .. } => Some(parameter),
                _ => None,
            })
            .unwrap();
        let foreign_position = foreign_skeleton
            .binder(foreign_parameter)
            .unwrap()
            .position();
        let (_, joined_foreign) = foreign_crosswalk
            .parameter_at_position(foreign_position)
            .unwrap()
            .unwrap();
        assert_ne!(parameter, joined_foreign);
        assert_eq!(
            skeleton.binder(parameter).unwrap().name(),
            foreign_skeleton.binder(joined_foreign).unwrap().name()
        );
        assert!(matches!(
            crosswalk.parameter_at_position(foreign_position),
            Err(ShadowError::ForeignArtifact)
        ));
    }

    #[test]
    fn shadow_source_crosswalk_preserves_nested_pending_and_unsupported_envelope() {
        let artifact = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let crosswalk = artifact.skeleton_source_crosswalk();
        assert_eq!(skeleton.pending().len(), 7);
        let mut count = 0;
        for expression in skeleton.expressions() {
            if let Form::Lambda { parameter, .. } = expression.form() {
                let (lambda, retained) = crosswalk
                    .parameter_at_position(skeleton.binder(parameter).unwrap().position())
                    .unwrap()
                    .unwrap();
                assert!(std::ptr::eq(lambda, expression));
                assert!(std::ptr::eq(retained, parameter));
                count += 1;
            }
        }
        assert_eq!(count, 2);
        assert_eq!(skeleton.pending().len(), 7);

        let parsed = parsed("my f x = x; my g x = x");
        let hir =
            lower_module_with_source_identity(hir_identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let unsupported = ShadowArtifact::from_parsed(parsed).unwrap();
        assert!(unsupported.skeleton().is_err());
        let empty = unsupported.skeleton_source_crosswalk();
        let mut positions = Vec::new();
        for item in hir.items() {
            let crate::HirItem::Binding(binding) = item else {
                panic!("binding")
            };
            let position = unsupported
                .parameter_source_position(&hir, binding.parameters()[0].id())
                .unwrap();
            assert!(empty.parameter_at_position(&position).unwrap().is_none());
            positions.push(position);
        }
        assert_ne!(positions[0], positions[1]);
    }

    #[test]
    fn shadow_annotation_positions_rejects_missing_annotation_reference() {
        let artifact = ShadowArtifact::from_parsed(parsed("x as int")).unwrap();
        let index = artifact.annotations().len();
        let invalid = AnnotationId(LocalId {
            artifact: artifact.identity.clone(),
            index,
        });
        assert_eq!(
            artifact.annotation(&invalid).unwrap_err(),
            ShadowError::MissingReference { index }
        );
    }

    #[test]
    fn selected_nested_source_preserves_binders_scope_return_and_pending_boundary() {
        let artifact = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let Form::Lambda {
            binding: apply,
            parameter: f,
            body: block,
            captures,
            correspondence,
        } = skeleton.expression(skeleton.body()).unwrap().form()
        else {
            panic!("outer lambda")
        };
        assert!(captures.is_empty());
        assert_eq!(
            *correspondence,
            ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
        );
        assert_eq!(skeleton.binder(apply).unwrap().name(), "apply");
        assert_eq!(skeleton.binder(f).unwrap().name(), "f");
        let Form::Bind {
            binder: step,
            value,
            body: returned,
        } = skeleton.expression(block).unwrap().form()
        else {
            panic!("sequential bind")
        };
        let Form::Lambda {
            binding,
            parameter: x,
            body: call,
            captures,
            correspondence,
        } = skeleton.expression(value).unwrap().form()
        else {
            panic!("local lambda")
        };
        assert_eq!(binding, step);
        assert_eq!(captures, &vec![f.clone()]);
        assert_eq!(
            *correspondence,
            ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
        );
        assert_eq!(skeleton.binder(x).unwrap().name(), "x");
        assert_eq!(skeleton.binder(step).unwrap().name(), "step");
        let Form::Apply {
            callee,
            argument,
            source_form,
        } = skeleton.expression(call).unwrap().form()
        else {
            panic!("f x")
        };
        assert_eq!(*source_form, SyntaxKind::MlArgument);
        let [incidence] = skeleton.capture_uses() else {
            panic!("one lexical capture-use incidence")
        };
        assert_eq!(incidence.lambda(), value);
        assert_eq!(incidence.captured(), f);
        let Form::Use { occurrence, .. } = skeleton.expression(callee).unwrap().form() else {
            panic!("callee use")
        };
        assert_eq!(incidence.occurrence(), occurrence);
        assert_eq!(
            incidence.position(),
            skeleton.use_position(occurrence).unwrap()
        );
        for (id, expected_binder, expected_range) in [
            (callee, f, 27..28),
            (argument, x, 29..30),
            (returned, step, 32..36),
        ] {
            let expression = skeleton.expression(id).unwrap();
            let Form::Use { binder, occurrence } = expression.form() else {
                panic!("resolved use")
            };
            assert_eq!(binder, expected_binder);
            assert_eq!(*expression.range(), expected_range);
            assert_eq!(
                skeleton.use_position(occurrence).unwrap(),
                expression.position()
            );
            assert_eq!(
                artifact.position(expression.position()).unwrap().kind(),
                SyntaxKind::IdentifierExpression
            );
        }
        assert_eq!(skeleton.uses().len(), 3);
        assert_eq!(skeleton.pending().len(), 7);
        for (pending, expected) in skeleton.pending().iter().zip([
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceEventContributionAndTypedOutputObservation,
            Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
            Premise::SourceDirectionalOutputEffectProtectionIntroduction,
        ]) {
            assert_eq!(pending.call(), call);
            assert_eq!(pending.premise(), expected);
        }
        for binder in skeleton.binders() {
            let position = artifact.position(binder.position()).unwrap();
            assert_eq!(position.kind(), SyntaxKind::IdentifierPattern);
            assert_eq!(position.range(), binder.range());
        }
        // A separately parsed artifact must never share identities.
        let other = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        assert_eq!(
            other.skeleton().unwrap().binder(f).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }

    #[test]
    fn selected_capture_use_incidence_rejects_inconsistent_links() {
        let artifact = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let mut skeleton = artifact.into_skeleton().unwrap();
        let other = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let other = other.skeleton().unwrap();
        let saved_lambda = skeleton.capture_uses[0].lambda.clone();
        skeleton.capture_uses[0].lambda = other.capture_uses[0].lambda.clone();
        assert_eq!(skeleton.validate(), Err(ShadowError::ForeignArtifact));
        skeleton.capture_uses[0].lambda = saved_lambda;

        let saved_binder = skeleton.capture_uses[0].captured.clone();
        skeleton.capture_uses[0].captured = BinderId(skeleton.id(1));
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].captured = saved_binder;

        let saved_use = skeleton.capture_uses[0].occurrence.clone();
        skeleton.capture_uses[0].occurrence = UseId(skeleton.id(1));
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].occurrence = saved_use;

        let saved_position = skeleton.capture_uses[0].position.clone();
        skeleton.capture_uses[0].position = skeleton.use_positions[1].clone();
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].position = saved_position;
        skeleton.validate().unwrap();
        skeleton.capture_uses.clear();
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
    }

    #[test]
    fn selected_nested_scope_accepts_formatting_with_approved_names_and_modifiers() {
        let source = "my  apply f  =  { my  step x  =  f  x;  step  }";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        assert_eq!(skeleton.expressions().len(), 7);
        assert_eq!(skeleton.uses().len(), 3);
        assert_eq!(skeleton.pending().len(), 7);
        assert_eq!(
            skeleton
                .binders()
                .iter()
                .map(Binder::name)
                .collect::<Vec<_>>(),
            ["f", "x", "step", "apply"]
        );
    }

    #[test]
    fn selected_nested_scope_rejects_missing_capture_and_escaped_local_parameter() {
        let mut skeleton = ShadowArtifact::from_parsed(parsed(NESTED))
            .unwrap()
            .into_skeleton()
            .unwrap();
        let local = skeleton.expressions.iter().position(|expression| {
            matches!(&expression.form, Form::Lambda { captures, .. } if !captures.is_empty())
        }).unwrap();
        let Form::Lambda {
            captures,
            parameter,
            ..
        } = &mut skeleton.expressions[local].form
        else {
            panic!("local lambda")
        };
        let x = parameter.clone();
        let saved = std::mem::take(captures);
        assert_eq!(
            skeleton.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
        let Form::Lambda { captures, .. } = &mut skeleton.expressions[local].form else {
            panic!("local lambda")
        };
        *captures = saved;
        skeleton.validate().unwrap();
        let returned = skeleton.uses.last().unwrap().0.index;
        let Form::Use { binder, .. } = &mut skeleton.expressions[returned].form else {
            panic!("returned step")
        };
        *binder = x;
        assert_eq!(
            skeleton.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
    }

    #[test]
    fn selected_nested_recognizer_rejects_adjacent_brace_forms() {
        for source in [
            "my wrapper callback = { my local input = callback input; local }",
            "my wrapper f = { my step x = f x; step }",
            "my apply callback = { my step x = callback x; step }",
            "my apply f = { my local x = f x; local }",
            "my apply f = { my step input = f input; step }",
            "our apply f = { my step x = f x; step }",
            "pub apply f = { my step x = f x; step }",
            "my apply f = { our step x = f x; step }",
            "my apply f = { pub step x = f x; step }",
            "my apply f = {}",
            "my apply f = { f }",
            "my apply f = { my step x = f x; step x }",
            "my apply f = { my step x = f x; x }",
            "my apply f = { my step x = step x; step }",
            "my apply f = { my step x = f(x); step }",
            "my apply f g = { my step x = f x; step }",
            "my apply f = { my step x y = f x; step }",
            "my apply f = { my step x = f x; my other y = f y; step }",
        ] {
            let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
            assert!(
                matches!(artifact.skeleton(), Err(ShadowError::UnsupportedExpression {
                kind: SyntaxKind::BracedStatementBlockExpression, range,
            }) if *range == (source.find('{').unwrap()..source.len())),
                "{source}"
            );
            assert_eq!(artifact.source(), source);
        }
    }

    #[test]
    fn occurrence_index_rejects_ambiguous_zero_width_cst_handles() {
        let parsed = parsed("my f x = x");
        let root = SyntaxNode::new_root(parsed.green().clone());
        let leaf = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IdentifierExpression)
            .unwrap();
        let green = leaf.green().into_owned();
        let empty = green.splice_children(0..green.children().count(), []);
        let root_green = root.green().into_owned();
        let synthetic = SyntaxNode::new_root(root_green.splice_children(
            0..root_green.children().count(),
            [empty.clone().into(), empty.into()],
        ));
        let mut artifact = ShadowArtifact::from_parsed(parsed).unwrap();
        let positions = artifact.retain(synthetic.clone());
        let leaves = synthetic.children().collect::<Vec<_>>();
        assert_eq!(leaves.len(), 2);
        assert_eq!(leaves[0], leaves[1]); // Rowan's shared green handle and offset.
        assert!(positions.get(&leaves[0]).unwrap().is_none());
    }

    #[test]
    fn expression_positions_resolve_exact_source_nodes_and_call_tails() {
        let source = "my call f x = f (x) 7(x)";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let mut kinds = Vec::new();
        let root = SyntaxNode::new_root(artifact.parsed().green().clone());
        let retained = artifact.positions();
        let tails = root
            .descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::MlArgument | SyntaxKind::CallTail))
            .map(|node| {
                let matches = retained
                    .iter()
                    .enumerate()
                    .filter(|(_, position)| {
                        position.is_node()
                            && position.kind() == node.kind()
                            && *position.range() == range_of(&node)
                    })
                    .map(|(index, _)| artifact.position_id(index))
                    .collect::<Vec<_>>();
                assert_eq!(matches.len(), 1);
                matches.into_iter().next().unwrap()
            })
            .collect::<Vec<_>>();
        let mut calls = Vec::new();
        for expression in skeleton.expressions() {
            let position = artifact.position(expression.position()).unwrap();
            assert!(position.is_node());
            kinds.push(position.kind());
            match expression.form() {
                Form::Apply { source_form, .. } => {
                    assert_eq!(position.kind(), *source_form);
                    calls.push(expression.position().clone());
                }
                Form::Use { occurrence, .. } => {
                    assert_eq!(
                        skeleton.use_position(occurrence).unwrap(),
                        expression.position()
                    );
                }
                _ => assert_eq!(position.range(), expression.range()),
            }
        }
        assert!(kinds.contains(&SyntaxKind::IntegerLiteral));
        assert!(kinds.contains(&SyntaxKind::ParenthesizedExpression));
        assert_eq!(calls.len(), tails.len());
        for tail in tails {
            assert_eq!(
                calls.iter().filter(|position| **position == tail).count(),
                1
            );
        }
    }

    #[test]
    fn expression_position_validation_rejects_foreign_missing_and_wrong_nodes() {
        let mut first = ShadowArtifact::from_parsed(parsed("my call f x = f x")).unwrap();
        let second = ShadowArtifact::from_parsed(parsed("my call f x = f x")).unwrap();
        let foreign = second.skeleton().unwrap().expressions()[0]
            .position()
            .clone();
        let missing = first.position_id(first.positions.len());
        let wrong = first.root();
        let skeleton = first.skeleton.as_mut().unwrap();
        let original = skeleton.expressions[0].position.clone();
        skeleton.expressions[0].position = foreign;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::ForeignArtifact)
        );
        skeleton.expressions[0].position = missing;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::MissingReference {
                index: first.positions.len()
            })
        );
        skeleton.expressions[0].position = wrong;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::InvalidUseReference)
        );
        skeleton.expressions[0].position = original;
        skeleton.validate_positions(&first.positions).unwrap();
    }

    #[test]
    fn raw_preflight_accepts_exact_depth_and_rejects_one_more() {
        // Synthetic CST tests the adapter's structural boundary independently
        // of grammar nesting and parser resource limits. Root depth is zero.
        let mut green = parsed(";").green().clone();
        for _ in 0..MAX_SYNTAX_DEPTH - 1 {
            let length = green.children().count();
            green = green.splice_children(0..length, [green.clone().into()]);
        }
        assert_eq!(preflight(&SyntaxNode::new_root(green.clone())), Ok(()));
        let length = green.children().count();
        green = green.splice_children(0..length, [green.clone().into()]);
        assert_eq!(
            preflight(&SyntaxNode::new_root(green)),
            Err(ShadowError::SyntaxDepthLimit)
        );
    }

    #[test]
    fn raw_preflight_accepts_exact_element_count_and_rejects_one_more() {
        let green = parsed(";").green().clone();
        let token = green.children().next().unwrap().to_owned();
        let length = green.children().count();
        let boundary = green.splice_children(
            0..length,
            std::iter::repeat_n(token.clone(), MAX_RAW_ELEMENTS - 1),
        );
        assert_eq!(preflight(&SyntaxNode::new_root(boundary)), Ok(()));
        let rejected =
            green.splice_children(0..length, std::iter::repeat_n(token, MAX_RAW_ELEMENTS));
        assert_eq!(
            preflight(&SyntaxNode::new_root(rejected)),
            Err(ShadowError::ElementLimit)
        );
    }

    #[test]
    fn parsed_flat_chain_preserves_every_ordinary_application() {
        // The public boundary starts after a successful parse. Large flat
        // source chains hit the upstream parser's recursive tail path, so this
        // integration case stays within its ordinary successful envelope.
        let source = format!("my chain f x = f{}", " x".repeat(8));
        let artifact = ShadowArtifact::from_parsed(parsed(&source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        assert_eq!(skeleton.expressions().len(), 17);
        assert_eq!(skeleton.pending().len(), 42);
        assert_eq!(skeleton.uses().len(), 9);
        drop(artifact);
    }

    #[test]
    fn long_flat_chain_builds_and_drops_without_recursive_expressions() {
        // Construct a shallow, lossless chain from parser-produced CST pieces.
        // This tests the owning projection's 4,000-tail worklist independently
        // of the source parser's separate recursive continuation stack limit.
        let parsed = parsed("my chain f x = f x");
        let raw_root = SyntaxNode::new_root(parsed.green().clone());
        let chain = raw_root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::BindingBody)
            .unwrap()
            .children()
            .find(|n| n.kind() == SyntaxKind::OperatorChain)
            .unwrap();
        assert_eq!(chain.to_string(), "f x");
        let green = chain.green().into_owned();
        let children = green.children().map(|e| e.to_owned()).collect::<Vec<_>>();
        let (callee, tail) = children.split_first().unwrap();
        let mut expanded = vec![callee.clone()];
        for _ in 0..4_000 {
            expanded.extend(tail.iter().cloned());
        }
        let synthetic = SyntaxNode::new_root(green.splice_children(0..children.len(), expanded));
        let source = format!("f{}", " x".repeat(4_000));
        assert_eq!(synthetic.to_string(), source);
        assert_eq!(preflight(&synthetic), Ok(()));
        let mut retained = ShadowArtifact::from_parsed(parsed).unwrap();
        let positions = retained.retain(synthetic.clone());
        let mut skeleton = retained.into_skeleton().unwrap();
        skeleton.expressions.clear();
        skeleton.uses.clear();
        skeleton.use_positions.clear();
        skeleton.pending.clear();
        skeleton.body = skeleton.project(synthetic, &source, &positions).unwrap();
        skeleton.validate().unwrap();
        assert_eq!(skeleton.expressions().len(), 8_001);
        assert_eq!(skeleton.pending().len(), 20_000);
        assert_eq!(skeleton.uses().len(), 4_001);
        drop(skeleton);
    }

    #[test]
    fn call_tail_preserves_one_whole_argument_and_pending_premises() {
        let artifact = ShadowArtifact::from_parsed(parsed("my call f x = f(x)")).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let Form::Apply {
            source_form,
            argument,
            ..
        } = skeleton.expression(skeleton.body()).unwrap().form()
        else {
            panic!("ordinary call")
        };
        assert_eq!(*source_form, SyntaxKind::CallTail);
        assert!(matches!(
            skeleton.expression(argument).unwrap().form(),
            Form::Use { .. }
        ));
        assert_eq!(skeleton.pending().len(), 7);
    }

    #[test]
    fn unsupported_expression_keeps_raw_source_without_a_success_fallback() {
        let source = "my constant x = \"unsupported\"";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(matches!(
            artifact.skeleton(),
            Err(ShadowError::UnsupportedExpression {
                kind: SyntaxKind::StringLiteral,
                ..
            })
        ));
        assert_eq!(artifact.source(), source);
    }

    #[test]
    fn private_reference_validation_rejects_missing_foreign_and_cyclic_ids() {
        let mut first = ShadowArtifact::from_parsed(parsed("my compose f g x = f (g x)"))
            .unwrap()
            .into_skeleton()
            .unwrap();
        let second = ShadowArtifact::from_parsed(parsed("my compose f g x = f (g x)"))
            .unwrap()
            .into_skeleton()
            .unwrap();
        assert_eq!(
            first
                .expression(&ExprId(first.id(first.expressions.len())))
                .unwrap_err(),
            ShadowError::MissingReference {
                index: first.expressions.len()
            }
        );
        let index = first.uses[0].0.index;
        let Form::Use { binder, .. } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *binder = BinderId(second.id(0));
        assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
        let local_binder = BinderId(first.id(0));
        let Form::Use { binder, occurrence } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *binder = local_binder;
        *occurrence = UseId(second.id(0));
        assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
        let local_occurrence = UseId(first.id(0));
        let Form::Use { occurrence, .. } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *occurrence = local_occurrence;
        first.validate().unwrap();
        let body = first.body.clone();
        let Form::Apply { argument, .. } = &mut first.expressions[body.0.index].form else {
            panic!("Apply")
        };
        *argument = body;
        assert_eq!(
            first.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
    }

    #[test]
    fn raw_reference_validation_rejects_missing_and_foreign_positions() {
        let first = ShadowArtifact::from_parsed(parsed("x as int")).unwrap();
        let second = ShadowArtifact::from_parsed(parsed("x as int")).unwrap();
        assert_eq!(
            first
                .position(&first.position_id(first.positions.len()))
                .unwrap_err(),
            ShadowError::MissingReference {
                index: first.positions.len()
            }
        );
        assert_eq!(
            first.position(&second.root()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }

    #[test]
    fn failed_narrow_build_keeps_the_complete_raw_snapshot() {
        let source = "my compose f g x = f (g missing)";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(
            matches!(artifact.skeleton(), Err(ShadowError::UnboundName { range }) if *range == (24..31))
        );
        assert_eq!(artifact.source(), source);
        assert_eq!(
            *artifact.position(&artifact.root()).unwrap().range(),
            0..source.len()
        );
    }
}
