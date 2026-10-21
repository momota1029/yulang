//! Source provenance owned by the immutable HIR artifact.
use std::{collections::HashMap, ops::Range};
use yu_syntax::{ParsedFile, SourceNodeKey, SyntaxNode};
use crate::{DefinitionRootId, ExpressionRootId, HirOccurrenceId, HirParameterId};

#[derive(Clone, Debug)]
pub enum HirParameterSourceOrigin {
    IdentifierPattern(SourceNodeKey),
    InlineLambda { lambda: SourceNodeKey, binder_range: Range<usize> },
}

#[derive(Clone, Debug)]
pub(crate) struct HirSourceIdentity {
    pub(crate) parse_root: SourceNodeKey,
    pub(crate) definitions: HashMap<DefinitionRootId, SourceNodeKey>,
    pub(crate) expressions: HashMap<ExpressionRootId, SourceNodeKey>,
    pub(crate) occurrences: HashMap<HirOccurrenceId, SourceNodeKey>,
    pub(crate) parameters: HashMap<HirParameterId, HirParameterSourceOrigin>,
    pub(crate) locals: HashMap<crate::HirLocalId, SourceNodeKey>,
    #[cfg(any(feature = "shadow", test))]
    pub(crate) local_binding: Option<crate::shadow::ShadowLocalBind>,
    pub(crate) local_parameter_owners: HashMap<HirParameterId, crate::HirLocalId>,
}

#[cfg(any(feature = "shadow", test))]
pub(crate) fn source_keys(parsed: &ParsedFile) -> HashMap<SyntaxNode, SourceNodeKey> {
    let mut keys = HashMap::new();
    let mut stack = vec![parsed.source_root()];
    while let Some(node) = stack.pop() {
        keys.insert(node.syntax().clone(), node.key());
        stack.extend(node.children());
    }
    keys
}

pub(crate) fn try_source_keys(parsed: &ParsedFile) -> Result<HashMap<SyntaxNode, SourceNodeKey>, crate::HirAvailabilityError> {
    let mut keys = HashMap::new();
    let mut stack = Vec::new();
    stack.try_reserve(1).map_err(|_| crate::HirAvailabilityError::IdentityExhausted)?;
    stack.push(parsed.source_root());
    while let Some(node) = stack.pop() {
        keys.try_reserve(1).map_err(|_| crate::HirAvailabilityError::IdentityExhausted)?;
        keys.insert(node.syntax().clone(), node.key());
        for child in node.children() {
            stack.try_reserve(1).map_err(|_| crate::HirAvailabilityError::IdentityExhausted)?;
            stack.push(child);
        }
    }
    Ok(keys)
}

/// Retains a node's exact child-index path from the owning immutable parse
/// root. The path is only a reconstruction locator; SourceNodeKey remains the
/// identity and caller-visible owner.
pub(crate) fn source_path(
    root: &SyntaxNode,
    node: &SyntaxNode,
) -> Result<Box<[u32]>, crate::HirAvailabilityError> {
    let mut path = Vec::new();
    let mut current = node.clone();
    while current != *root {
        let parent = current.parent().ok_or(crate::HirAvailabilityError::StructuralProjection)?;
        let ordinal = parent.children().position(|child| child == current)
            .ok_or(crate::HirAvailabilityError::StructuralProjection)?;
        path.try_reserve(1).map_err(|_| crate::HirAvailabilityError::IdentityExhausted)?;
        path.push(u32::try_from(ordinal).map_err(|_| crate::HirAvailabilityError::IdentityExhausted)?);
        current = parent;
    }
    path.reverse();
    Ok(path.into_boxed_slice())
}

pub(crate) fn syntax_node_at_path(
    parsed: &ParsedFile,
    path: &[u32],
) -> Result<SyntaxNode, crate::HirAvailabilityError> {
    let mut node = SyntaxNode::new_root(parsed.green().clone());
    for &ordinal in path {
        node = node.children().nth(ordinal as usize)
            .ok_or(crate::HirAvailabilityError::StructuralProjection)?;
    }
    Ok(node)
}

impl HirSourceIdentity {
    pub(crate) fn new(parsed: &ParsedFile) -> Self {
        Self {
            parse_root: parsed.source_root().key(),
            definitions: HashMap::new(),
            expressions: HashMap::new(),
            occurrences: HashMap::new(),
            parameters: HashMap::new(),
            locals: HashMap::new(),
            #[cfg(any(feature = "shadow", test))]
            local_binding: None,
            local_parameter_owners: HashMap::new(),
        }
    }
    pub(crate) fn empty_stage(&self) -> Self {
        Self {
            parse_root: self.parse_root.clone(),
            definitions: HashMap::new(), expressions: HashMap::new(), occurrences: HashMap::new(),
            parameters: HashMap::new(), locals: HashMap::new(),
            #[cfg(any(feature = "shadow", test))]
            local_binding: None,
            local_parameter_owners: HashMap::new(),
        }
    }
    pub(crate) fn append_stage(&mut self, stage: Self) -> Result<(), crate::HirAvailabilityError> {
        use crate::HirAvailabilityError;
        if self.parse_root != stage.parse_root
            || stage.occurrences.keys().any(|id| self.occurrences.contains_key(id))
            || stage.parameters.keys().any(|id| self.parameters.contains_key(id))
            || stage.locals.keys().any(|id| self.locals.contains_key(id))
            || stage.local_parameter_owners.keys().any(|id| self.local_parameter_owners.contains_key(id))
            || !stage.definitions.is_empty() || !stage.expressions.is_empty()
        {
            return Err(HirAvailabilityError::StructuralProjection);
        }
        // Every fallible reservation precedes publication of the root's delta.
        self.occurrences.try_reserve(stage.occurrences.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        self.parameters.try_reserve(stage.parameters.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        self.locals.try_reserve(stage.locals.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        self.local_parameter_owners.try_reserve(stage.local_parameter_owners.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        self.occurrences.extend(stage.occurrences);
        self.parameters.extend(stage.parameters);
        self.locals.extend(stage.locals);
        self.local_parameter_owners.extend(stage.local_parameter_owners);
        Ok(())
    }
    pub(crate) fn record_local(&mut self, id: crate::HirLocalId, key: SourceNodeKey) {
        self.locals.insert(id, key);
    }
    #[cfg(any(feature = "shadow", test))]
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
        self.parameters.insert(id, HirParameterSourceOrigin::IdentifierPattern(key));
    }
    pub(crate) fn record_inline_parameter(&mut self, id: HirParameterId, lambda: SourceNodeKey, binder_range: Range<usize>) {
        self.parameters.insert(id, HirParameterSourceOrigin::InlineLambda { lambda, binder_range });
    }
    pub(crate) fn record_occurrence(&mut self, id: HirOccurrenceId, key: SourceNodeKey) {
        self.occurrences.insert(id, key);
    }
}
