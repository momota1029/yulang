//! Opt-in, conditional finite Path/Inc query for supplied typed evidence (§6 of
//! the typed-boundary draft). This owns no source judgment or acceptance rule.
//! Profiles, typed correspondences, observations, receipts and actual activation
//! identities remain independent caller assumptions under one original context.
//! Removing this module has no production effect; there are no production users.

use crate::shadow_directional_protection::AssumedOriginalContext;

/// Immutable, validated finite relation. Node indices name exact typed ports;
/// equal witness values never join distinct views, contexts or activations.
/// Caller-owned witness tokens occupy stable, nonoverlapping, nonzero-sized
/// storage for this borrow. Their addresses are the assumed identities, not
/// addresses of runtime values or newly created evidence wrappers.
pub struct AssumedTypedEvidence<'a, W> {
    context: &'a AssumedOriginalContext<'a, W>,
    nodes: &'a [AssumedTypedPort<'a, W>],
    profiles: &'a [AssumedProfile<'a, W>],
    observations: &'a [AssumedObserve<'a, W>],
    receipts: &'a [AssumedReceive<'a, W>],
    outgoing: Vec<Vec<usize>>,
}

impl<'a, W> AssumedTypedEvidence<'a, W> {
    /// Validates wiring only, never source licensing or typed correspondence.
    /// Each (view, position) identity has one node, avoiding ambiguous aliases.
    pub fn new(
        context: &'a AssumedOriginalContext<'a, W>,
        nodes: &'a [AssumedTypedPort<'a, W>],
        profiles: &'a [AssumedProfile<'a, W>],
        flows: &[AssumedFlow<'a, W>],
        observations: &'a [AssumedObserve<'a, W>],
        receipts: &'a [AssumedReceive<'a, W>],
    ) -> Result<Self, EvidenceError> {
        if std::mem::size_of::<W>() == 0 {
            return Err(EvidenceError::ZeroSizedWitness);
        }
        for (index, node) in nodes.iter().enumerate() {
            if !std::ptr::eq(node.context, context) {
                return Err(EvidenceError::MixedContext);
            }
            if nodes[..index].iter().any(|prior| {
                std::ptr::eq(prior.view, node.view) && std::ptr::eq(prior.position, node.position)
            }) {
                return Err(EvidenceError::DuplicatePort);
            }
        }
        let valid = |node: usize| node < nodes.len();
        for profile in profiles {
            if !std::ptr::eq(profile.boundary.context, context) {
                return Err(EvidenceError::MixedContext);
            }
            if !valid(profile.port) {
                return Err(EvidenceError::InvalidNode);
            }
        }
        if flows
            .iter()
            .any(|record| !std::ptr::eq(record.context, context))
            || observations
                .iter()
                .any(|record| !std::ptr::eq(record.event.context, context))
            || receipts
                .iter()
                .any(|record| !std::ptr::eq(record.context, context))
        {
            return Err(EvidenceError::MixedContext);
        }
        if observations.iter().any(|record| !valid(record.port))
            || receipts.iter().any(|record| !valid(record.port))
            || flows
                .iter()
                .any(|edge| !valid(edge.from) || !valid(edge.to))
        {
            return Err(EvidenceError::InvalidNode);
        }
        let mut outgoing = vec![Vec::new(); nodes.len()];
        for edge in flows {
            outgoing[edge.from].push(edge.to);
        }
        Ok(Self {
            context,
            nodes,
            profiles,
            observations,
            receipts,
            outgoing,
        })
    }

    /// Computes raw least reachability and its exact current activation filter.
    /// Does not select a handler, grant release, infer protection, or mutate input.
    pub fn query_conditionally(
        &self,
        profile_index: usize,
        event: &AssumedEvent<'a, W>,
        candidate: &AssumedHandler<'a, W>,
        current: &AssumedConfiguration<'a, W>,
    ) -> Result<ConditionalIncidence, EvidenceError> {
        let profile = self
            .profiles
            .get(profile_index)
            .ok_or(EvidenceError::InvalidProfile)?;
        if !std::ptr::eq(event.context, self.context)
            || !std::ptr::eq(candidate.context, self.context)
            || !std::ptr::eq(current.context, self.context)
        {
            return Err(EvidenceError::MixedContext);
        }
        let mut endpoints = vec![false; self.nodes.len()];
        for observation in self.observations {
            if std::ptr::eq(observation.event.witness, event.witness)
                && self.receipts.iter().any(|receipt| {
                    receipt.port == observation.port && std::ptr::eq(receipt.owner, candidate.owner)
                })
            {
                endpoints[observation.port] = true;
            }
        }
        let mut visited = vec![false; self.nodes.len()];
        let mut queue = Vec::with_capacity(self.nodes.len());
        visited[profile.port] = true;
        queue.push(profile.port);
        let mut cursor = 0;
        let mut path = false;
        while cursor < queue.len() {
            let node = queue[cursor];
            cursor += 1;
            if endpoints[node] {
                path = true;
                break;
            }
            for &next in &self.outgoing[node] {
                if !visited[next] {
                    visited[next] = true;
                    queue.push(next);
                }
            }
        }
        let active = |witness, roots: &[&W]| roots.iter().any(|root| std::ptr::eq(*root, witness));
        Ok(ConditionalIncidence {
            status: ConditionalStatus::Assumed,
            path,
            inc_c: path
                && active(candidate.witness, current.active_handlers)
                && active(candidate.owner, current.active_owners)
                && active(profile.boundary.original_receiver, current.active_owners),
        })
    }
}

/// Assumed effect-observation position of an exact evidence-bearing view.
/// The view witness denotes (value, signature, evidence root), not value alone.
pub struct AssumedTypedPort<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub view: &'a W,
    pub position: &'a W,
}

/// Actual original boundary occurrence, independent of source position/type.
pub struct AssumedBoundary<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub witness: &'a W,
    pub original_receiver: &'a W,
}

/// Caller-supplied protected profile position; no capture contract is implied.
pub struct AssumedProfile<'a, W> {
    /// Original p/beta/provenance packet identity, retained without merging.
    pub witness: &'a W,
    pub boundary: &'a AssumedBoundary<'a, W>,
    pub port: usize,
}

/// One supplied typed correspondence between exact effect ports.
pub struct AssumedFlow<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub from: usize,
    pub to: usize,
}

/// Historical event exposure at this exact executing view/position.
pub struct AssumedObserve<'a, W> {
    pub event: &'a AssumedEvent<'a, W>,
    pub port: usize,
}

/// Receipt expanded along independently supplied corresponding-path evidence
/// to this target view/effect port; not the raw Receive syntax itself.
/// This records ownership of use and creates no boundary or contract.
pub struct AssumedReceive<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub owner: &'a W,
    pub port: usize,
}

/// Actual event identity under the original context, independent of family/value.
pub struct AssumedEvent<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub witness: &'a W,
}

pub struct AssumedHandler<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub witness: &'a W,
    pub owner: &'a W,
}

/// Actual currently active roots, not every record reachable from a continuation.
pub struct AssumedConfiguration<'a, W> {
    pub context: &'a AssumedOriginalContext<'a, W>,
    pub active_handlers: &'a [&'a W],
    pub active_owners: &'a [&'a W],
}

/// Conditional facts about supplied evidence, never source acceptance or a grant.
#[derive(Debug, PartialEq, Eq)]
pub struct ConditionalIncidence {
    pub status: ConditionalStatus,
    pub path: bool,
    pub inc_c: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConditionalStatus {
    Assumed,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EvidenceError {
    ZeroSizedWitness,
    InvalidNode,
    InvalidProfile,
    MixedContext,
    DuplicatePort,
}
