//! Sealed, iterative SCC planning for one fully collected constraint batch.

use std::{
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher},
    sync::Arc,
};

use super::{
    CollectedDefinition, CollectionArtifactToken, CollectionAvailabilityError,
    CollectionLookupError, DefinitionOrderId, DefinitionUse, DefinitionUseId, ProductionCounters,
};

/// Artifact-branded canonical identity for one static SCC.
///
/// The canonical definition is the minimum `DefinitionOrderId` member. It is
/// therefore independent of spelling, path text, and map insertion order.
#[derive(Clone)]
pub(crate) struct SccComponentId {
    canonical_definition: DefinitionOrderId,
}

impl SccComponentId {
    pub(super) fn new(canonical_definition: DefinitionOrderId) -> Self {
        Self {
            canonical_definition,
        }
    }

    pub(super) fn canonical_definition(&self) -> &DefinitionOrderId {
        &self.canonical_definition
    }
}

/// The F1 kernel only needs a stable definition identity.  Keeping this as a
/// borrowed input contract lets F2 build directly from F0's retained records
/// instead of materializing a second `Vec<DefinitionOrderId>`.
pub(super) trait SccDefinition {
    fn identity(&self) -> &DefinitionOrderId;
}

impl SccDefinition for CollectedDefinition {
    fn identity(&self) -> &DefinitionOrderId {
        self.definition()
    }
}

#[cfg(test)]
impl SccDefinition for DefinitionOrderId {
    fn identity(&self) -> &DefinitionOrderId {
        self
    }
}

impl std::fmt::Debug for SccComponentId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SccComponentId")
            .field("canonical_definition", &self.canonical_definition.ordinal())
            .finish()
    }
}

impl PartialEq for SccComponentId {
    fn eq(&self, other: &Self) -> bool {
        self.canonical_definition == other.canonical_definition
    }
}
impl Eq for SccComponentId {}
impl Hash for SccComponentId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical_definition.hash(state);
    }
}

#[derive(Clone, Debug)]
struct SccComponent {
    id: SccComponentId,
    members: Vec<DefinitionOrderId>,
    internal_uses: Vec<DefinitionUseId>,
    incoming_uses: Vec<DefinitionUseId>,
}

/// Immutable output of the standalone F1 static graph kernel.
#[derive(Debug)]
pub(crate) struct SccPlan {
    artifact: Arc<CollectionArtifactToken>,
    components_in_dependency_first_order: Vec<SccComponent>,
    component_positions: HashMap<SccComponentId, usize>,
    component_of_definition: HashMap<DefinitionOrderId, SccComponentId>,
}

/// Cloning duplicates immutable plan indexes and ID handles while preserving
/// the collection artifact brand through its shared `Arc` token. It does not
/// change F1 construction counters, which report only `SccPlan::build` work.
impl Clone for SccPlan {
    fn clone(&self) -> Self {
        Self {
            artifact: self.artifact.clone(),
            components_in_dependency_first_order: self.components_in_dependency_first_order.clone(),
            component_positions: self.component_positions.clone(),
            component_of_definition: self.component_of_definition.clone(),
        }
    }
}

#[derive(Debug)]
struct GraphArc {
    target: usize,
    payloads: Vec<DefinitionUseId>,
}

/// O(1) phase-exact logical-byte state for the graph-to-component transfer.
/// Each aggregate changes only when ownership or a container capacity changes;
/// no source-sized container is rescanned from an element/arc/component loop.
struct PartitionWorkspace {
    input_bytes: usize,
    graph_fixed_bytes: usize,
    forward_arc_bytes: usize,
    component_for_node_bytes: usize,
    discovered_outer_bytes: usize,
    discovered_member_bytes: usize,
    components_outer_bytes: usize,
    component_member_bytes: usize,
    predecessor_bytes: usize,
    open_dependency_bytes: usize,
    condensation_edge_bytes: usize,
}

impl PartitionWorkspace {
    fn bytes(&self, current_member_bytes: usize, local_arc_bytes: usize) -> usize {
        self.input_bytes
            + self.graph_fixed_bytes
            + self.forward_arc_bytes
            + self.component_for_node_bytes
            + self.discovered_outer_bytes
            + self.discovered_member_bytes
            + self.components_outer_bytes
            + self.component_member_bytes
            + self.predecessor_bytes
            + self.open_dependency_bytes
            + self.condensation_edge_bytes
            + current_member_bytes
            + local_arc_bytes
    }
}

#[derive(Clone, Copy)]
struct DfsFrame {
    node: usize,
    next_edge: usize,
}

/// A deterministic min queue with comparisons explicitly accounted for.
#[derive(Default)]
struct ReadyQueue {
    entries: Vec<(u32, usize)>,
}

impl ReadyQueue {
    fn push(&mut self, entry: (u32, usize), counters: &mut ProductionCounters) {
        counters.scc_ready_queue_operations += 1;
        self.entries.push(entry);
        let mut index = self.entries.len() - 1;
        while index > 0 {
            let parent = (index - 1) / 2;
            counters.scc_ready_queue_comparisons += 1;
            if self.entries[parent] <= self.entries[index] {
                break;
            }
            self.entries.swap(parent, index);
            index = parent;
        }
        counters.scc_ready_queue_maximum_size = counters
            .scc_ready_queue_maximum_size
            .max(self.entries.len());
    }

    fn pop_min(&mut self, counters: &mut ProductionCounters) -> Option<(u32, usize)> {
        let minimum = self.entries.first().copied()?;
        counters.scc_ready_queue_operations += 1;
        let last = self.entries.pop().expect("first implies one entry");
        if !self.entries.is_empty() {
            self.entries[0] = last;
            let mut index = 0;
            loop {
                let left = index * 2 + 1;
                if left >= self.entries.len() {
                    break;
                }
                let right = left + 1;
                let mut child = left;
                if right < self.entries.len() {
                    counters.scc_ready_queue_comparisons += 1;
                    if self.entries[right] < self.entries[left] {
                        child = right;
                    }
                }
                counters.scc_ready_queue_comparisons += 1;
                if self.entries[index] <= self.entries[child] {
                    break;
                }
                self.entries.swap(index, child);
                index = child;
            }
        }
        Some(minimum)
    }
}

impl SccPlan {
    pub(super) fn build<T: SccDefinition>(
        artifact: &Arc<CollectionArtifactToken>,
        definitions: &[T],
        uses: &[DefinitionUse],
        counters: &mut ProductionCounters,
    ) -> Result<Self, CollectionAvailabilityError> {
        u32::try_from(definitions.len())
            .map_err(|_| CollectionAvailabilityError::GraphIdentityExhausted)?;
        let mut node_for_definition = HashMap::with_capacity(definitions.len());
        for (node, definition) in definitions.iter().enumerate() {
            let definition = definition.identity();
            if !Arc::ptr_eq(artifact, &definition.artifact) {
                return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
            }
            counters.scc_definition_index_probes += 1;
            let capacity = node_for_definition.capacity();
            if node_for_definition
                .insert(definition.clone(), node)
                .is_some()
            {
                return Err(CollectionAvailabilityError::DuplicateDefinitionOrderId);
            }
            if node_for_definition.capacity() != capacity {
                counters.scc_map_set_rebuilds += 1;
            }
        }
        if node_for_definition.len() != definitions.len() {
            return Err(CollectionAvailabilityError::NonTotalDefinitionMap);
        }
        counters.scc_definition_index_capacity = node_for_definition.capacity();

        let mut seen_uses = HashSet::with_capacity(uses.len());
        let mut ordered_uses = uses.iter().collect::<Vec<_>>();
        for use_record in &ordered_uses {
            if !Arc::ptr_eq(artifact, &use_record.id.artifact)
                || !Arc::ptr_eq(artifact, &use_record.parent.artifact)
                || !Arc::ptr_eq(artifact, &use_record.target.artifact)
            {
                return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
            }
            counters.scc_seen_use_set_probes += 1;
            let capacity = seen_uses.capacity();
            if !seen_uses.insert(use_record.id.clone()) {
                return Err(CollectionAvailabilityError::DuplicateDefinitionUseId);
            }
            if seen_uses.capacity() != capacity {
                counters.scc_map_set_rebuilds += 1;
            }
        }
        counters.scc_seen_use_set_capacity = seen_uses.capacity();
        sort_by_count(&mut ordered_uses, counters, |left, right| {
            use_key(left).cmp(&use_key(right))
        });

        let mut forward = (0..definitions.len())
            .map(|_| Vec::<GraphArc>::new())
            .collect::<Vec<_>>();
        let mut reverse = (0..definitions.len())
            .map(|_| Vec::<usize>::new())
            .collect::<Vec<_>>();
        let mut cursor = 0;
        while cursor < ordered_uses.len() {
            let first = ordered_uses[cursor];
            counters.scc_definition_index_probes += 1;
            let parent = *node_for_definition
                .get(&first.parent)
                .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
            counters.scc_definition_index_probes += 1;
            let target = *node_for_definition
                .get(&first.target)
                .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
            let start = cursor;
            cursor += 1;
            while cursor < ordered_uses.len()
                && ordered_uses[cursor].parent == first.parent
                && ordered_uses[cursor].target == first.target
            {
                cursor += 1;
            }
            let payloads = ordered_uses[start..cursor]
                .iter()
                .map(|use_record| use_record.id.clone())
                .collect::<Vec<_>>();
            counters.scc_distinct_arcs += 1;
            counters.scc_retained_occurrence_payloads += payloads.len();
            counters.scc_forward_adjacency_entries += 1;
            counters.scc_forward_payload_lengths += payloads.len();
            counters.scc_reverse_adjacency_entries += 1;
            forward[parent].push(GraphArc { target, payloads });
            reverse[target].push(parent);
        }
        counters.scc_forward_adjacency_capacity =
            forward.capacity() + forward.iter().map(Vec::capacity).sum::<usize>();
        counters.scc_reverse_adjacency_capacity =
            reverse.capacity() + reverse.iter().map(Vec::capacity).sum::<usize>();
        counters.scc_forward_payload_capacity = forward
            .iter()
            .flat_map(|arcs| arcs.iter())
            .map(|arc| arc.payloads.capacity())
            .sum();

        let graph_build_bytes =
            f1_input_retained_bytes(definitions, uses).saturating_add(graph_phase_bytes(
                &ordered_uses,
                &forward,
                &reverse,
                &seen_uses,
                &node_for_definition,
            ));
        let components_by_discovery = strongly_connected_components(
            &forward,
            &reverse,
            definitions,
            graph_build_bytes,
            counters,
        );
        let mut component_for_node = vec![usize::MAX; definitions.len()];
        let mut components = Vec::with_capacity(components_by_discovery.len());
        let mut components_by_discovery = components_by_discovery;
        let forward_arc_bytes = forward.iter().map(graph_arc_storage_bytes).sum::<usize>();
        let mut partition_workspace = PartitionWorkspace {
            input_bytes: f1_input_retained_bytes(definitions, uses),
            graph_fixed_bytes: graph_phase_bytes(
                &ordered_uses,
                &forward,
                &reverse,
                &seen_uses,
                &node_for_definition,
            )
            .saturating_sub(forward_arc_bytes),
            forward_arc_bytes,
            component_for_node_bytes: logical_vec_bytes(&component_for_node),
            discovered_outer_bytes: logical_vec_bytes(&components_by_discovery),
            discovered_member_bytes: components_by_discovery.iter().map(logical_vec_bytes).sum(),
            components_outer_bytes: logical_vec_bytes(&components),
            component_member_bytes: 0,
            predecessor_bytes: 0,
            open_dependency_bytes: 0,
            condensation_edge_bytes: 0,
        };
        let mut partition_peak_bytes = partition_workspace.bytes(0, 0);
        while let Some(mut members) = components_by_discovery.pop() {
            let members_bytes = logical_vec_bytes(&members);
            partition_workspace.discovered_member_bytes -= members_bytes;
            let component_index = components.len();
            sort_by_count(&mut members, counters, |left, right| {
                definitions[*left]
                    .identity()
                    .ordinal()
                    .cmp(&definitions[*right].identity().ordinal())
            });
            let canonical = members
                .first()
                .copied()
                .ok_or(CollectionAvailabilityError::NonTotalSccMembershipMap)?;
            for &node in &members {
                if component_for_node[node] != usize::MAX {
                    return Err(CollectionAvailabilityError::NonTotalSccMembershipMap);
                }
                component_for_node[node] = component_index;
            }
            counters.scc_component_writes += members.len();
            counters.scc_maximum_component_size =
                counters.scc_maximum_component_size.max(members.len());
            let mut component_members = Vec::with_capacity(members.len());
            // Source DFS members and the preallocated destination members are
            // co-resident while handles move; sampling is O(1).
            partition_peak_bytes = partition_peak_bytes.max(
                partition_workspace.bytes(members_bytes + logical_vec_bytes(&component_members), 0),
            );
            for &node in &members {
                component_members.push(definitions[node].identity().clone());
            }
            partition_workspace.component_member_bytes += logical_vec_bytes(&component_members);
            components.push(SccComponent {
                id: SccComponentId::new(definitions[canonical].identity().clone()),
                members: component_members,
                internal_uses: Vec::new(),
                incoming_uses: Vec::new(),
            });
            // `members` remains allocated until this iteration ends, so it is
            // included with its newly retained destination at the move peak.
            partition_peak_bytes =
                partition_peak_bytes.max(partition_workspace.bytes(members_bytes, 0));
        }
        if component_for_node
            .iter()
            .any(|component| *component == usize::MAX)
        {
            return Err(CollectionAvailabilityError::NonTotalSccMembershipMap);
        }
        u32::try_from(components.len())
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        counters.scc_count = components.len();

        let mut condensation_edges = HashSet::new();
        let mut predecessors = (0..components.len())
            .map(|_| Vec::new())
            .collect::<Vec<_>>();
        let mut open_dependencies = vec![0usize; components.len()];
        partition_workspace.predecessor_bytes = predecessor_bytes(&predecessors);
        partition_workspace.open_dependency_bytes = logical_vec_bytes(&open_dependencies);
        partition_workspace.condensation_edge_bytes = logical_set_bytes(&condensation_edges);
        partition_peak_bytes = partition_peak_bytes.max(partition_workspace.bytes(0, 0));
        for parent in 0..forward.len() {
            let mut arcs = std::mem::take(&mut forward[parent]);
            let mut local_arc_bytes = graph_arc_storage_bytes(&arcs);
            partition_workspace.forward_arc_bytes -= local_arc_bytes;
            let parent_component = component_for_node[parent];
            while let Some(arc) = arcs.pop() {
                let target_component = component_for_node[arc.target];
                let payload_bytes = logical_vec_bytes(&arc.payloads);
                if parent_component == target_component {
                    let previous_capacity =
                        logical_vec_bytes(&components[parent_component].internal_uses);
                    components[parent_component]
                        .internal_uses
                        .reserve(arc.payloads.len());
                    partition_workspace.component_member_bytes +=
                        logical_vec_bytes(&components[parent_component].internal_uses)
                            - previous_capacity;
                    partition_peak_bytes =
                        partition_peak_bytes.max(partition_workspace.bytes(0, local_arc_bytes));
                    components[parent_component]
                        .internal_uses
                        .extend(arc.payloads);
                } else {
                    let previous_capacity =
                        logical_vec_bytes(&components[target_component].incoming_uses);
                    components[target_component]
                        .incoming_uses
                        .reserve(arc.payloads.len());
                    partition_workspace.component_member_bytes +=
                        logical_vec_bytes(&components[target_component].incoming_uses)
                            - previous_capacity;
                    partition_peak_bytes =
                        partition_peak_bytes.max(partition_workspace.bytes(0, local_arc_bytes));
                    components[target_component]
                        .incoming_uses
                        .extend(arc.payloads);
                    counters.scc_condensation_set_probes += 1;
                    let capacity = condensation_edges.capacity();
                    if condensation_edges.insert((parent_component, target_component)) {
                        open_dependencies[parent_component] += 1;
                        let previous_capacity = logical_vec_bytes(&predecessors[target_component]);
                        predecessors[target_component].push(parent_component);
                        partition_workspace.predecessor_bytes +=
                            logical_vec_bytes(&predecessors[target_component]) - previous_capacity;
                    }
                    if condensation_edges.capacity() != capacity {
                        counters.scc_map_set_rebuilds += 1;
                        partition_workspace.condensation_edge_bytes =
                            logical_set_bytes(&condensation_edges);
                    }
                    partition_peak_bytes =
                        partition_peak_bytes.max(partition_workspace.bytes(0, local_arc_bytes));
                }
                // `extend` consumes the source payload allocation; the local
                // arc vector still owns only its GraphArc slot array.
                local_arc_bytes -= payload_bytes;
            }
        }
        counters.scc_condensation_set_capacity = condensation_edges.capacity();
        counters.scc_internal_use_count = components
            .iter()
            .map(|component| component.internal_uses.len())
            .sum();
        counters.scc_incoming_use_count = components
            .iter()
            .map(|component| component.incoming_uses.len())
            .sum();
        for component in &mut components {
            sort_by_count(&mut component.internal_uses, counters, use_id_order);
            sort_by_count(&mut component.incoming_uses, counters, use_id_order);
        }
        counters.scc_partition_workspace_peak_bytes =
            partition_peak_bytes.max(partition_workspace.bytes(0, 0));

        // The discovery source has completed its transfer and is no longer
        // co-resident with scheduling or freezing allocations.
        drop(components_by_discovery);
        partition_workspace.discovered_outer_bytes = 0;
        partition_workspace.discovered_member_bytes = 0;
        let scheduler_baseline_bytes = partition_workspace
            .bytes(0, 0)
            .saturating_sub(partition_workspace.predecessor_bytes)
            .saturating_sub(partition_workspace.open_dependency_bytes);
        let scheduler_predecessor_bytes = partition_workspace.predecessor_bytes;
        let dependency_first = schedule_dependency_sinks(
            &components,
            &mut predecessors,
            &mut open_dependencies,
            condensation_edges.len(),
            scheduler_baseline_bytes,
            scheduler_predecessor_bytes,
            counters,
        )?;
        // Scheduling consumes these temporary condensation worklists before
        // the immutable-plan freeze transition begins.
        drop(predecessors);
        drop(open_dependencies);
        let dependency_first_capacity = dependency_first.capacity();
        let mut component_positions = HashMap::with_capacity(components.len());
        let mut component_of_definition = HashMap::with_capacity(definitions.len());
        let mut ordered_components = Vec::with_capacity(components.len());
        let mut components = components.into_iter().map(Some).collect::<Vec<_>>();
        // One bounded phase-boundary scan establishes the source component
        // aggregate. The transfer loop below then maintains it in O(1).
        let freeze_base_bytes = f1_input_retained_bytes(definitions, uses)
            + graph_phase_bytes(
                &ordered_uses,
                &forward,
                &reverse,
                &seen_uses,
                &node_for_definition,
            )
            + logical_vec_bytes(&component_for_node)
            + logical_set_bytes(&condensation_edges)
            + dependency_first_capacity * std::mem::size_of::<usize>();
        let source_component_slots = logical_vec_bytes(&components);
        let mut source_component_bytes = components
            .iter()
            .flatten()
            .map(component_storage_bytes)
            .sum::<usize>();
        let ordered_component_slots = logical_vec_bytes(&ordered_components);
        let mut ordered_component_bytes = 0;
        let freeze_bytes =
            |current_component_bytes: usize,
             source_component_bytes: usize,
             ordered_component_bytes: usize,
             component_positions: &HashMap<SccComponentId, usize>,
             component_of_definition: &HashMap<DefinitionOrderId, SccComponentId>| {
                freeze_base_bytes
                    + source_component_slots
                    + source_component_bytes
                    + ordered_component_slots
                    + ordered_component_bytes
                    + logical_map_bytes(component_positions)
                    + logical_map_bytes(component_of_definition)
                    + current_component_bytes
            };
        let mut freeze_peak_bytes = freeze_bytes(
            0,
            source_component_bytes,
            ordered_component_bytes,
            &component_positions,
            &component_of_definition,
        );
        for component_index in dependency_first {
            let position = ordered_components.len();
            let component = components[component_index]
                .take()
                .ok_or(CollectionAvailabilityError::NonTotalSccComponentMap)?;
            let component_bytes = component_storage_bytes(&component);
            source_component_bytes -= component_bytes;
            counters.scc_plan_component_index_probes += 1;
            let capacity = component_positions.capacity();
            if component_positions
                .insert(component.id.clone(), position)
                .is_some()
            {
                return Err(CollectionAvailabilityError::NonTotalSccComponentMap);
            }
            if component_positions.capacity() != capacity {
                counters.scc_map_set_rebuilds += 1;
            }
            for definition in &component.members {
                counters.scc_plan_definition_index_probes += 1;
                let capacity = component_of_definition.capacity();
                if component_of_definition
                    .insert(definition.clone(), component.id.clone())
                    .is_some()
                {
                    return Err(CollectionAvailabilityError::NonTotalSccMembershipMap);
                }
                if component_of_definition.capacity() != capacity {
                    counters.scc_map_set_rebuilds += 1;
                }
            }
            freeze_peak_bytes = freeze_peak_bytes.max(freeze_bytes(
                component_bytes,
                source_component_bytes,
                ordered_component_bytes,
                &component_positions,
                &component_of_definition,
            ));
            ordered_components.push(component);
            ordered_component_bytes += component_bytes;
            freeze_peak_bytes = freeze_peak_bytes.max(freeze_bytes(
                0,
                source_component_bytes,
                ordered_component_bytes,
                &component_positions,
                &component_of_definition,
            ));
        }
        if component_positions.len() != ordered_components.len()
            || component_of_definition.len() != definitions.len()
        {
            return Err(CollectionAvailabilityError::NonTotalSccComponentMap);
        }

        counters.scc_plan_component_capacity = ordered_components.capacity();
        counters.scc_plan_member_capacity = ordered_components
            .iter()
            .map(|component| component.members.capacity())
            .sum();
        counters.scc_plan_internal_use_capacity = ordered_components
            .iter()
            .map(|component| component.internal_uses.capacity())
            .sum();
        counters.scc_plan_incoming_use_capacity = ordered_components
            .iter()
            .map(|component| component.incoming_uses.capacity())
            .sum();
        counters.scc_plan_component_index_capacity = component_positions.capacity();
        counters.scc_plan_definition_index_capacity = component_of_definition.capacity();
        counters.scc_plan_retained_payload_bytes = retained_plan_bytes(
            &ordered_components,
            &component_positions,
            &component_of_definition,
        );
        counters.scc_freeze_transition_peak_bytes = freeze_peak_bytes;
        // F1 clones stable handles only at the index/member/payload sites:
        // 4D + 2C DefinitionOrderId handles and 2U DefinitionUseId handles.
        // These are handle bytes, never their artifact/HIR referent payloads.
        let definition_id_clones = definitions.len() * 4 + ordered_components.len() * 2;
        let use_id_clones = uses.len() * 2;
        counters.scc_stable_id_clone_count = definition_id_clones + use_id_clones;
        counters.scc_stable_id_clone_payload_bytes = definition_id_clones
            * std::mem::size_of::<DefinitionOrderId>()
            + use_id_clones * std::mem::size_of::<DefinitionUseId>();
        counters.scc_graph_workspace_peak_known_bytes = graph_build_bytes;
        let retained_plan_phase_bytes = retained_plan_bytes(
            &ordered_components,
            &component_positions,
            &component_of_definition,
        );
        counters.scc_f1_graph_input_plan_peak_known_bytes = graph_build_bytes
            .max(counters.scc_kosaraju_workspace_peak_bytes)
            .max(counters.scc_partition_workspace_peak_bytes)
            .max(counters.scc_scheduler_workspace_peak_bytes)
            .max(freeze_peak_bytes)
            .max(retained_plan_phase_bytes);

        Ok(Self {
            artifact: artifact.clone(),
            components_in_dependency_first_order: ordered_components,
            component_positions,
            component_of_definition,
        })
    }

    /// Canonical component identities in condensation dependency-sink-first order.
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn components_in_dependency_first_order(
        &self,
    ) -> impl Iterator<Item = &SccComponentId> {
        self.components_in_dependency_first_order
            .iter()
            .map(|component| &component.id)
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(super) fn component_for_definition(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<&SccComponentId, CollectionLookupError> {
        self.require_owned_definition(definition)?;
        self.component_of_definition
            .get(definition)
            .ok_or(CollectionLookupError::MissingIdentity)
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(super) fn members(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionOrderId], CollectionLookupError> {
        Ok(self.component(component)?.members.as_slice())
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(super) fn internal_uses(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionUseId], CollectionLookupError> {
        Ok(self.component(component)?.internal_uses.as_slice())
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(super) fn incoming_uses(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionUseId], CollectionLookupError> {
        Ok(self.component(component)?.incoming_uses.as_slice())
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    fn component(
        &self,
        component: &SccComponentId,
    ) -> Result<&SccComponent, CollectionLookupError> {
        self.require_owned_component(component)?;
        self.component_positions
            .get(component)
            .and_then(|&position| self.components_in_dependency_first_order.get(position))
            .ok_or(CollectionLookupError::MissingIdentity)
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    fn require_owned_definition(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<(), CollectionLookupError> {
        Arc::ptr_eq(&self.artifact, &definition.artifact)
            .then_some(())
            .ok_or(CollectionLookupError::ArtifactMismatch)
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    fn require_owned_component(
        &self,
        component: &SccComponentId,
    ) -> Result<(), CollectionLookupError> {
        self.require_owned_definition(&component.canonical_definition)
    }

    #[cfg(test)]
    fn component_for_test(&self, id: &SccComponentId) -> Option<&SccComponent> {
        self.component_positions
            .get(id)
            .and_then(|&position| self.components_in_dependency_first_order.get(position))
    }

    #[cfg(test)]
    pub(super) fn members_for_test(&self, id: &SccComponentId) -> Option<&[DefinitionOrderId]> {
        self.component_for_test(id)
            .map(|component| component.members.as_slice())
    }

    #[cfg(test)]
    pub(super) fn internal_uses_for_test(&self, id: &SccComponentId) -> Option<&[DefinitionUseId]> {
        self.component_for_test(id)
            .map(|component| component.internal_uses.as_slice())
    }

    #[cfg(test)]
    pub(super) fn incoming_uses_for_test(&self, id: &SccComponentId) -> Option<&[DefinitionUseId]> {
        self.component_for_test(id)
            .map(|component| component.incoming_uses.as_slice())
    }
}

fn use_key(use_record: &DefinitionUse) -> (u32, u32, u32) {
    (
        use_record.parent.ordinal(),
        use_record.target.ordinal(),
        use_record.id.occurrence.ordinal(),
    )
}

fn use_id_order(left: &DefinitionUseId, right: &DefinitionUseId) -> std::cmp::Ordering {
    left.occurrence.ordinal().cmp(&right.occurrence.ordinal())
}

fn sort_by_count<T, F>(items: &mut [T], counters: &mut ProductionCounters, mut compare: F)
where
    F: FnMut(&T, &T) -> std::cmp::Ordering,
{
    counters.scc_sort_count += 1;
    counters.scc_sort_elements += items.len();
    // Every F1 sort key is total and unique after the duplicate-ID checks, so
    // unstable sorting preserves the canonical raw plan without heap scratch.
    items.sort_unstable_by(|left, right| {
        counters.scc_sort_comparisons += 1;
        compare(left, right)
    });
}

fn strongly_connected_components<T: SccDefinition>(
    forward: &[Vec<GraphArc>],
    reverse: &[Vec<usize>],
    definitions: &[T],
    baseline_bytes: usize,
    counters: &mut ProductionCounters,
) -> Vec<Vec<usize>> {
    let mut visited = vec![false; definitions.len()];
    let mut finish_order = Vec::with_capacity(definitions.len());
    let mut stack = Vec::new();
    let mut assigned = Vec::new();
    let mut reverse_stack = Vec::new();
    let mut components = Vec::new();
    let mut discovered_member_bytes = 0;
    for root in 0..definitions.len() {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        counters.scc_node_visits += 1;
        stack.push(DfsFrame {
            node: root,
            next_edge: 0,
        });
        counters.scc_stack_pushes += 1;
        counters.scc_peak_stack_bytes = counters
            .scc_peak_stack_bytes
            .max(stack.capacity() * std::mem::size_of::<DfsFrame>());
        record_kosaraju_peak(
            counters,
            baseline_bytes,
            &visited,
            &assigned,
            &finish_order,
            &stack,
            &reverse_stack,
            &components,
            discovered_member_bytes,
            0,
        );
        while let Some(frame) = stack.last_mut() {
            if frame.next_edge < forward[frame.node].len() {
                let target = forward[frame.node][frame.next_edge].target;
                frame.next_edge += 1;
                counters.scc_edge_visits += 1;
                if !visited[target] {
                    visited[target] = true;
                    counters.scc_node_visits += 1;
                    stack.push(DfsFrame {
                        node: target,
                        next_edge: 0,
                    });
                    counters.scc_stack_pushes += 1;
                    counters.scc_peak_stack_bytes = counters
                        .scc_peak_stack_bytes
                        .max(stack.capacity() * std::mem::size_of::<DfsFrame>());
                    record_kosaraju_peak(
                        counters,
                        baseline_bytes,
                        &visited,
                        &assigned,
                        &finish_order,
                        &stack,
                        &reverse_stack,
                        &components,
                        discovered_member_bytes,
                        0,
                    );
                }
            } else {
                finish_order.push(frame.node);
                stack.pop();
            }
        }
    }

    assigned = vec![false; definitions.len()];
    record_kosaraju_peak(
        counters,
        baseline_bytes,
        &visited,
        &assigned,
        &finish_order,
        &stack,
        &reverse_stack,
        &components,
        discovered_member_bytes,
        0,
    );
    for &root in finish_order.iter().rev() {
        if assigned[root] {
            continue;
        }
        let mut members = Vec::new();
        reverse_stack.push(root);
        assigned[root] = true;
        counters.scc_node_visits += 1;
        counters.scc_stack_pushes += 1;
        counters.scc_peak_stack_bytes = counters.scc_peak_stack_bytes.max(
            stack.capacity() * std::mem::size_of::<DfsFrame>()
                + reverse_stack.capacity() * std::mem::size_of::<usize>(),
        );
        record_kosaraju_peak(
            counters,
            baseline_bytes,
            &visited,
            &assigned,
            &finish_order,
            &stack,
            &reverse_stack,
            &components,
            discovered_member_bytes,
            logical_capacity_bytes(&members),
        );
        while let Some(node) = reverse_stack.pop() {
            members.push(node);
            for &predecessor in &reverse[node] {
                counters.scc_edge_visits += 1;
                if !assigned[predecessor] {
                    assigned[predecessor] = true;
                    counters.scc_node_visits += 1;
                    reverse_stack.push(predecessor);
                    counters.scc_stack_pushes += 1;
                    counters.scc_peak_stack_bytes = counters.scc_peak_stack_bytes.max(
                        stack.capacity() * std::mem::size_of::<DfsFrame>()
                            + reverse_stack.capacity() * std::mem::size_of::<usize>(),
                    );
                    record_kosaraju_peak(
                        counters,
                        baseline_bytes,
                        &visited,
                        &assigned,
                        &finish_order,
                        &stack,
                        &reverse_stack,
                        &components,
                        discovered_member_bytes,
                        logical_capacity_bytes(&members),
                    );
                }
            }
        }
        // Kosaraju has no lowlink table. The production counter remains zero
        // so callers can distinguish this selected iterative algorithm from
        // an iterative Tarjan implementation.
        discovered_member_bytes += logical_capacity_bytes(&members);
        components.push(members);
        record_kosaraju_peak(
            counters,
            baseline_bytes,
            &visited,
            &assigned,
            &finish_order,
            &stack,
            &reverse_stack,
            &components,
            discovered_member_bytes,
            0,
        );
    }
    counters.scc_peak_temporary_set_bytes = visited.capacity() * std::mem::size_of::<bool>()
        + assigned.capacity() * std::mem::size_of::<bool>();
    components
}

/// Update the Kosaraju peak from O(1) maintained capacity aggregates. The
/// caller supplies the discovered-member sum so this never traverses it.
#[allow(clippy::too_many_arguments)]
fn record_kosaraju_peak(
    counters: &mut ProductionCounters,
    baseline_bytes: usize,
    visited: &Vec<bool>,
    assigned: &Vec<bool>,
    finish_order: &Vec<usize>,
    forward_stack: &Vec<DfsFrame>,
    reverse_stack: &Vec<usize>,
    components: &Vec<Vec<usize>>,
    discovered_member_bytes: usize,
    current_member_bytes: usize,
) {
    let bytes = baseline_bytes
        + logical_capacity_bytes(visited)
        + logical_capacity_bytes(assigned)
        + logical_capacity_bytes(finish_order)
        + logical_capacity_bytes(forward_stack)
        + logical_capacity_bytes(reverse_stack)
        + logical_capacity_bytes(components)
        + discovered_member_bytes
        + current_member_bytes;
    counters.scc_kosaraju_workspace_peak_bytes =
        counters.scc_kosaraju_workspace_peak_bytes.max(bytes);
}

fn schedule_dependency_sinks(
    components: &[SccComponent],
    predecessors: &mut Vec<Vec<usize>>,
    open_dependencies: &mut Vec<usize>,
    condensation_edge_count: usize,
    baseline_bytes: usize,
    predecessor_bytes: usize,
    counters: &mut ProductionCounters,
) -> Result<Vec<usize>, CollectionAvailabilityError> {
    let mut ready = ReadyQueue::default();
    for (component, &dependencies) in open_dependencies.iter().enumerate() {
        counters.scc_condensation_node_visits += 1;
        if dependencies == 0 {
            ready.push(
                (
                    components[component].id.canonical_definition.ordinal(),
                    component,
                ),
                counters,
            );
        }
    }
    let mut ordered = Vec::with_capacity(components.len());
    record_scheduler_peak(
        counters,
        baseline_bytes,
        predecessor_bytes,
        logical_capacity_bytes(open_dependencies),
        logical_capacity_bytes(&ready.entries),
        logical_capacity_bytes(&ordered),
    );
    while let Some((_, component)) = ready.pop_min(counters) {
        ordered.push(component);
        record_scheduler_peak(
            counters,
            baseline_bytes,
            predecessor_bytes,
            logical_capacity_bytes(open_dependencies),
            logical_capacity_bytes(&ready.entries),
            logical_capacity_bytes(&ordered),
        );
        for predecessor in predecessors[component].drain(..) {
            counters.scc_condensation_edge_visits += 1;
            let dependencies = open_dependencies
                .get_mut(predecessor)
                .ok_or(CollectionAvailabilityError::NonTotalSccComponentMap)?;
            *dependencies = dependencies
                .checked_sub(1)
                .ok_or(CollectionAvailabilityError::NonTotalSccComponentMap)?;
            if *dependencies == 0 {
                ready.push(
                    (
                        components[predecessor].id.canonical_definition.ordinal(),
                        predecessor,
                    ),
                    counters,
                );
            }
        }
        record_scheduler_peak(
            counters,
            baseline_bytes,
            predecessor_bytes,
            logical_capacity_bytes(open_dependencies),
            logical_capacity_bytes(&ready.entries),
            logical_capacity_bytes(&ordered),
        );
    }
    if ordered.len() != components.len()
        || counters.scc_condensation_edge_visits != condensation_edge_count
    {
        return Err(CollectionAvailabilityError::NonTotalSccComponentMap);
    }
    Ok(ordered)
}

fn record_scheduler_peak(
    counters: &mut ProductionCounters,
    baseline_bytes: usize,
    predecessor_bytes: usize,
    open_dependencies_bytes: usize,
    ready_bytes: usize,
    ordered_bytes: usize,
) {
    let bytes =
        baseline_bytes + predecessor_bytes + open_dependencies_bytes + ready_bytes + ordered_bytes;
    counters.scc_scheduler_workspace_peak_bytes =
        counters.scc_scheduler_workspace_peak_bytes.max(bytes);
}

/// Logical byte accounting uses each `Vec`/`HashMap`/`HashSet` public capacity
/// times its stored element or key/value slot size. It includes the owned slot
/// arrays listed by each phase; it excludes allocator metadata, hash control
/// bytes, fragmentation, allocation timing, and referent payloads behind IDs.
fn logical_vec_bytes<T>(items: &Vec<T>) -> usize {
    items.capacity() * std::mem::size_of::<T>()
}

fn logical_capacity_bytes<T>(items: &Vec<T>) -> usize {
    logical_vec_bytes(items)
}

fn logical_map_bytes<K, V>(items: &HashMap<K, V>) -> usize {
    items.capacity() * std::mem::size_of::<(K, V)>()
}

fn logical_set_bytes<T>(items: &HashSet<T>) -> usize {
    items.capacity() * std::mem::size_of::<T>()
}

/// Allocation-free ordered-use sorting and all live graph/index allocations.
fn graph_phase_bytes(
    ordered_uses: &Vec<&DefinitionUse>,
    forward: &Vec<Vec<GraphArc>>,
    reverse: &Vec<Vec<usize>>,
    seen_uses: &HashSet<DefinitionUseId>,
    node_for_definition: &HashMap<DefinitionOrderId, usize>,
) -> usize {
    logical_vec_bytes(ordered_uses)
        + logical_vec_bytes(forward)
        + forward
            .iter()
            .map(|arcs| {
                logical_vec_bytes(arcs)
                    + arcs
                        .iter()
                        .map(|arc| logical_vec_bytes(&arc.payloads))
                        .sum::<usize>()
            })
            .sum::<usize>()
        + logical_vec_bytes(reverse)
        + reverse.iter().map(logical_vec_bytes).sum::<usize>()
        + logical_set_bytes(seen_uses)
        + logical_map_bytes(node_for_definition)
}

fn graph_arc_storage_bytes(arcs: &Vec<GraphArc>) -> usize {
    logical_vec_bytes(arcs)
        + arcs
            .iter()
            .map(|arc| logical_vec_bytes(&arc.payloads))
            .sum::<usize>()
}

fn component_bytes(components: &Vec<SccComponent>) -> usize {
    logical_vec_bytes(components)
        + components
            .iter()
            .map(|component| {
                logical_vec_bytes(&component.members)
                    + logical_vec_bytes(&component.internal_uses)
                    + logical_vec_bytes(&component.incoming_uses)
            })
            .sum::<usize>()
}

fn predecessor_bytes(predecessors: &Vec<Vec<usize>>) -> usize {
    logical_vec_bytes(predecessors) + predecessors.iter().map(logical_vec_bytes).sum::<usize>()
}

fn retained_plan_bytes(
    components: &Vec<SccComponent>,
    component_positions: &HashMap<SccComponentId, usize>,
    component_of_definition: &HashMap<DefinitionOrderId, SccComponentId>,
) -> usize {
    component_bytes(components)
        + logical_map_bytes(component_positions)
        + logical_map_bytes(component_of_definition)
}

fn component_storage_bytes(component: &SccComponent) -> usize {
    logical_vec_bytes(&component.members)
        + logical_vec_bytes(&component.internal_uses)
        + logical_vec_bytes(&component.incoming_uses)
}

pub(super) fn f1_input_retained_bytes<T>(definitions: &[T], uses: &[DefinitionUse]) -> usize {
    definitions.len() * std::mem::size_of::<T>() + uses.len() * std::mem::size_of::<DefinitionUse>()
}
