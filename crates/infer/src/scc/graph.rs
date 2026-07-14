use super::*;

pub(super) struct ComponentGraph {
    components: FxHashMap<ComponentId, Component>,
    def_to_component: FxHashMap<DefId, ComponentId>,
    edges: FxHashMap<ComponentId, FxHashMap<ComponentId, Vec<UseEdge>>>,
    reverse_edges: FxHashMap<ComponentId, FxHashSet<ComponentId>>,
    fetches: FxHashMap<DefId, BindingFetch>,
    stats: SccStats,
    next_component: u32,
}

impl ComponentGraph {
    pub(super) fn new() -> Self {
        Self {
            components: FxHashMap::default(),
            def_to_component: FxHashMap::default(),
            edges: FxHashMap::default(),
            reverse_edges: FxHashMap::default(),
            fetches: FxHashMap::default(),
            stats: SccStats::default(),
            next_component: 0,
        }
    }

    pub(super) fn stats(&self) -> SccStats {
        self.stats
    }

    pub(super) fn ensure_component(&mut self, def: DefId) -> ComponentId {
        if let Some(component) = self.def_to_component.get(&def) {
            return *component;
        }

        let id = ComponentId(self.next_component);
        self.next_component += 1;
        self.components.insert(id, Component::new(def));
        self.def_to_component.insert(def, id);
        id
    }

    pub(super) fn component_of(&self, def: DefId) -> Option<ComponentId> {
        self.def_to_component.get(&def).copied()
    }

    pub(super) fn root_of(&self, def: DefId) -> Option<TypeVar> {
        let component = self.component_of(def)?;
        self.components.get(&component)?.roots.get(&def).copied()
    }

    pub(super) fn record_fetch(&mut self, def: DefId, fetch: BindingFetch) {
        self.fetches.insert(def, fetch);
    }

    pub(super) fn fetch_of(&self, def: DefId) -> BindingFetch {
        self.fetches
            .get(&def)
            .copied()
            .unwrap_or(BindingFetch::FetchValue)
    }

    pub(super) fn members(&self, component: ComponentId) -> Vec<DefId> {
        self.components
            .get(&component)
            .map(|component| component.members.clone())
            .unwrap_or_default()
    }

    pub(super) fn register_def(&mut self, def: DefId, root: TypeVar) {
        let component = self.ensure_component(def);
        self.components
            .get_mut(&component)
            .expect("component must exist after ensure_component")
            .roots
            .insert(def, root);
    }

    pub(super) fn register_def_and_open_uses(&mut self, def: DefId, root: TypeVar) -> Vec<OpenUse> {
        let component = self.ensure_component(def);
        self.register_def(def, root);
        self.open_pending_uses_for(component, def)
    }

    pub(super) fn finish_def(&mut self, def: DefId) {
        let component = self.ensure_component(def);
        self.components
            .get_mut(&component)
            .expect("component must exist after ensure_component")
            .finished
            .insert(def);
    }

    pub(super) fn add_method_dependency(&mut self, component: ComponentId) {
        if let Some(component) = self.components.get_mut(&component) {
            component.method_dependencies += 1;
        }
    }

    pub(super) fn resolve_method_dependency(&mut self, component: ComponentId) {
        if let Some(component) = self.components.get_mut(&component) {
            component.method_dependencies = component.method_dependencies.saturating_sub(1);
        }
    }

    pub(super) fn add_conformance_pending(
        &mut self,
        component: ComponentId,
        member: DefId,
    ) -> bool {
        let Some(component) = self.components.get_mut(&component) else {
            return false;
        };
        if component.conformance_released.contains(&member) {
            return false;
        }
        component.conformance_pending.insert(member)
    }

    pub(super) fn release_conformance(&mut self, component: ComponentId, member: DefId) -> bool {
        let Some(component) = self.components.get_mut(&component) else {
            return false;
        };
        if !component.conformance_pending.remove(&member) {
            return false;
        }
        component.conformance_released.insert(member);
        true
    }

    pub(super) fn add_use_edge(
        &mut self,
        from: ComponentId,
        to: ComponentId,
        edge: UseEdge,
    ) -> bool {
        let targets = self.edges.entry(from).or_default();
        let edge_was_new = !targets.contains_key(&to);
        let uses = targets.entry(to).or_default();
        uses.push(edge);
        self.stats.payload_sorts += 1;
        self.stats.payload_sort_total_len += uses.len();
        sort_use_edges(uses);
        self.reverse_edges.entry(to).or_default().insert(from);
        edge_was_new
    }

    pub(super) fn add_dependency_edge(&mut self, from: ComponentId, to: ComponentId) -> bool {
        let targets = self.edges.entry(from).or_default();
        if targets.contains_key(&to) {
            self.stats.duplicate_dependency_payloads += 1;
            return false;
        }

        targets.insert(to, Vec::new());
        self.reverse_edges.entry(to).or_default().insert(from);
        true
    }

    pub(super) fn add_internal_use(
        &mut self,
        component: ComponentId,
        edge: UseEdge,
    ) -> Option<OpenUse> {
        let component = self
            .components
            .get_mut(&component)
            .expect("component must exist before adding internal use");
        push_unique_use(&mut component.internal_uses, edge);
        let Some(use_value) = edge.use_value else {
            return None;
        };
        if let Some(root) = component.roots.get(&edge.target).copied() {
            return Some(OpenUse {
                target: edge.target,
                target_root: root,
                use_value,
            });
        }
        push_unique_use(&mut component.pending_open_uses, edge);
        None
    }

    pub(super) fn open_pending_uses_for(
        &mut self,
        component: ComponentId,
        target: DefId,
    ) -> Vec<OpenUse> {
        let Some(component) = self.components.get_mut(&component) else {
            return Vec::new();
        };
        let Some(root) = component.roots.get(&target).copied() else {
            return Vec::new();
        };

        self.stats.pending_use_scans += 1;
        self.stats.pending_use_scan_count += component.pending_open_uses.len();
        let mut still_pending = Vec::new();
        let mut open_uses = Vec::new();
        for edge in component.pending_open_uses.drain(..) {
            if edge.target == target {
                let Some(use_value) = edge.use_value else {
                    continue;
                };
                open_uses.push(OpenUse {
                    target,
                    target_root: root,
                    use_value,
                });
            } else {
                still_pending.push(edge);
            }
        }
        component.pending_open_uses = still_pending;
        sort_open_uses(&mut open_uses);
        open_uses
    }

    pub(super) fn open_resolved_pending_uses(&mut self, component: ComponentId) -> Vec<OpenUse> {
        let targets = self
            .components
            .get(&component)
            .map(|component| {
                let mut targets = component.roots.keys().copied().collect::<Vec<_>>();
                sort_defs(&mut targets);
                targets
            })
            .unwrap_or_default();
        let mut open_uses = Vec::new();
        for target in targets {
            open_uses.extend(self.open_pending_uses_for(component, target));
        }
        sort_open_uses(&mut open_uses);
        open_uses
    }

    pub(super) fn can_reach(&mut self, start: ComponentId, target: ComponentId) -> bool {
        self.stats.reachability_calls += 1;
        if start == target {
            return true;
        }

        let mut seen = FxHashSet::default();
        let mut stack = vec![start];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            self.stats.reachability_nodes_visited += 1;
            if let Some(edges) = self.edges.get(&current) {
                self.stats.reachability_edges_visited += edges.len();
                for next in edges.keys() {
                    if *next == target {
                        return true;
                    }
                    stack.push(*next);
                }
            }
        }
        false
    }

    pub(super) fn cycle_closed_by(
        &mut self,
        from: ComponentId,
        to: ComponentId,
    ) -> Vec<ComponentId> {
        let mut forward = self.reachable_from(to);
        forward.insert(to);
        let mut backward = self.reaching_to(from);
        backward.insert(from);

        let mut cycle = forward
            .intersection(&backward)
            .copied()
            .filter(|component| self.components.contains_key(component))
            .collect::<Vec<_>>();
        sort_components(&mut cycle);
        cycle
    }

    pub(super) fn reachable_from(&mut self, start: ComponentId) -> FxHashSet<ComponentId> {
        self.stats.reachability_calls += 1;
        let mut seen = FxHashSet::default();
        let mut stack = vec![start];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            self.stats.reachability_nodes_visited += 1;
            if let Some(edges) = self.edges.get(&current) {
                self.stats.reachability_edges_visited += edges.len();
                stack.extend(edges.keys().copied());
            }
        }
        seen
    }

    pub(super) fn reaching_to(&mut self, target: ComponentId) -> FxHashSet<ComponentId> {
        self.stats.reachability_calls += 1;
        let mut seen = FxHashSet::default();
        let mut stack = vec![target];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            self.stats.reachability_nodes_visited += 1;
            if let Some(sources) = self.reverse_edges.get(&current) {
                self.stats.reachability_edges_visited += sources.len();
                stack.extend(sources.iter().copied());
            }
        }
        seen
    }

    pub(super) fn merge_components(&mut self, components: Vec<ComponentId>) -> MergedComponent {
        let mut components = components;
        sort_components(&mut components);
        self.stats.merge_count += 1;
        self.stats.merged_component_count += components.len();
        let merged_id = components[0];
        let merge_set = components.iter().copied().collect::<FxHashSet<_>>();
        let event_components = components
            .iter()
            .map(|component| self.members(*component))
            .collect::<Vec<_>>();

        let mut merged_component = Component::empty();
        for component in &components {
            let component = self
                .components
                .remove(component)
                .expect("cycle components must be open");
            merged_component.absorb(component);
        }
        sort_defs(&mut merged_component.members);
        for member in &merged_component.members {
            self.def_to_component.insert(*member, merged_id);
        }
        let merged_members = merged_component.members.clone();
        self.components.insert(merged_id, merged_component);

        let internal_uses = self.rebuild_edges_after_merge(merged_id, &merge_set);
        let mut open_uses = self.open_resolved_pending_uses(merged_id);
        for use_edge in internal_uses {
            if let Some(open_use) = self.add_internal_use(merged_id, use_edge) {
                open_uses.push(open_use);
            }
        }
        sort_open_uses(&mut open_uses);

        MergedComponent {
            id: merged_id,
            components: event_components,
            members: merged_members,
            open_uses,
        }
    }

    pub(super) fn rebuild_edges_after_merge(
        &mut self,
        merged_id: ComponentId,
        merge_set: &FxHashSet<ComponentId>,
    ) -> Vec<UseEdge> {
        let old_edges = std::mem::take(&mut self.edges);
        self.reverse_edges.clear();
        let mut internal_uses = Vec::new();

        for (from, targets) in old_edges {
            let new_from = if merge_set.contains(&from) {
                merged_id
            } else {
                from
            };
            for (to, mut uses) in targets {
                self.stats.rebuilt_edges += 1;
                self.stats.rebuilt_edge_payloads += uses.len();
                let new_to = if merge_set.contains(&to) {
                    merged_id
                } else {
                    to
                };
                if new_from == new_to {
                    internal_uses.append(&mut uses);
                    continue;
                }
                let entry = self
                    .edges
                    .entry(new_from)
                    .or_default()
                    .entry(new_to)
                    .or_default();
                entry.append(&mut uses);
                self.stats.payload_sorts += 1;
                self.stats.payload_sort_total_len += entry.len();
                sort_use_edges(entry);
                self.reverse_edges
                    .entry(new_to)
                    .or_default()
                    .insert(new_from);
            }
        }
        self.stats.payload_sorts += 1;
        self.stats.payload_sort_total_len += internal_uses.len();
        sort_use_edges(&mut internal_uses);
        internal_uses
    }

    pub(super) fn remove_ready_component(
        &mut self,
        component: ComponentId,
    ) -> Option<RemovedComponent> {
        if !self.is_ready_to_quantify(component) {
            return None;
        }

        let component_data = self.components.remove(&component)?;
        let members = component_data.members;
        let roots = members
            .iter()
            .map(|def| {
                *component_data
                    .roots
                    .get(def)
                    .expect("ready component must have roots for all members")
            })
            .collect::<Vec<_>>();
        let quantified = members
            .iter()
            .copied()
            .zip(roots.iter().copied())
            .collect::<Vec<_>>();

        for member in &members {
            self.def_to_component.remove(member);
        }

        let outgoing = self.edges.remove(&component).unwrap_or_default();
        let mut reverse_cleanup = outgoing.keys().copied().collect::<Vec<_>>();
        sort_components(&mut reverse_cleanup);
        let mut empty_reverse_targets = Vec::new();
        for target in reverse_cleanup {
            if let Some(sources) = self.reverse_edges.get_mut(&target) {
                sources.remove(&component);
                if sources.is_empty() {
                    empty_reverse_targets.push(target);
                }
            }
        }
        for target in empty_reverse_targets {
            self.reverse_edges.remove(&target);
        }

        let incoming_sources = self
            .reverse_edges
            .remove(&component)
            .map(|sources| {
                let mut sources = sources.into_iter().collect::<Vec<_>>();
                sort_components(&mut sources);
                sources
            })
            .unwrap_or_default();

        let mut incoming_uses = Vec::new();
        let mut predecessors = Vec::new();
        let mut empty_sources = Vec::new();
        for source in incoming_sources {
            if let Some(targets) = self.edges.get_mut(&source) {
                if let Some(mut uses) = targets.remove(&component) {
                    incoming_uses.append(&mut uses);
                    if self.components.contains_key(&source) {
                        predecessors.push(source);
                    }
                }
                if targets.is_empty() {
                    empty_sources.push(source);
                }
            }
        }
        for source in empty_sources {
            self.edges.remove(&source);
        }

        sort_use_edges(&mut incoming_uses);
        sort_components(&mut predecessors);
        predecessors.dedup();

        Some(RemovedComponent {
            members,
            roots,
            quantified,
            incoming_uses,
            predecessors,
        })
    }

    pub(super) fn is_ready_to_quantify(&mut self, component: ComponentId) -> bool {
        self.stats.ready_component_checks += 1;
        let Some(component_data) = self.components.get(&component) else {
            return false;
        };
        let has_outgoing_edges = self
            .edges
            .get(&component)
            .map(|targets| !targets.is_empty())
            .unwrap_or(false);
        if has_outgoing_edges
            || component_data.method_dependencies != 0
            || !component_data.conformance_pending.is_empty()
        {
            return false;
        }
        self.stats.ready_member_checks += component_data.members.len();
        component_data.members.iter().all(|def| {
            component_data.finished.contains(def) && component_data.roots.contains_key(def)
        })
    }

    pub(super) fn is_blocked_only_by_method_dependencies(&self, component: ComponentId) -> bool {
        let Some(component_data) = self.components.get(&component) else {
            return true;
        };
        let has_outgoing_edges = self
            .edges
            .get(&component)
            .map(|targets| !targets.is_empty())
            .unwrap_or(false);
        !has_outgoing_edges
            && component_data.method_dependencies > 0
            && component_data.conformance_pending.is_empty()
            && component_data.members.iter().all(|def| {
                component_data.finished.contains(def) && component_data.roots.contains_key(def)
            })
    }

    pub(super) fn candidate_independent_fallback_frontier(
        &self,
        member_is_captured: impl Fn(DefId) -> bool,
    ) -> Vec<CandidateIndependentFallbackComponent> {
        let mut candidates = self
            .components
            .iter()
            .filter_map(|(component, component_data)| {
                // This is exactly the existing selection-fallback readiness floor: complete,
                // conformance-free, edge-free, and blocked by one or more method dependencies.
                if !self.is_blocked_only_by_method_dependencies(*component) {
                    return None;
                }

                let has_captured_predecessor =
                    self.reverse_edges
                        .get(component)
                        .is_some_and(|predecessors| {
                            let mut predecessors = predecessors.iter().copied().collect::<Vec<_>>();
                            sort_components(&mut predecessors);
                            predecessors.into_iter().any(|predecessor| {
                                self.is_finished_captured_predecessor(
                                    predecessor,
                                    &member_is_captured,
                                )
                            })
                        });
                if !has_captured_predecessor {
                    return None;
                }

                let mut members = component_data.members.clone();
                sort_defs(&mut members);
                Some(CandidateIndependentFallbackComponent {
                    component_id: CandidateFallbackComponentId(component.0),
                    members,
                    method_dependencies: component_data.method_dependencies,
                })
            })
            .collect::<Vec<_>>();
        candidates.sort_by(|left, right| {
            left.members
                .iter()
                .map(|member| member.0)
                .cmp(right.members.iter().map(|member| member.0))
                .then_with(|| left.component_id.0.cmp(&right.component_id.0))
        });
        candidates
    }

    fn is_finished_captured_predecessor(
        &self,
        component: ComponentId,
        member_is_captured: &impl Fn(DefId) -> bool,
    ) -> bool {
        let Some(component_data) = self.components.get(&component) else {
            return false;
        };
        if component_data.conformance_pending.is_empty()
            || component_data.method_dependencies != 0
            || !self
                .edges
                .get(&component)
                .is_some_and(|targets| !targets.is_empty())
            || !component_data.members.iter().all(|def| {
                component_data.finished.contains(def) && component_data.roots.contains_key(def)
            })
        {
            return false;
        }

        let mut pending_members = component_data
            .conformance_pending
            .iter()
            .copied()
            .collect::<Vec<_>>();
        sort_defs(&mut pending_members);
        pending_members.into_iter().any(member_is_captured)
    }

    pub(super) fn first_ready_except_conformance(&self) -> Option<ConformanceReadyComponent> {
        let mut ready = self
            .components
            .iter()
            .filter_map(|(component, component_data)| {
                if component_data.conformance_pending.is_empty()
                    || component_data.method_dependencies != 0
                    || self
                        .edges
                        .get(component)
                        .is_some_and(|targets| !targets.is_empty())
                    || !component_data.members.iter().all(|def| {
                        component_data.finished.contains(def)
                            && component_data.roots.contains_key(def)
                    })
                {
                    return None;
                }

                let mut members = component_data.members.clone();
                sort_defs(&mut members);
                let mut pending_members = component_data
                    .conformance_pending
                    .iter()
                    .copied()
                    .collect::<Vec<_>>();
                sort_defs(&mut pending_members);
                Some(ConformanceReadyComponent {
                    members,
                    pending_members,
                })
            })
            .collect::<Vec<_>>();
        ready.sort_by_key(|component| {
            component
                .members
                .iter()
                .map(|member| member.0)
                .collect::<Vec<_>>()
        });
        ready.into_iter().next()
    }

    pub(super) fn computed_fetch_cycle(
        &self,
        component: ComponentId,
    ) -> Option<ComputedFetchCycle> {
        let component = self.components.get(&component)?;
        if component.computed_fetch_cycle_reported || component.members.len() <= 1 {
            return None;
        }
        component
            .internal_uses
            .iter()
            .copied()
            .filter(|edge| edge.use_value.is_some())
            .find(|edge| self.fetch_of(edge.target).runs_computation())
            .map(|edge| ComputedFetchCycle {
                component: component.members.clone(),
                parent: edge.parent,
                target: edge.target,
            })
    }

    pub(super) fn mark_computed_fetch_cycle_reported(&mut self, component: ComponentId) {
        if let Some(component) = self.components.get_mut(&component) {
            component.computed_fetch_cycle_reported = true;
        }
    }
}

struct Component {
    members: Vec<DefId>,
    roots: FxHashMap<DefId, TypeVar>,
    finished: FxHashSet<DefId>,
    pending_open_uses: Vec<UseEdge>,
    internal_uses: Vec<UseEdge>,
    method_dependencies: usize,
    conformance_pending: FxHashSet<DefId>,
    conformance_released: FxHashSet<DefId>,
    computed_fetch_cycle_reported: bool,
}

impl Component {
    pub(super) fn new(def: DefId) -> Self {
        Self {
            members: vec![def],
            roots: FxHashMap::default(),
            finished: FxHashSet::default(),
            pending_open_uses: Vec::new(),
            internal_uses: Vec::new(),
            method_dependencies: 0,
            conformance_pending: FxHashSet::default(),
            conformance_released: FxHashSet::default(),
            computed_fetch_cycle_reported: false,
        }
    }

    pub(super) fn empty() -> Self {
        Self {
            members: Vec::new(),
            roots: FxHashMap::default(),
            finished: FxHashSet::default(),
            pending_open_uses: Vec::new(),
            internal_uses: Vec::new(),
            method_dependencies: 0,
            conformance_pending: FxHashSet::default(),
            conformance_released: FxHashSet::default(),
            computed_fetch_cycle_reported: false,
        }
    }

    pub(super) fn absorb(&mut self, component: Component) {
        self.members.extend(component.members);
        self.roots.extend(component.roots);
        self.finished.extend(component.finished);
        self.pending_open_uses.extend(component.pending_open_uses);
        self.internal_uses.extend(component.internal_uses);
        self.method_dependencies += component.method_dependencies;
        self.conformance_pending
            .extend(component.conformance_pending);
        self.conformance_released
            .extend(component.conformance_released);
        self.computed_fetch_cycle_reported |= component.computed_fetch_cycle_reported;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// open component を指す machine-local ID。
pub(super) struct ComponentId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// component 間 use edge に残す payload。
///
/// edge の target component が量化されたとき、この情報から use-site instantiation event を作る。
pub(super) struct UseEdge {
    pub(super) parent: DefId,
    pub(super) target: DefId,
    pub(super) use_value: Option<TypeVar>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct OpenUse {
    pub(super) target: DefId,
    pub(super) target_root: TypeVar,
    pub(super) use_value: TypeVar,
}

impl OpenUse {
    pub(super) fn into_event(self) -> SccEvent {
        SccEvent::OpenUse {
            target: self.target,
            target_root: self.target_root,
            use_value: self.use_value,
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct ComputedFetchCycle {
    pub(super) component: Vec<DefId>,
    pub(super) parent: DefId,
    pub(super) target: DefId,
}

#[derive(Debug, Clone)]
/// merge event を作るために、merge 後の ID と表示用 member list を一緒に返す値。
pub(super) struct MergedComponent {
    pub(super) id: ComponentId,
    pub(super) components: Vec<Vec<DefId>>,
    pub(super) members: Vec<DefId>,
    pub(super) open_uses: Vec<OpenUse>,
}

#[derive(Debug, Clone)]
/// ready component を graph から外した結果。
///
/// incoming use edge と predecessor を一緒に返し、`SccMachine` が event を吐いたあとに
/// predecessor の量化判定を cascade できるようにする。
pub(super) struct RemovedComponent {
    pub(super) members: Vec<DefId>,
    pub(super) roots: Vec<TypeVar>,
    pub(super) quantified: Vec<(DefId, TypeVar)>,
    pub(super) incoming_uses: Vec<UseEdge>,
    pub(super) predecessors: Vec<ComponentId>,
}
