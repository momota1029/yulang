//! DefId 間依存を incremental に管理する SCC machine。
//!
//! method selection は型制約が進んだあとで解けるため、DefId の依存 graph は一度で確定しない。
//! そのため全体 Tarjan を毎回やり直すのではなく、open component graph を持ち、
//! 新しい edge が cycle を閉じた時だけ関係 component を merge する。
//!
//! この machine は量化タイミングも所有する。component が lowering 完了済みで、
//! method dependency も outgoing SCC edge も持たなくなったら `QuantifyComponent` を出し、
//! open graph から削除する。削除された component へ入っていた use edge は `InstantiateUse` に変換する。

use std::collections::VecDeque;

use poly::expr::DefId;
use poly::types::TypeVar;
use rustc_hash::{FxHashMap, FxHashSet};

/// open SCC graph と量化済み def を持つ machine。
///
/// `quantified` に入った def は open graph から消えている。以後その def への use は edge を張らず、
/// `InstantiateUse` event になる。open component はまだ量化できない def の集合で、
/// method dependency count と outgoing edge が 0 になるまで保持する。
pub struct SccMachine {
    graph: ComponentGraph,
    quantified: FxHashMap<DefId, TypeVar>,
    events: Vec<SccEvent>,
}

impl SccMachine {
    pub fn new() -> Self {
        Self {
            graph: ComponentGraph::new(),
            quantified: FxHashMap::default(),
            events: Vec::new(),
        }
    }

    pub fn apply(&mut self, input: SccInput) {
        match input {
            SccInput::UseResolved {
                parent,
                target,
                use_value,
            } => self.add_use(parent, target, use_value),
            SccInput::RegisterDef { def, root } => self.register_def(def, root),
            SccInput::DefFinished { def } => self.finish_def(def),
            SccInput::MethodDependencyAdded { parent } => self.add_method_dependency(parent),
            SccInput::MethodDependencyResolved { parent } => self.resolve_method_dependency(parent),
        }
    }

    pub fn use_resolved(&mut self, input: SccInput) {
        self.apply(input);
    }

    pub fn register_def(&mut self, def: DefId, root: TypeVar) {
        if self.quantified.contains_key(&def) {
            self.quantified.insert(def, root);
            return;
        }

        let component = self.graph.ensure_component(def);
        self.graph.register_def(def, root);
        self.settle_components([component]);
    }

    pub fn finish_def(&mut self, def: DefId) {
        if self.quantified.contains_key(&def) {
            return;
        }

        let component = self.graph.ensure_component(def);
        self.graph.finish_def(def);
        self.settle_components([component]);
    }

    pub fn add_method_dependency(&mut self, parent: DefId) {
        if self.quantified.contains_key(&parent) {
            return;
        }

        let component = self.graph.ensure_component(parent);
        self.graph.add_method_dependency(component);
    }

    pub fn resolve_method_dependency(&mut self, parent: DefId) {
        let Some(component) = self.graph.component_of(parent) else {
            return;
        };
        self.graph.resolve_method_dependency(component);
        self.settle_components([component]);
    }

    pub fn take_events(&mut self) -> Vec<SccEvent> {
        std::mem::take(&mut self.events)
    }

    fn add_use(&mut self, parent: DefId, target: DefId, use_value: TypeVar) {
        if self.quantified.contains_key(&target) {
            self.events
                .push(SccEvent::InstantiateUse { target, use_value });
            self.settle_def(parent);
            return;
        }

        let from = self.graph.ensure_component(parent);
        let to = self.graph.ensure_component(target);
        if from == to {
            return;
        }

        let edge = UseEdge { target, use_value };
        let edge_was_new = self.graph.add_use_edge(from, to, edge);
        if !edge_was_new {
            return;
        }

        if self.graph.can_reach(to, from) {
            let cycle = self.graph.cycle_closed_by(from, to);
            let merged = self.graph.merge_components(cycle);
            self.events.push(SccEvent::MergeComponents {
                components: merged.components,
                merged: merged.members,
            });
            self.settle_components([merged.id]);
        } else {
            self.events.push(SccEvent::ComponentEdgeAdded {
                from: self.graph.members(from),
                to: self.graph.members(to),
            });
        }
    }

    fn settle_def(&mut self, def: DefId) {
        if let Some(component) = self.graph.component_of(def) {
            self.settle_components([component]);
        }
    }

    fn settle_components<I>(&mut self, components: I)
    where
        I: IntoIterator<Item = ComponentId>,
    {
        let mut queue = VecDeque::from_iter(components);
        while let Some(component) = queue.pop_front() {
            let Some(removed) = self.graph.remove_ready_component(component) else {
                continue;
            };

            for (def, root) in &removed.quantified {
                self.quantified.insert(*def, *root);
            }
            self.events.push(SccEvent::QuantifyComponent {
                component: removed.members,
                roots: removed.roots,
            });

            for use_edge in removed.incoming_uses {
                self.events.push(SccEvent::InstantiateUse {
                    target: use_edge.target,
                    use_value: use_edge.use_value,
                });
            }

            queue.extend(removed.predecessors);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// SCC machine へ渡す入力。
///
/// `UseResolved` は `parent` から `target` への use が確定したことを表す。
/// `RegisterDef` / `DefFinished` は、量化 ready 判定に必要な def 側の情報。
/// method dependency は selection がまだ解けていない間、component の量化を止めるために使う。
pub enum SccInput {
    UseResolved {
        parent: DefId,
        target: DefId,
        use_value: TypeVar,
    },
    RegisterDef {
        def: DefId,
        root: TypeVar,
    },
    DefFinished {
        def: DefId,
    },
    MethodDependencyAdded {
        parent: DefId,
    },
    MethodDependencyResolved {
        parent: DefId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// SCC machine が外へ出す event。
///
/// `ComponentEdgeAdded` は非循環 edge の追加。
/// `MergeComponents` は新 edge が cycle を閉じ、複数 component が1つになったことを表す。
/// `QuantifyComponent` はこの component を generalize してよいという命令。
/// `InstantiateUse` は target が量化済みになったため、use-site に scheme を展開してよいという命令。
pub enum SccEvent {
    ComponentEdgeAdded {
        from: Vec<DefId>,
        to: Vec<DefId>,
    },
    MergeComponents {
        components: Vec<Vec<DefId>>,
        merged: Vec<DefId>,
    },
    InstantiateUse {
        target: DefId,
        use_value: TypeVar,
    },
    QuantifyComponent {
        component: Vec<DefId>,
        roots: Vec<TypeVar>,
    },
}

#[derive(Debug, Clone)]
/// 量化前の component graph。
///
/// node は component、edge は未量化 target への use dependency。
/// edge payload には、target def と use-site の型 slot を残す。target component が量化された瞬間、
/// incoming edge payload から `InstantiateUse` を作るため。
struct ComponentGraph {
    components: FxHashMap<ComponentId, Component>,
    def_to_component: FxHashMap<DefId, ComponentId>,
    edges: FxHashMap<ComponentId, FxHashMap<ComponentId, Vec<UseEdge>>>,
    reverse_edges: FxHashMap<ComponentId, FxHashSet<ComponentId>>,
    next_component: u32,
}

impl ComponentGraph {
    fn new() -> Self {
        Self {
            components: FxHashMap::default(),
            def_to_component: FxHashMap::default(),
            edges: FxHashMap::default(),
            reverse_edges: FxHashMap::default(),
            next_component: 0,
        }
    }

    fn ensure_component(&mut self, def: DefId) -> ComponentId {
        if let Some(component) = self.def_to_component.get(&def) {
            return *component;
        }

        let id = ComponentId(self.next_component);
        self.next_component += 1;
        self.components.insert(id, Component::new(def));
        self.def_to_component.insert(def, id);
        id
    }

    fn component_of(&self, def: DefId) -> Option<ComponentId> {
        self.def_to_component.get(&def).copied()
    }

    fn members(&self, component: ComponentId) -> Vec<DefId> {
        self.components
            .get(&component)
            .map(|component| component.members.clone())
            .unwrap_or_default()
    }

    fn register_def(&mut self, def: DefId, root: TypeVar) {
        let component = self.ensure_component(def);
        self.components
            .get_mut(&component)
            .expect("component must exist after ensure_component")
            .roots
            .insert(def, root);
    }

    fn finish_def(&mut self, def: DefId) {
        let component = self.ensure_component(def);
        self.components
            .get_mut(&component)
            .expect("component must exist after ensure_component")
            .finished
            .insert(def);
    }

    fn add_method_dependency(&mut self, component: ComponentId) {
        if let Some(component) = self.components.get_mut(&component) {
            component.method_dependencies += 1;
        }
    }

    fn resolve_method_dependency(&mut self, component: ComponentId) {
        if let Some(component) = self.components.get_mut(&component) {
            component.method_dependencies = component.method_dependencies.saturating_sub(1);
        }
    }

    fn add_use_edge(&mut self, from: ComponentId, to: ComponentId, edge: UseEdge) -> bool {
        let uses = self.edges.entry(from).or_default().entry(to).or_default();
        let edge_was_new = uses.is_empty();
        uses.push(edge);
        sort_use_edges(uses);
        self.reverse_edges.entry(to).or_default().insert(from);
        edge_was_new
    }

    fn can_reach(&self, start: ComponentId, target: ComponentId) -> bool {
        if start == target {
            return true;
        }

        let mut seen = FxHashSet::default();
        let mut stack = vec![start];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(edges) = self.edges.get(&current) {
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

    fn cycle_closed_by(&self, from: ComponentId, to: ComponentId) -> Vec<ComponentId> {
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

    fn reachable_from(&self, start: ComponentId) -> FxHashSet<ComponentId> {
        let mut seen = FxHashSet::default();
        let mut stack = vec![start];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(edges) = self.edges.get(&current) {
                stack.extend(edges.keys().copied());
            }
        }
        seen
    }

    fn reaching_to(&self, target: ComponentId) -> FxHashSet<ComponentId> {
        let mut seen = FxHashSet::default();
        let mut stack = vec![target];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(sources) = self.reverse_edges.get(&current) {
                stack.extend(sources.iter().copied());
            }
        }
        seen
    }

    fn merge_components(&mut self, components: Vec<ComponentId>) -> MergedComponent {
        let mut components = components;
        sort_components(&mut components);
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

        self.rebuild_edges_after_merge(merged_id, &merge_set);

        MergedComponent {
            id: merged_id,
            components: event_components,
            members: merged_members,
        }
    }

    fn rebuild_edges_after_merge(
        &mut self,
        merged_id: ComponentId,
        merge_set: &FxHashSet<ComponentId>,
    ) {
        let old_edges = std::mem::take(&mut self.edges);
        self.reverse_edges.clear();

        for (from, targets) in old_edges {
            let new_from = if merge_set.contains(&from) {
                merged_id
            } else {
                from
            };
            for (to, mut uses) in targets {
                let new_to = if merge_set.contains(&to) {
                    merged_id
                } else {
                    to
                };
                if new_from == new_to {
                    continue;
                }
                let entry = self
                    .edges
                    .entry(new_from)
                    .or_default()
                    .entry(new_to)
                    .or_default();
                entry.append(&mut uses);
                sort_use_edges(entry);
                self.reverse_edges
                    .entry(new_to)
                    .or_default()
                    .insert(new_from);
            }
        }
    }

    fn remove_ready_component(&mut self, component: ComponentId) -> Option<RemovedComponent> {
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
        for target in reverse_cleanup {
            if let Some(sources) = self.reverse_edges.get_mut(&target) {
                sources.remove(&component);
            }
        }
        self.remove_empty_reverse_entries();

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

    fn is_ready_to_quantify(&self, component: ComponentId) -> bool {
        let Some(component_data) = self.components.get(&component) else {
            return false;
        };
        let has_outgoing_edges = self
            .edges
            .get(&component)
            .map(|targets| !targets.is_empty())
            .unwrap_or(false);
        !has_outgoing_edges
            && component_data.method_dependencies == 0
            && component_data.members.iter().all(|def| {
                component_data.finished.contains(def) && component_data.roots.contains_key(def)
            })
    }

    fn remove_empty_reverse_entries(&mut self) {
        self.reverse_edges.retain(|_, sources| !sources.is_empty());
    }
}

#[derive(Debug, Clone)]
/// open component の中身。
///
/// `members` は同じ SCC に属する DefId。`roots` は各 DefId の root type var。
/// `finished` は lowering が完了した DefId。`method_dependencies` は未解決 method selection など、
/// edge としてまだ確定していない依存の数。
struct Component {
    members: Vec<DefId>,
    roots: FxHashMap<DefId, TypeVar>,
    finished: FxHashSet<DefId>,
    method_dependencies: usize,
}

impl Component {
    fn new(def: DefId) -> Self {
        Self {
            members: vec![def],
            roots: FxHashMap::default(),
            finished: FxHashSet::default(),
            method_dependencies: 0,
        }
    }

    fn empty() -> Self {
        Self {
            members: Vec::new(),
            roots: FxHashMap::default(),
            finished: FxHashSet::default(),
            method_dependencies: 0,
        }
    }

    fn absorb(&mut self, component: Component) {
        self.members.extend(component.members);
        self.roots.extend(component.roots);
        self.finished.extend(component.finished);
        self.method_dependencies += component.method_dependencies;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// open component を指す machine-local ID。
struct ComponentId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// component 間 use edge に残す payload。
///
/// edge の target component が量化されたとき、この情報から use-site instantiation event を作る。
struct UseEdge {
    target: DefId,
    use_value: TypeVar,
}

#[derive(Debug, Clone)]
/// merge event を作るために、merge 後の ID と表示用 member list を一緒に返す値。
struct MergedComponent {
    id: ComponentId,
    components: Vec<Vec<DefId>>,
    members: Vec<DefId>,
}

#[derive(Debug, Clone)]
/// ready component を graph から外した結果。
///
/// incoming use edge と predecessor を一緒に返し、`SccMachine` が event を吐いたあとに
/// predecessor の量化判定を cascade できるようにする。
struct RemovedComponent {
    members: Vec<DefId>,
    roots: Vec<TypeVar>,
    quantified: Vec<(DefId, TypeVar)>,
    incoming_uses: Vec<UseEdge>,
    predecessors: Vec<ComponentId>,
}

fn sort_defs(defs: &mut [DefId]) {
    defs.sort_by_key(|def| def.0);
}

fn sort_components(components: &mut [ComponentId]) {
    components.sort_by_key(|component| component.0);
}

fn sort_use_edges(edges: &mut [UseEdge]) {
    edges.sort_by_key(|edge| (edge.target.0, edge.use_value.0));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolved_open_use_adds_component_edge_event() {
        let mut machine = SccMachine::new();

        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(3),
        });

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![DefId(1)],
                to: vec![DefId(2)]
            }]
        );
    }

    #[test]
    fn quantified_target_emits_instantiate_use_without_edge() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(2), TypeVar(20));
        machine.finish_def(DefId(2));
        machine.take_events();

        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(3),
        });

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::InstantiateUse {
                target: DefId(2),
                use_value: TypeVar(3),
            }]
        );
    }

    #[test]
    fn edge_that_closes_cycle_merges_only_related_components() {
        let mut machine = SccMachine::new();
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(12),
        });
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(2),
            target: DefId(3),
            use_value: TypeVar(23),
        });
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(4),
            target: DefId(5),
            use_value: TypeVar(45),
        });
        machine.take_events();

        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(3),
            target: DefId(1),
            use_value: TypeVar(31),
        });

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::MergeComponents {
                components: vec![vec![DefId(1)], vec![DefId(2)], vec![DefId(3)]],
                merged: vec![DefId(1), DefId(2), DefId(3)],
            }]
        );
    }

    #[test]
    fn method_dependency_blocks_quantification_until_resolved() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.add_method_dependency(DefId(1));
        machine.finish_def(DefId(1));

        assert_eq!(machine.take_events(), vec![]);

        machine.resolve_method_dependency(DefId(1));

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::QuantifyComponent {
                component: vec![DefId(1)],
                roots: vec![TypeVar(10)],
            }]
        );
    }

    #[test]
    fn open_dependency_blocks_quantification_until_target_quantifies() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.register_def(DefId(2), TypeVar(20));
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(12),
        });
        machine.take_events();

        machine.finish_def(DefId(1));
        assert_eq!(machine.take_events(), vec![]);

        machine.finish_def(DefId(2));
        assert_eq!(
            machine.take_events(),
            vec![
                SccEvent::QuantifyComponent {
                    component: vec![DefId(2)],
                    roots: vec![TypeVar(20)],
                },
                SccEvent::InstantiateUse {
                    target: DefId(2),
                    use_value: TypeVar(12),
                },
                SccEvent::QuantifyComponent {
                    component: vec![DefId(1)],
                    roots: vec![TypeVar(10)],
                },
            ]
        );
    }

    #[test]
    fn finished_cycle_quantifies_as_one_component_after_merge() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.register_def(DefId(2), TypeVar(20));
        machine.finish_def(DefId(1));
        machine.finish_def(DefId(2));
        assert_eq!(
            machine.take_events(),
            vec![
                SccEvent::QuantifyComponent {
                    component: vec![DefId(1)],
                    roots: vec![TypeVar(10)]
                },
                SccEvent::QuantifyComponent {
                    component: vec![DefId(2)],
                    roots: vec![TypeVar(20)]
                }
            ]
        );

        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.register_def(DefId(2), TypeVar(20));
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(12),
        });
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(2),
            target: DefId(1),
            use_value: TypeVar(21),
        });
        machine.take_events();

        machine.finish_def(DefId(1));
        machine.finish_def(DefId(2));

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::QuantifyComponent {
                component: vec![DefId(1), DefId(2)],
                roots: vec![TypeVar(10), TypeVar(20)],
            }]
        );
    }
}
