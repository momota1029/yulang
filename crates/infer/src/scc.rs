//! DefId 間依存を incremental に管理する SCC machine。
//!
//! method selection は型制約が進んだあとで解けるため、DefId の依存 graph は一度で確定しない。
//! そのため全体 Tarjan を毎回やり直すのではなく、open component graph を持ち、
//! 新しい edge が cycle を閉じた時だけ関係 component を merge する。
//!
//! この machine は量化タイミングも所有する。component が lowering 完了済みで、
//! method dependency も outgoing SCC edge も持たなくなったら `QuantifyComponent` を出し、
//! open graph から削除する。削除された component へ入っていた use edge は `InstantiateUse` に変換する。

mod graph;

use std::collections::VecDeque;

use poly::expr::DefId;
use poly::types::TypeVar;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::typing::BindingFetch;
use graph::{ComponentGraph, ComponentId, OpenUse, UseEdge};

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
            SccInput::DependencyAdded { parent, target } => self.add_dependency(parent, target),
            SccInput::RegisterDef { def, root } => self.register_def(def, root),
            SccInput::DefFetchRecorded { def, fetch } => self.record_fetch(def, fetch),
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
        let open_uses = self.graph.register_def_and_open_uses(def, root);
        for open_use in open_uses {
            self.events.push(open_use.into_event());
        }
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

    pub fn root_of(&self, def: DefId) -> Option<TypeVar> {
        self.graph.root_of(def)
    }

    pub fn fetch_of(&self, def: DefId) -> BindingFetch {
        self.graph.fetch_of(def)
    }

    pub fn selection_fallback_ready(&self, parent: DefId) -> bool {
        if self.quantified.contains_key(&parent) {
            return true;
        }
        let Some(component) = self.graph.component_of(parent) else {
            return true;
        };
        self.graph.is_blocked_only_by_method_dependencies(component)
    }

    fn record_fetch(&mut self, def: DefId, fetch: BindingFetch) {
        self.graph.record_fetch(def, fetch);
        let Some(component) = self.graph.component_of(def) else {
            return;
        };
        self.report_computed_fetch_cycle_if_needed(component);
        self.settle_components([component]);
    }

    fn add_use(&mut self, parent: DefId, target: DefId, use_value: TypeVar) {
        if self.quantified.contains_key(&target) {
            self.events.push(SccEvent::InstantiateUse {
                parent,
                target,
                use_value,
            });
            self.settle_def(parent);
            return;
        }

        let from = self.graph.ensure_component(parent);
        let to = self.graph.ensure_component(target);
        if from == to {
            let edge = UseEdge {
                parent,
                target,
                use_value: Some(use_value),
            };
            if let Some(open_use) = self.graph.add_internal_use(from, edge) {
                self.events.push(open_use.into_event());
            }
            self.report_computed_fetch_cycle_if_needed(from);
            self.settle_components([from]);
            return;
        }

        let edge = UseEdge {
            parent,
            target,
            use_value: Some(use_value),
        };
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
            for open_use in merged.open_uses {
                self.events.push(open_use.into_event());
            }
            self.report_computed_fetch_cycle_if_needed(merged.id);
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
                if let Some(use_value) = use_edge.use_value {
                    self.events.push(SccEvent::InstantiateUse {
                        parent: use_edge.parent,
                        target: use_edge.target,
                        use_value,
                    });
                }
            }

            queue.extend(removed.predecessors);
        }
    }

    fn add_dependency(&mut self, parent: DefId, target: DefId) {
        if self.quantified.contains_key(&target) {
            self.settle_def(parent);
            return;
        }

        let from = self.graph.ensure_component(parent);
        let to = self.graph.ensure_component(target);
        if from == to {
            self.settle_components([from]);
            return;
        }

        let edge = UseEdge {
            parent,
            target,
            use_value: None,
        };
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
            for open_use in merged.open_uses {
                self.events.push(open_use.into_event());
            }
            self.report_computed_fetch_cycle_if_needed(merged.id);
            self.settle_components([merged.id]);
        } else {
            self.events.push(SccEvent::ComponentEdgeAdded {
                from: self.graph.members(from),
                to: self.graph.members(to),
            });
        }
    }

    fn report_computed_fetch_cycle_if_needed(&mut self, component: ComponentId) {
        let Some(issue) = self.graph.computed_fetch_cycle(component) else {
            return;
        };
        self.graph.mark_computed_fetch_cycle_reported(component);
        self.events.push(SccEvent::ComputedFetchCycle {
            component: issue.component,
            parent: issue.parent,
            target: issue.target,
        });
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
    DependencyAdded {
        parent: DefId,
        target: DefId,
    },
    RegisterDef {
        def: DefId,
        root: TypeVar,
    },
    DefFetchRecorded {
        def: DefId,
        fetch: BindingFetch,
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
/// `OpenUse` は target が同じ未量化 SCC 内に入ったため、use-site と target root を直接つなぐ命令。
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
    OpenUse {
        target: DefId,
        target_root: TypeVar,
        use_value: TypeVar,
    },
    InstantiateUse {
        parent: DefId,
        target: DefId,
        use_value: TypeVar,
    },
    ComputedFetchCycle {
        component: Vec<DefId>,
        parent: DefId,
        target: DefId,
    },
    QuantifyComponent {
        component: Vec<DefId>,
        roots: Vec<TypeVar>,
    },
}

fn sort_defs(defs: &mut [DefId]) {
    defs.sort_by_key(|def| def.0);
}

fn sort_components(components: &mut [ComponentId]) {
    components.sort_by_key(|component| component.0);
}

fn sort_use_edges(edges: &mut [UseEdge]) {
    edges.sort_by_key(|edge| {
        (
            edge.parent.0,
            edge.target.0,
            edge.use_value.map(|value| value.0).unwrap_or(u32::MAX),
        )
    });
}

fn sort_open_uses(uses: &mut [OpenUse]) {
    uses.sort_by_key(|use_site| {
        (
            use_site.target.0,
            use_site.target_root.0,
            use_site.use_value.0,
        )
    });
}

fn push_unique_use(uses: &mut Vec<UseEdge>, edge: UseEdge) {
    if !uses.contains(&edge) {
        uses.push(edge);
        sort_use_edges(uses);
    }
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
                parent: DefId(1),
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
    fn computed_fetch_cycle_reports_when_fetch_is_known_before_merge() {
        let mut machine = SccMachine::new();
        machine.apply(SccInput::DefFetchRecorded {
            def: DefId(2),
            fetch: BindingFetch::FetchComputation,
        });
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(12),
        });
        machine.take_events();

        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(2),
            target: DefId(1),
            use_value: TypeVar(21),
        });

        assert_eq!(
            machine.take_events(),
            vec![
                SccEvent::MergeComponents {
                    components: vec![vec![DefId(1)], vec![DefId(2)]],
                    merged: vec![DefId(1), DefId(2)],
                },
                SccEvent::ComputedFetchCycle {
                    component: vec![DefId(1), DefId(2)],
                    parent: DefId(1),
                    target: DefId(2),
                },
            ]
        );
    }

    #[test]
    fn computed_fetch_cycle_reports_when_fetch_is_recorded_after_merge() {
        let mut machine = SccMachine::new();
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

        machine.apply(SccInput::DefFetchRecorded {
            def: DefId(2),
            fetch: BindingFetch::FetchComputation,
        });

        assert_eq!(
            machine.take_events(),
            vec![SccEvent::ComputedFetchCycle {
                component: vec![DefId(1), DefId(2)],
                parent: DefId(1),
                target: DefId(2),
            }]
        );
    }

    #[test]
    fn cycle_merge_opens_internal_uses_when_roots_are_known() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.register_def(DefId(2), TypeVar(20));
        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(1),
            target: DefId(2),
            use_value: TypeVar(12),
        });
        machine.take_events();

        machine.use_resolved(SccInput::UseResolved {
            parent: DefId(2),
            target: DefId(1),
            use_value: TypeVar(21),
        });

        assert_eq!(
            machine.take_events(),
            vec![
                SccEvent::MergeComponents {
                    components: vec![vec![DefId(1)], vec![DefId(2)]],
                    merged: vec![DefId(1), DefId(2)],
                },
                SccEvent::OpenUse {
                    target: DefId(1),
                    target_root: TypeVar(10),
                    use_value: TypeVar(21),
                },
                SccEvent::OpenUse {
                    target: DefId(2),
                    target_root: TypeVar(20),
                    use_value: TypeVar(12),
                },
            ]
        );
    }

    #[test]
    fn internal_use_waits_until_target_root_is_registered() {
        let mut machine = SccMachine::new();
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

        assert_eq!(
            machine.take_events(),
            vec![
                SccEvent::ComponentEdgeAdded {
                    from: vec![DefId(1)],
                    to: vec![DefId(2)],
                },
                SccEvent::MergeComponents {
                    components: vec![vec![DefId(1)], vec![DefId(2)]],
                    merged: vec![DefId(1), DefId(2)],
                },
            ]
        );

        machine.register_def(DefId(2), TypeVar(20));
        assert_eq!(
            machine.take_events(),
            vec![SccEvent::OpenUse {
                target: DefId(2),
                target_root: TypeVar(20),
                use_value: TypeVar(12),
            }]
        );

        machine.register_def(DefId(1), TypeVar(10));
        assert_eq!(
            machine.take_events(),
            vec![SccEvent::OpenUse {
                target: DefId(1),
                target_root: TypeVar(10),
                use_value: TypeVar(21),
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
                    parent: DefId(1),
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
    fn non_instantiating_dependency_blocks_without_instantiate_event() {
        let mut machine = SccMachine::new();
        machine.register_def(DefId(1), TypeVar(10));
        machine.register_def(DefId(2), TypeVar(20));
        machine.apply(SccInput::DependencyAdded {
            parent: DefId(1),
            target: DefId(2),
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
