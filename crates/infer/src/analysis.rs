//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

use std::collections::VecDeque;

use poly::expr::{Arena as PolyArena, Def, DefId, RefId, SelectId, SelectResolution};
use poly::types::{Neg, Pos, Scheme, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::arena::Arena as InferArena;
use crate::constraints::ConstraintEvent;
use crate::generalize::{
    GeneralizedCompactRoot, finalize_generalized_compact_root_with_ancestors, generalize_type_var,
};
use crate::instantiate::instantiate_scheme;
use crate::scc::{SccEvent, SccInput, SccMachine};
use crate::uses::{RefUseTable, SelectionUseTable};

/// 推論中の複数 machine を束ねる session。
///
/// `poly` は最終 IR と解決結果を持つ。`infer` は型制約 machine を持つ。
/// `refs` / `selections` は use-site 型と parent、`scc` は def 間依存を持つ。
/// それぞれの責務を分けたまま、event queue で進行を同期する。
pub struct AnalysisSession {
    pub poly: PolyArena,
    pub infer: InferArena,
    pub refs: RefUseTable,
    pub selections: SelectionUseTable,
    pub scc: SccMachine,
    schemes: FxHashMap<DefId, GeneralizedCompactRoot>,
    scc_events: Vec<SccEvent>,
    work: VecDeque<AnalysisWork>,
}

impl AnalysisSession {
    pub fn new(poly: PolyArena) -> Self {
        Self {
            poly,
            infer: InferArena::new(),
            refs: RefUseTable::new(),
            selections: SelectionUseTable::new(),
            scc: SccMachine::new(),
            schemes: FxHashMap::default(),
            scc_events: Vec::new(),
            work: VecDeque::new(),
        }
    }

    pub fn enqueue(&mut self, work: AnalysisWork) {
        self.work.push_back(work);
    }

    pub fn work(&self) -> &VecDeque<AnalysisWork> {
        &self.work
    }

    pub fn has_pending_work(&self) -> bool {
        !self.work.is_empty() || !self.infer.constraints().events().is_empty()
    }

    pub fn route_constraint_events(&mut self) {
        for event in self.infer.constraints_mut().take_events() {
            if let ConstraintEvent::LowerBoundAdded { var, .. } = event {
                for select in self.selections.pending_for_lower_bound(var) {
                    self.enqueue(AnalysisWork::ProbeSelect(select));
                }
            }
        }
    }

    pub fn drain_work(&mut self) {
        while self.step() {}
    }

    pub fn step(&mut self) -> bool {
        self.route_constraint_events();
        let Some(work) = self.work.pop_front() else {
            return false;
        };
        self.apply_work(work);
        true
    }

    pub fn take_scc_events(&mut self) -> Vec<SccEvent> {
        self.route_scc_events();
        std::mem::take(&mut self.scc_events)
    }

    fn apply_work(&mut self, work: AnalysisWork) {
        match work {
            AnalysisWork::ResolveRef(_) | AnalysisWork::ProbeSelect(_) => {}
            AnalysisWork::ApplyRefResolution { ref_id, target } => {
                self.poly.resolve_ref(ref_id, target);
                if let Some(use_site) = self.refs.get(ref_id).copied() {
                    self.scc.use_resolved(SccInput::UseResolved {
                        parent: use_site.parent,
                        target,
                        use_value: use_site.value,
                    });
                }
            }
            AnalysisWork::ApplySelectionResolution { select_id, target } => {
                self.poly.resolve_select(select_id, target.resolution());
                let Some(use_site) = self.selections.get(select_id).copied() else {
                    return;
                };
                match target {
                    SelectionTarget::RecordField => {}
                    SelectionTarget::Method { def } => {
                        self.scc.use_resolved(SccInput::UseResolved {
                            parent: use_site.parent,
                            target: def,
                            use_value: use_site.method_value,
                        });
                    }
                    SelectionTarget::TypeclassMethod { member } => {
                        self.scc.use_resolved(SccInput::UseResolved {
                            parent: use_site.parent,
                            target: member,
                            use_value: use_site.method_value,
                        });
                    }
                }
            }
            AnalysisWork::Scc(input) => self.scc.apply(input),
        }
        self.route_scc_events();
    }

    fn route_scc_events(&mut self) {
        for event in self.scc.take_events() {
            match event {
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value,
                } => {
                    self.constrain_open_use(target_root, use_value);
                    self.scc_events.push(SccEvent::OpenUse {
                        target,
                        target_root,
                        use_value,
                    });
                }
                SccEvent::QuantifyComponent { component, roots } => {
                    self.quantify_component(&component, &roots);
                    self.scc_events
                        .push(SccEvent::QuantifyComponent { component, roots });
                }
                SccEvent::InstantiateUse { target, use_value } => {
                    self.instantiate_use(target, use_value);
                    self.scc_events
                        .push(SccEvent::InstantiateUse { target, use_value });
                }
                other => self.scc_events.push(other),
            }
        }
    }

    fn constrain_open_use(&mut self, target_root: TypeVar, use_value: TypeVar) {
        let target_pos = self.infer.alloc_pos(Pos::Var(target_root));
        let use_neg = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(target_pos, use_neg);
    }

    fn quantify_component(&mut self, component: &[DefId], roots: &[TypeVar]) {
        let generalized = component
            .iter()
            .copied()
            .zip(roots.iter().copied())
            .map(|(def, root)| {
                (
                    def,
                    generalize_type_var(
                        self.infer.constraints(),
                        root,
                        crate::constraints::TypeLevel::root(),
                        &FxHashSet::default(),
                    ),
                )
            })
            .collect::<Vec<_>>();

        for (def, scheme) in &generalized {
            self.schemes.insert(*def, scheme.clone());
        }

        for (def, scheme) in generalized {
            let ancestors = self.scheme_ancestors(def);
            let ancestors = ancestors.iter().collect::<Vec<_>>();
            let finalized = finalize_generalized_compact_root_with_ancestors(
                &mut self.poly.typ,
                &scheme,
                &ancestors,
            );
            self.set_def_scheme(def, finalized.scheme);
        }
    }

    fn instantiate_use(&mut self, target: DefId, use_value: TypeVar) {
        let Some(scheme) = self.def_scheme(target).cloned() else {
            return;
        };
        let use_level = self.infer.constraints().level_of(use_value);
        let predicate = instantiate_scheme(&self.poly.typ, &mut self.infer, use_level, &scheme);
        let use_upper = self.infer.alloc_neg(Neg::Var(use_value));
        self.infer.subtype(predicate, use_upper);
    }

    fn def_scheme(&self, def: DefId) -> Option<&Scheme> {
        let Some(Def::Let { scheme, .. }) = self.poly.defs.get(def) else {
            return None;
        };
        scheme.as_ref()
    }

    fn scheme_ancestors(&self, def: DefId) -> Vec<GeneralizedCompactRoot> {
        let parents = def_parent_map(&self.poly);
        let mut chain = Vec::new();
        let mut current = def;
        while let Some(parent) = parents.get(&current).copied() {
            chain.push(parent);
            current = parent;
        }
        chain.reverse();
        chain
            .into_iter()
            .filter_map(|ancestor| self.schemes.get(&ancestor).cloned())
            .collect()
    }

    fn set_def_scheme(&mut self, def: DefId, scheme: poly::types::Scheme) {
        let Some(Def::Let { scheme: target, .. }) = self.poly.defs.get_mut(def) else {
            return;
        };
        *target = Some(scheme);
    }
}

fn def_parent_map(poly: &PolyArena) -> FxHashMap<DefId, DefId> {
    let mut parents = FxHashMap::default();
    for (parent, def) in poly.defs.iter() {
        match def {
            Def::Mod { children, .. } | Def::Let { children, .. } => {
                for child in children {
                    parents.insert(*child, parent);
                }
            }
            Def::Arg => {}
        }
    }
    parents
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// `AnalysisSession` の work queue に積む作業。
///
/// `ResolveRef` / `ProbeSelect` は実際の解決器がまだ入る前の hook。
/// `Apply*Resolution` は解決結果が分かったあと、`poly` と SCC へ反映する段階。
/// `Scc` は lowering / resolver から SCC machine へ直接渡したい入力を queue に載せるための variant。
pub enum AnalysisWork {
    ResolveRef(RefId),
    ProbeSelect(SelectId),
    ApplyRefResolution {
        ref_id: RefId,
        target: DefId,
    },
    ApplySelectionResolution {
        select_id: SelectId,
        target: SelectionTarget,
    },
    Scc(SccInput),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// selection が何として解けたか。
///
/// `RecordField` は値の projection だけなので SCC edge を作らない。
/// `Method` / `TypeclassMethod` は hidden use なので、method def を parent def からの依存として SCC に渡す。
pub enum SelectionTarget {
    RecordField,
    Method { def: DefId },
    TypeclassMethod { member: DefId },
}

impl SelectionTarget {
    pub fn resolution(self) -> SelectResolution {
        match self {
            Self::RecordField => SelectResolution::RecordField,
            Self::Method { def } => SelectResolution::Method { def },
            Self::TypeclassMethod { member } => SelectResolution::TypeclassMethod { member },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::{ConstraintWeight, ConstraintWeights};
    use crate::uses::{RefUse, SelectionUse};
    use poly::expr::{Arena as PolyArena, Expr, Lit, Vis};
    use poly::types::{Neg, Pos, SubtractId, TypeVar};

    #[test]
    fn lower_bound_events_route_receiver_and_ref_payload_select_watchers() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let receiver_select = SelectId(0);
        let payload_select = SelectId(1);
        let watched = TypeVar(2);
        session.selections.watch_receiver(watched, receiver_select);
        session
            .selections
            .watch_ref_payload(watched, payload_select);

        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["ref".into()], vec![]));
        let upper = session.infer.alloc_neg(Neg::Var(watched));
        session.infer.weighted_subtype(
            lower,
            ConstraintWeights {
                left: ConstraintWeight::from_ids([SubtractId(0)]),
                right: ConstraintWeight::empty(),
            },
            upper,
        );
        session.route_constraint_events();

        assert_eq!(
            session.work().iter().cloned().collect::<Vec<_>>(),
            vec![
                AnalysisWork::ProbeSelect(receiver_select),
                AnalysisWork::ProbeSelect(payload_select)
            ]
        );
    }

    #[test]
    fn ref_resolution_routes_parent_and_use_value_to_scc_machine() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let reference = session.poly.add_ref();
        let parent = DefId(1);
        let target = DefId(2);
        session.refs.insert(
            reference,
            RefUse {
                parent,
                value: TypeVar(3),
            },
        );

        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });
        session.drain_work();

        assert_eq!(session.poly.ref_target(reference), Some(target));
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![parent],
                to: vec![target]
            }]
        );
    }

    #[test]
    fn method_selection_resolution_routes_hidden_method_use_to_scc_machine() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let receiver = session.poly.add_expr(Expr::Lit(Lit::Unit));
        let select = session.poly.add_select("display");
        session.poly.add_expr(Expr::Select(receiver, select));
        let parent = DefId(1);
        let method = DefId(2);
        session.selections.insert(
            select,
            SelectionUse {
                parent,
                receiver_value: TypeVar(3),
                method_value: TypeVar(4),
            },
        );

        session.enqueue(AnalysisWork::ApplySelectionResolution {
            select_id: select,
            target: SelectionTarget::Method { def: method },
        });
        session.drain_work();

        assert_eq!(
            session.poly.select(select).resolution,
            Some(SelectResolution::Method { def: method })
        );
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![parent],
                to: vec![method]
            }]
        );
    }

    #[test]
    fn open_scc_use_adds_target_to_use_constraint() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let a = DefId(1);
        let b = DefId(2);
        let a_root = TypeVar(10);
        let b_root = TypeVar(20);
        let a_to_b_use = TypeVar(12);
        let b_to_a_use = TypeVar(21);
        let a_to_b_ref = session.poly.add_ref();
        let b_to_a_ref = session.poly.add_ref();
        session.refs.insert(
            a_to_b_ref,
            RefUse {
                parent: a,
                value: a_to_b_use,
            },
        );
        session.refs.insert(
            b_to_a_ref,
            RefUse {
                parent: b,
                value: b_to_a_use,
            },
        );

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: a,
            root: a_root,
        }));
        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
            def: b,
            root: b_root,
        }));
        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: a_to_b_ref,
            target: b,
        });
        session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: b_to_a_ref,
            target: a,
        });
        session.drain_work();

        let b_root_pos = session.infer.alloc_pos(Pos::Var(b_root));
        let a_to_b_neg = session.infer.alloc_neg(Neg::Var(a_to_b_use));
        let bounds = session.infer.constraints().bounds();
        let use_bounds = bounds.of(a_to_b_use).expect("use bounds");
        assert!(use_bounds.lowers().iter().any(|bound| bound.pos == b_root_pos
            && bound.weights == ConstraintWeights::empty()));
        let target_bounds = bounds.of(b_root).expect("target root bounds");
        assert!(target_bounds.uppers().iter().any(|bound| bound.neg == a_to_b_neg
            && bound.weights == ConstraintWeights::empty()));

        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value,
                } if *target == b && *target_root == b_root && *use_value == a_to_b_use
            )
        }));
    }

    #[test]
    fn quantify_component_writes_scheme_to_poly_def() {
        let mut poly = PolyArena::new();
        let def = poly.defs.fresh();
        poly.defs.set(
            def,
            Def::Let {
                vis: Vis::My,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        let mut session = AnalysisSession::new(poly);
        let root = session.infer.fresh_type_var();

        session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));
        session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
        session.drain_work();

        let Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) = session.poly.defs.get(def)
        else {
            panic!("ready SCC should write a scheme to Def::Let");
        };
        assert_eq!(scheme.quantifiers, Vec::new());
        assert!(session.schemes.contains_key(&def));
        assert!(session.take_scc_events().iter().any(|event| {
            matches!(
                event,
                SccEvent::QuantifyComponent {
                    component,
                    roots,
                } if component == &vec![def] && roots == &vec![root]
            )
        }));
    }
}
