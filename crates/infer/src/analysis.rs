//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

use std::collections::VecDeque;

use poly::expr::{Arena as PolyArena, DefId, RefId, SelectId, SelectResolution};

use crate::arena::Arena as InferArena;
use crate::constraints::ConstraintEvent;
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
        self.scc.take_events()
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
    }
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
    use poly::expr::{Arena as PolyArena, Expr, Lit};
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
}
