use super::*;
use crate::compact::compact_type_var;

/// Read-only inventory of the analysis queue at a Stage 0 lowering cutoff.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Stage0PendingWorkInventory {
    pub(crate) constraint_events: usize,
    pub(crate) unresolved_selections: usize,
    pub(crate) resolve_refs: usize,
    pub(crate) apply_refs: usize,
    pub(crate) probe_selects: usize,
    pub(crate) apply_selections: usize,
    pub(crate) register_defs: usize,
    pub(crate) def_fetches: usize,
    pub(crate) def_finishes: usize,
    pub(crate) uses: usize,
    pub(crate) dependencies: usize,
    pub(crate) method_dependencies_added: usize,
    pub(crate) method_dependencies_resolved: usize,
    pub(crate) conformance_pending: usize,
    pub(crate) conformance_released: usize,
}

/// Test-only trace of the bounded work that can run while every `DefFinished` stays deferred.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Stage0RoutedWorkTrace {
    pub(crate) elapsed: Duration,
    pub(crate) rounds: usize,
    pub(crate) routed_items: usize,
    pub(crate) open_uses: usize,
    pub(crate) instantiated_uses: usize,
    pub(crate) quantified_components: usize,
    pub(crate) before: Stage0PendingWorkInventory,
    pub(crate) after: Stage0PendingWorkInventory,
}

/// Read-only snapshot taken after an SCC becomes ready but before its first root generalizes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Stage0QuantifyEvent {
    pub(crate) def: DefId,
    pub(crate) component: Vec<DefId>,
    pub(crate) quantified_components_before: usize,
    pub(crate) root: CompactRoot,
    pub(crate) roles: Vec<CompactRoleConstraint>,
}

impl AnalysisSession {
    pub(crate) fn stage0_watch_quantify_def(&mut self, def: DefId) {
        self.stage0_quantify_watch.insert(def);
    }

    pub(crate) fn stage0_take_quantify_events(&mut self) -> Vec<Stage0QuantifyEvent> {
        std::mem::take(&mut self.stage0_quantify_events)
    }

    pub(super) fn stage0_capture_quantify_component(
        &mut self,
        component: &[DefId],
        roots: &[TypeVar],
    ) {
        for (def, root) in component.iter().copied().zip(roots.iter().copied()) {
            if !self.stage0_quantify_watch.contains(&def) {
                continue;
            }
            let root = compact_type_var(self.infer.constraints(), root);
            let roles = self
                .roles
                .for_owner(def)
                .iter()
                .map(|role| compact_role_constraint(self.infer.constraints(), role))
                .collect();
            self.stage0_quantify_events.push(Stage0QuantifyEvent {
                def,
                component: component.to_vec(),
                quantified_components_before: self.timing.quantified_components,
                root,
                roles,
            });
        }
    }

    pub(crate) fn stage0_pending_work_inventory(&self) -> Stage0PendingWorkInventory {
        let mut out = Stage0PendingWorkInventory {
            constraint_events: self.infer.constraints().events().len(),
            unresolved_selections: self.selections.unresolved().count(),
            ..Stage0PendingWorkInventory::default()
        };
        for work in &self.work {
            match work {
                AnalysisWork::ResolveRef(_) => out.resolve_refs += 1,
                AnalysisWork::ApplyRefResolution { .. } => out.apply_refs += 1,
                AnalysisWork::ProbeSelect(_) => out.probe_selects += 1,
                AnalysisWork::ApplySelectionResolution { .. } => out.apply_selections += 1,
                AnalysisWork::Scc(input) => match input {
                    SccInput::RegisterDef { .. } => out.register_defs += 1,
                    SccInput::DefFetchRecorded { .. } => out.def_fetches += 1,
                    SccInput::DefFinished { .. } => out.def_finishes += 1,
                    SccInput::UseResolved { .. } => out.uses += 1,
                    SccInput::DependencyAdded { .. } => out.dependencies += 1,
                    SccInput::MethodDependencyAdded { .. } => out.method_dependencies_added += 1,
                    SccInput::MethodDependencyResolved { .. } => {
                        out.method_dependencies_resolved += 1
                    }
                    SccInput::ConformancePending { .. } => out.conformance_pending += 1,
                    SccInput::ConformanceReleased { .. } => out.conformance_released += 1,
                },
            }
        }
        out
    }

    /// Route constraint/reference/SCC attachment work without allowing a component to finish.
    ///
    /// This is characterization-only. It deliberately retains every `DefFinished` item, never
    /// invokes the method-role pass, and asserts that ordinary SCC quantification did not begin.
    pub(crate) fn stage0_route_non_quantifying_work(&mut self) -> Stage0RoutedWorkTrace {
        const MAX_ROUTED_ITEMS: usize = 2_000_000;

        let before = self.stage0_pending_work_inventory();
        let timing_before = self.timing();
        let start = Instant::now();
        let mut rounds = 0usize;
        let mut routed_items = 0usize;

        loop {
            rounds += 1;
            let had_constraint_events = !self.infer.constraints().events().is_empty();
            self.route_constraint_events();

            let pending = self.work.len();
            let mut progressed = false;
            for _ in 0..pending {
                let Some(work) = self.work.pop_front() else {
                    break;
                };
                if matches!(work, AnalysisWork::Scc(SccInput::DefFinished { .. })) {
                    self.work.push_back(work);
                    continue;
                }

                self.apply_work(work);
                self.route_scc_events();
                progressed = true;
                routed_items += 1;
                assert!(
                    routed_items <= MAX_ROUTED_ITEMS,
                    "Stage 0 non-quantifying route exceeded its characterization bound"
                );
            }

            if !progressed && !had_constraint_events {
                break;
            }
        }

        let elapsed = start.elapsed();
        let timing_after = self.timing();
        let quantified_components = timing_after
            .quantified_components
            .saturating_sub(timing_before.quantified_components);
        assert_eq!(
            quantified_components, 0,
            "Stage 0 routed work must stop before component quantification"
        );

        Stage0RoutedWorkTrace {
            elapsed,
            rounds,
            routed_items,
            open_uses: timing_after
                .scc_open_use_events
                .saturating_sub(timing_before.scc_open_use_events),
            instantiated_uses: timing_after
                .scc_instantiate_events
                .saturating_sub(timing_before.scc_instantiate_events),
            quantified_components,
            before,
            after: self.stage0_pending_work_inventory(),
        }
    }
}
