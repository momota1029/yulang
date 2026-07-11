use super::*;

/// Pre-canonical unit boundary captured from settled inference state.
///
/// This is the Stage 2 handoff between ownership discovery/bound capture and the later joint
/// compact simplification. Raw `TypeVar` order is only a stable worklist order here; it is not the
/// serialized canonical order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CapturedBoundaryInterface {
    pub(crate) bounds: Vec<CapturedBoundaryBound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CapturedBoundaryBound {
    pub(crate) var: TypeVar,
    pub(crate) bounds: CompactBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BoundaryCaptureError {
    MissingGeneralizedScheme {
        def: DefId,
    },
    ConflictingBinderClass {
        var: TypeVar,
    },
    BoundaryDependsOnLocalBinder {
        boundary: TypeVar,
        local: TypeVar,
    },
    UnclassifiedBoundaryDependency {
        boundary: TypeVar,
        dependency: TypeVar,
    },
    FreezeProducedConstraint {
        def: Option<DefId>,
        boundary: Option<TypeVar>,
        merge_constraints: usize,
        subtype_constraints: usize,
    },
}

impl AnalysisSession {
    /// Discover and capture the unit-owned `B` closure for already-generalized definitions.
    ///
    /// The traversal is finite: each boundary variable is captured at most once. It never adds a
    /// constraint or restarts generalization. Structural constraints rediscovered from the final
    /// scheme view or while compacting a bound must already be present in the normal
    /// generalization lanes, otherwise capture fails.
    pub(crate) fn capture_cache_boundary_interface(
        &self,
        defs: impl IntoIterator<Item = DefId>,
    ) -> Result<CapturedBoundaryInterface, BoundaryCaptureError> {
        let mut defs = defs.into_iter().collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        defs.dedup();

        let mut local_binders = FxHashSet::default();
        let mut seed_boundaries = FxHashMap::default();
        for def in defs {
            let root = self
                .schemes
                .get(&def)
                .ok_or(BoundaryCaptureError::MissingGeneralizedScheme { def })?;
            let generated = collect_interval_dominance_constraints_with_metrics(
                &root.compact,
                &root.role_predicates,
            )
            .0;
            let unapplied = unapplied_compact_subtype_constraint_count(
                &generated,
                &self.cache_interface_applied_subtype_constraints,
            );
            if unapplied != 0 {
                return Err(BoundaryCaptureError::FreezeProducedConstraint {
                    def: Some(def),
                    boundary: None,
                    merge_constraints: 0,
                    subtype_constraints: unapplied,
                });
            }

            local_binders.extend(root.quantifiers.iter().copied());
            local_binders.extend(root.compact.rec_vars.iter().map(|rec| rec.var));
            let boundary = self.generalize_boundary(def);
            for var in generalized_compact_boundary_vars(root) {
                seed_boundaries
                    .entry(var)
                    .and_modify(|current: &mut TypeLevel| *current = (*current).max(boundary))
                    .or_insert(boundary);
            }
        }

        if let Some(var) = seed_boundaries
            .keys()
            .copied()
            .find(|var| local_binders.contains(var))
        {
            return Err(BoundaryCaptureError::ConflictingBinderClass { var });
        }

        let seed_vars = seed_boundaries.keys().copied().collect::<FxHashSet<_>>();
        let mut ownership = seed_boundaries;
        let mut pending = ownership.keys().copied().collect::<Vec<_>>();
        pending.sort_by_key(|var| var.0);
        let mut pending = pending.into_iter().collect::<VecDeque<_>>();
        let mut prefrozen = FxHashMap::<TypeVar, CompactBounds>::default();
        let mut visited = FxHashSet::default();
        let mut bounds = Vec::new();

        while let Some(var) = pending.pop_front() {
            if !visited.insert(var) {
                continue;
            }
            let owner_boundary = ownership[&var];
            let (bound, mut dependencies) = if let Some(bound) = prefrozen.remove(&var) {
                (bound, Vec::new())
            } else {
                let (capture, merge_constraints) =
                    crate::compact::compact_type_var_boundary_bounds_recording_merge_constraints(
                        self.infer.constraints(),
                        var,
                    );
                let unapplied = unapplied_compact_merge_constraint_count(
                    &merge_constraints,
                    &self.cache_interface_applied_merge_constraints,
                );
                if unapplied != 0 {
                    return Err(BoundaryCaptureError::FreezeProducedConstraint {
                        def: None,
                        boundary: Some(var),
                        merge_constraints: unapplied,
                        subtype_constraints: 0,
                    });
                }
                let mut dependencies = Vec::new();
                for recursive in capture.recursive {
                    dependencies.push(recursive.var);
                    dependencies.extend(compact_boundary_bound_vars(&recursive.bounds));
                    if recursive.var != var {
                        prefrozen.entry(recursive.var).or_insert(recursive.bounds);
                    }
                }
                (capture.bounds, dependencies)
            };

            dependencies.extend(compact_boundary_bound_vars(&bound));
            dependencies.sort_by_key(|dependency| dependency.0);
            dependencies.dedup();
            for dependency in dependencies {
                if dependency == var || ownership.contains_key(&dependency) {
                    continue;
                }
                if local_binders.contains(&dependency) {
                    return Err(BoundaryCaptureError::BoundaryDependsOnLocalBinder {
                        boundary: var,
                        local: dependency,
                    });
                }
                if !seed_vars.contains(&dependency)
                    && self.infer.constraints().level_of(dependency) > owner_boundary
                {
                    return Err(BoundaryCaptureError::UnclassifiedBoundaryDependency {
                        boundary: var,
                        dependency,
                    });
                }
                ownership.insert(dependency, owner_boundary);
                pending.push_back(dependency);
            }
            bounds.push(CapturedBoundaryBound { var, bounds: bound });
        }

        bounds.sort_by_key(|bound| bound.var.0);
        Ok(CapturedBoundaryInterface { bounds })
    }
}
