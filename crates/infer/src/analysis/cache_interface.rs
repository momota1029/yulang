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

/// Pre-normalization candidate components classified against the captured unit boundary.
///
/// Each candidate remains intact so the next Stage 4 slice can compact its head and prerequisites
/// together. This capture only establishes binder ownership; it does not resolve roles, simplify a
/// candidate, or assign a meaning to prerequisite-only variables.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CapturedCandidateInterface {
    pub(crate) candidates: Vec<CapturedCandidate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CapturedCandidate {
    pub(crate) candidate: crate::roles::RoleImplCandidate,
    pub(crate) head_binders: Vec<TypeVar>,
    pub(crate) boundary: Vec<TypeVar>,
    pub(crate) prerequisite_only: Vec<TypeVar>,
}

/// One-pass normalized candidate components awaiting structural freeze and canonical ordering.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NormalizedCandidateInterface {
    pub(crate) candidates: Vec<NormalizedCandidate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NormalizedCandidate {
    pub(crate) candidate: crate::roles::RoleImplCandidate,
    pub(crate) head: CompactRoleConstraint,
    pub(crate) prerequisites: Vec<CompactRoleConstraint>,
    pub(crate) head_binders: Vec<TypeVar>,
    pub(crate) boundary: Vec<TypeVar>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CanonicalCacheInterfaceDraft {
    pub(crate) schemes: Vec<CanonicalSchemeDraft>,
    pub(crate) boundary: CapturedBoundaryInterface,
    pub(crate) binders: CanonicalBinderClasses,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalSchemeDraft {
    pub(crate) def: DefId,
    pub(crate) generalized: GeneralizedCompactRoot,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CanonicalBinderClasses {
    pub(crate) schemes: Vec<CanonicalSchemeBinders>,
    pub(crate) boundary: Vec<TypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalSchemeBinders {
    pub(crate) def: DefId,
    pub(crate) quantified: Vec<TypeVar>,
    pub(crate) recursive: Vec<TypeVar>,
}

struct FrozenCanonicalScheme {
    def: DefId,
    scheme: Scheme,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BoundaryCaptureError {
    MissingGeneralizedScheme {
        def: DefId,
    },
    MissingPolySchemeTarget {
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
    MalformedJointComponent,
    UnboundSchemeVariable {
        def: DefId,
        var: TypeVar,
    },
    UnboundCandidateVariable {
        impl_def: Option<DefId>,
        role: Vec<String>,
        var: TypeVar,
    },
    MissingBoundaryBound {
        var: TypeVar,
    },
    ConflictingBoundaryBound {
        var: TypeVar,
    },
}

impl CanonicalCacheInterfaceDraft {
    /// Structurally freeze this validated draft into one poly arena.
    ///
    /// Taking the draft by value makes this the single handoff point: typed and runtime surfaces
    /// must share the resulting arena instead of independently finalizing compact graphs. All
    /// target definitions are checked before the arena or its schemes are changed.
    pub(crate) fn freeze_into_poly(
        self,
        machine: &crate::constraints::ConstraintMachine,
        poly: &mut PolyArena,
    ) -> Result<crate::CompiledBoundaryInterface, BoundaryCaptureError> {
        for draft in &self.schemes {
            if !matches!(
                poly.defs.get(draft.def),
                Some(Def::Let {
                    scheme: Some(_),
                    ..
                })
            ) {
                return Err(BoundaryCaptureError::MissingPolySchemeTarget { def: draft.def });
            }
        }

        let schemes = self
            .schemes
            .iter()
            .map(|draft| FrozenCanonicalScheme {
                def: draft.def,
                scheme: crate::generalize::finalize_generalized_compact_root(
                    &mut poly.typ,
                    machine,
                    &draft.generalized,
                )
                .scheme,
            })
            .collect::<Vec<_>>();
        let boundary = crate::CompiledBoundaryInterface {
            bounds: self
                .boundary
                .bounds
                .iter()
                .map(|bound| crate::CompiledBoundaryBound {
                    var: bound.var,
                    bounds: finalize_compact_boundary_bounds(&mut poly.typ, machine, &bound.bounds),
                })
                .collect(),
        };

        for frozen in schemes {
            let Some(Def::Let { scheme, .. }) = poly.defs.get_mut(frozen.def) else {
                unreachable!("cache-interface scheme targets were validated before freeze")
            };
            *scheme = Some(frozen.scheme);
        }
        Ok(boundary)
    }
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

    /// Classify candidate head binders and known `B` occurrences before joint normalization.
    ///
    /// Variables occurring only in prerequisites remain explicitly unclassified. Their binder
    /// interpretation is not inferred from convenience, and no candidate search is run here. The
    /// later joint-normalization slice must reject only those that survive normal simplification.
    pub(crate) fn capture_cache_candidate_interface(
        &self,
        boundary: &CapturedBoundaryInterface,
    ) -> CapturedCandidateInterface {
        let boundary_binders = boundary
            .bounds
            .iter()
            .map(|bound| bound.var)
            .collect::<FxHashSet<_>>();
        let types = self.infer.constraints().types();
        let mut captured = Vec::new();

        for candidate in self.role_impls.iter() {
            let head = candidate.as_constraint().raw_vars(types);
            let mut all = head.clone();
            for prerequisite in &candidate.prerequisites {
                all.extend(prerequisite.raw_vars(types));
            }

            let mut head_binders = head
                .difference(&boundary_binders)
                .copied()
                .collect::<Vec<_>>();
            let mut candidate_boundary = all
                .intersection(&boundary_binders)
                .copied()
                .collect::<Vec<_>>();
            let closed = head
                .union(&boundary_binders)
                .copied()
                .collect::<FxHashSet<_>>();
            let mut prerequisite_only = all.difference(&closed).copied().collect::<Vec<_>>();

            head_binders.sort_by_key(|var| var.0);
            candidate_boundary.sort_by_key(|var| var.0);
            prerequisite_only.sort_by_key(|var| var.0);
            captured.push(CapturedCandidate {
                candidate: candidate.clone(),
                head_binders,
                boundary: candidate_boundary,
                prerequisite_only,
            });
        }

        captured.sort_by(|left, right| {
            left.candidate
                .role
                .cmp(&right.candidate.role)
                .then_with(|| {
                    left.candidate
                        .impl_def
                        .map(|def| def.0)
                        .cmp(&right.candidate.impl_def.map(|def| def.0))
                })
                .then_with(|| {
                    left.head_binders
                        .iter()
                        .map(|var| var.0)
                        .cmp(right.head_binders.iter().map(|var| var.0))
                })
                .then_with(|| {
                    left.boundary
                        .iter()
                        .map(|var| var.0)
                        .cmp(right.boundary.iter().map(|var| var.0))
                })
                .then_with(|| {
                    left.prerequisite_only
                        .iter()
                        .map(|var| var.0)
                        .cmp(right.prerequisite_only.iter().map(|var| var.0))
                })
        });
        CapturedCandidateInterface {
            candidates: captured,
        }
    }

    /// Normalize each captured candidate as one connected head/prerequisite/`B` component.
    ///
    /// This is one structural pass per candidate. It does not resolve candidates or recursively
    /// discharge prerequisites, and it never retries after simplification.
    pub(crate) fn normalize_cache_candidate_interface(
        &self,
        captured: CapturedCandidateInterface,
        boundary: &CapturedBoundaryInterface,
    ) -> Result<NormalizedCandidateInterface, BoundaryCaptureError> {
        let mut candidates = Vec::with_capacity(captured.candidates.len());
        for candidate in captured.candidates {
            candidates.push(normalize_cache_candidate(self, candidate, boundary)?);
        }
        Ok(NormalizedCandidateInterface { candidates })
    }

    /// Apply the normal structural simplification once to schemes and their captured boundary.
    pub(crate) fn freeze_cache_interface(
        &self,
        defs: impl IntoIterator<Item = DefId>,
    ) -> Result<CanonicalCacheInterfaceDraft, BoundaryCaptureError> {
        let mut defs = defs.into_iter().collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        defs.dedup();
        let boundary = self.capture_cache_boundary_interface(defs.iter().copied())?;
        let schemes = defs
            .into_iter()
            .map(|def| {
                self.schemes
                    .get(&def)
                    .cloned()
                    .map(|generalized| CanonicalSchemeDraft { def, generalized })
                    .ok_or(BoundaryCaptureError::MissingGeneralizedScheme { def })
            })
            .collect::<Result<Vec<_>, _>>()?;

        freeze_joint_cache_interface(self, schemes, boundary)
    }
}

fn normalize_cache_candidate(
    session: &AnalysisSession,
    captured: CapturedCandidate,
    boundary: &CapturedBoundaryInterface,
) -> Result<NormalizedCandidate, BoundaryCaptureError> {
    let mut merge_constraints = Vec::new();
    let (head, head_merges) = compact_role_constraint_recording_merge_constraints(
        session.infer.constraints(),
        &captured.candidate.as_constraint(),
    );
    merge_constraints.extend(head_merges);
    let mut prerequisites = Vec::with_capacity(captured.candidate.prerequisites.len());
    for prerequisite in &captured.candidate.prerequisites {
        let (prerequisite, prerequisite_merges) =
            compact_role_constraint_recording_merge_constraints(
                session.infer.constraints(),
                prerequisite,
            );
        prerequisites.push(prerequisite);
        merge_constraints.extend(prerequisite_merges);
    }
    let unapplied = unapplied_compact_merge_constraint_count(
        &merge_constraints,
        &session.cache_interface_applied_merge_constraints,
    );
    if unapplied != 0 {
        return Err(BoundaryCaptureError::FreezeProducedConstraint {
            def: captured.candidate.impl_def,
            boundary: None,
            merge_constraints: unapplied,
            subtype_constraints: 0,
        });
    }

    let candidate_boundary = reachable_candidate_boundary(&captured.boundary, boundary)?;
    // Unlike a scheme component, a candidate has no main value root to place in a synthetic tuple.
    // Keeping head, prerequisites, and bound carriers in one role slice gives the existing
    // occurrence/sandwich passes the same joint component while the root remains structurally empty.
    let mut roles = Vec::with_capacity(1 + prerequisites.len() + candidate_boundary.len());
    roles.push(head);
    roles.extend(prerequisites);
    let real_role_count = roles.len();
    roles.extend(candidate_boundary.iter().map(boundary_bound_carrier));
    let boundary_baseline = collect_interval_dominance_constraints_with_metrics(
        &CompactRoot::default(),
        &roles[real_role_count..],
    )
    .0;
    let boundary_baseline = compact_subtype_constraint_keys(&boundary_baseline);

    let mut root = CompactRoot::default();
    let mut substitutions = coalesce_floor_interval_equalities(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut root,
        &mut roles,
    );
    substitutions.extend(coalesce_floor_variable_sandwiches(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut root,
        &mut roles,
    ));
    substitutions.extend(eliminate_floor_redundant_variables(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut root,
        &mut roles,
    ));
    let simplification = simplify_compact_root_with_roles_and_non_generic(
        session.infer.constraints(),
        TypeLevel::root().child(),
        &mut root,
        &mut roles,
        &FxHashSet::default(),
    );
    substitutions.extend(simplification.substitutions.iter().copied());
    let substitutions = normalize_var_substitutions(substitutions);
    let substitution_map = substitutions
        .iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect::<FxHashMap<_, _>>();

    let generated = collect_interval_dominance_constraints_with_metrics(&root, &roles).0;
    let unapplied = unapplied_compact_subtype_constraint_count_with_known(
        &generated,
        &session.cache_interface_applied_subtype_constraints,
        &boundary_baseline,
    );
    if unapplied != 0 {
        return Err(BoundaryCaptureError::FreezeProducedConstraint {
            def: captured.candidate.impl_def,
            boundary: None,
            merge_constraints: 0,
            subtype_constraints: unapplied,
        });
    }

    let mut roles = roles.into_iter();
    let head = roles
        .next()
        .ok_or(BoundaryCaptureError::MalformedJointComponent)?;
    let prerequisites = roles
        .by_ref()
        .take(captured.candidate.prerequisites.len())
        .collect::<Vec<_>>();
    if prerequisites.len() != captured.candidate.prerequisites.len()
        || roles.count() != candidate_boundary.len()
    {
        return Err(BoundaryCaptureError::MalformedJointComponent);
    }

    let known_boundary = rewrite_binders(
        &boundary
            .bounds
            .iter()
            .map(|bound| bound.var)
            .collect::<Vec<_>>(),
        &substitution_map,
    )
    .into_iter()
    .collect::<FxHashSet<_>>();
    let head_vars = compact_role_constraint_vars(&head);
    let prerequisite_vars = prerequisites
        .iter()
        .flat_map(compact_role_constraint_vars)
        .collect::<FxHashSet<_>>();
    let closed = head_vars
        .union(&known_boundary)
        .copied()
        .collect::<FxHashSet<_>>();
    let mut unbound = prerequisite_vars
        .difference(&closed)
        .copied()
        .collect::<Vec<_>>();
    unbound.sort_by_key(|var| var.0);
    if let Some(var) = unbound.into_iter().next() {
        return Err(BoundaryCaptureError::UnboundCandidateVariable {
            impl_def: captured.candidate.impl_def,
            role: captured.candidate.role.clone(),
            var,
        });
    }

    let mut head_binders = head_vars
        .difference(&known_boundary)
        .copied()
        .collect::<Vec<_>>();
    let all_vars = head_vars
        .union(&prerequisite_vars)
        .copied()
        .collect::<FxHashSet<_>>();
    let mut candidate_boundary = all_vars
        .intersection(&known_boundary)
        .copied()
        .collect::<Vec<_>>();
    head_binders.sort_by_key(|var| var.0);
    candidate_boundary.sort_by_key(|var| var.0);

    Ok(NormalizedCandidate {
        candidate: captured.candidate,
        head,
        prerequisites,
        head_binders,
        boundary: candidate_boundary,
    })
}

fn reachable_candidate_boundary(
    roots: &[TypeVar],
    boundary: &CapturedBoundaryInterface,
) -> Result<Vec<CapturedBoundaryBound>, BoundaryCaptureError> {
    let bounds = boundary
        .bounds
        .iter()
        .map(|bound| (bound.var, bound))
        .collect::<FxHashMap<_, _>>();
    let mut pending = roots.iter().copied().collect::<VecDeque<_>>();
    let mut visited = FxHashSet::default();
    let mut reachable = Vec::new();
    while let Some(var) = pending.pop_front() {
        if !visited.insert(var) {
            continue;
        }
        let bound = bounds
            .get(&var)
            .copied()
            .ok_or(BoundaryCaptureError::MissingBoundaryBound { var })?;
        for dependency in compact_boundary_bound_vars(&bound.bounds) {
            if dependency != var {
                pending.push_back(dependency);
            }
        }
        reachable.push(bound.clone());
    }
    reachable.sort_by_key(|bound| bound.var.0);
    Ok(reachable)
}

fn compact_role_constraint_vars(role: &CompactRoleConstraint) -> FxHashSet<TypeVar> {
    role.inputs
        .iter()
        .map(|input| &input.bounds)
        .chain(
            role.associated
                .iter()
                .map(|associated| &associated.value.bounds),
        )
        .flat_map(compact_boundary_bound_vars)
        .collect()
}

fn freeze_joint_cache_interface(
    session: &AnalysisSession,
    mut schemes: Vec<CanonicalSchemeDraft>,
    boundary: CapturedBoundaryInterface,
) -> Result<CanonicalCacheInterfaceDraft, BoundaryCaptureError> {
    if schemes.is_empty() {
        return Ok(CanonicalCacheInterfaceDraft::default());
    }

    let original_quantifiers = schemes
        .iter()
        .map(|scheme| scheme.generalized.quantifiers.clone())
        .collect::<Vec<_>>();
    let original_recursive = schemes
        .iter()
        .map(|scheme| {
            scheme
                .generalized
                .compact
                .rec_vars
                .iter()
                .map(|rec| rec.var)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let role_counts = schemes
        .iter()
        .map(|scheme| scheme.generalized.role_predicates.len())
        .collect::<Vec<_>>();
    let roots = schemes
        .iter()
        .map(|scheme| scheme.generalized.compact.root.clone())
        .collect::<Vec<_>>();
    let recursive = schemes
        .iter()
        .flat_map(|scheme| scheme.generalized.compact.rec_vars.iter().cloned())
        .collect::<Vec<_>>();
    let mut roles = schemes
        .iter()
        .flat_map(|scheme| scheme.generalized.role_predicates.iter().cloned())
        .collect::<Vec<_>>();
    let real_role_count = roles.len();
    roles.extend(boundary.bounds.iter().map(boundary_bound_carrier));

    let boundary_baseline = collect_interval_dominance_constraints_with_metrics(
        &CompactRoot::default(),
        &roles[real_role_count..],
    )
    .0;
    let boundary_baseline = compact_subtype_constraint_keys(&boundary_baseline);

    let mut joint = CompactRoot {
        root: CompactType::from_tuple(crate::compact::CompactTuple { items: roots }),
        rec_vars: recursive,
    };
    let mut substitutions = coalesce_floor_interval_equalities(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut joint,
        &mut roles,
    );
    substitutions.extend(coalesce_floor_variable_sandwiches(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut joint,
        &mut roles,
    ));
    substitutions.extend(eliminate_floor_redundant_variables(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut joint,
        &mut roles,
    ));
    let simplification = simplify_compact_root_with_roles_and_non_generic(
        session.infer.constraints(),
        TypeLevel::root().child(),
        &mut joint,
        &mut roles,
        &FxHashSet::default(),
    );
    substitutions.extend(simplification.substitutions.iter().copied());
    let substitutions = normalize_var_substitutions(substitutions);
    let substitution_map = substitutions
        .iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect::<FxHashMap<_, _>>();

    let generated = collect_interval_dominance_constraints_with_metrics(&joint, &roles).0;
    let unapplied = unapplied_compact_subtype_constraint_count_with_known(
        &generated,
        &session.cache_interface_applied_subtype_constraints,
        &boundary_baseline,
    );
    if unapplied != 0 {
        return Err(BoundaryCaptureError::FreezeProducedConstraint {
            def: None,
            boundary: None,
            merge_constraints: 0,
            subtype_constraints: unapplied,
        });
    }

    let roots = take_joint_scheme_roots(&mut joint, schemes.len())?;
    let mut roles = roles.into_iter();
    for ((scheme, root), role_count) in schemes
        .iter_mut()
        .zip(roots)
        .zip(role_counts.iter().copied())
    {
        scheme.generalized.compact.root = root;
        scheme.generalized.role_predicates = roles.by_ref().take(role_count).collect();
        scheme.generalized.substitutions = normalize_var_substitutions(
            scheme
                .generalized
                .substitutions
                .iter()
                .copied()
                .chain(substitutions.iter().copied())
                .collect(),
        );
        scheme
            .generalized
            .sandwiches
            .extend(simplification.sandwiches.iter().cloned());
    }

    let boundary_roles = roles.collect::<Vec<_>>();
    if boundary_roles.len() != boundary.bounds.len() {
        return Err(BoundaryCaptureError::MalformedJointComponent);
    }

    let mut recursive_owners = FxHashMap::<TypeVar, DefId>::default();
    for (index, scheme) in schemes.iter_mut().enumerate() {
        scheme.generalized.quantifiers =
            rewrite_binders(&original_quantifiers[index], &substitution_map);
        for var in rewrite_binders(&original_recursive[index], &substitution_map) {
            if recursive_owners.insert(var, scheme.def).is_some() {
                return Err(BoundaryCaptureError::ConflictingBinderClass { var });
            }
        }
        scheme.generalized.compact.rec_vars.clear();
    }
    for rec in joint.rec_vars {
        let Some(owner) = recursive_owners.get(&rec.var).copied() else {
            continue;
        };
        let scheme = schemes
            .iter_mut()
            .find(|scheme| scheme.def == owner)
            .expect("recursive owner came from selected schemes");
        scheme.generalized.compact.rec_vars.push(rec);
    }
    for scheme in &mut schemes {
        prune_generalized_compact_root_for_cache(&mut scheme.generalized);
    }

    let mut simplified_boundary = Vec::new();
    for (captured, carrier) in boundary.bounds.into_iter().zip(boundary_roles) {
        let Some(var) = rewrite_binder(captured.var, &substitution_map) else {
            continue;
        };
        let [input] = carrier.inputs.as_slice() else {
            return Err(BoundaryCaptureError::MalformedJointComponent);
        };
        insert_boundary_bound(
            &mut simplified_boundary,
            CapturedBoundaryBound {
                var,
                bounds: input.bounds.clone(),
            },
        )?;
    }

    validate_and_prune_cache_interface(schemes, simplified_boundary)
}

fn boundary_bound_carrier(bound: &CapturedBoundaryBound) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: Vec::new(),
        inputs: vec![CompactRoleArg::invariant(bound.bounds.clone())],
        associated: Vec::new(),
    }
}

fn take_joint_scheme_roots(
    joint: &mut CompactRoot,
    expected: usize,
) -> Result<Vec<CompactType>, BoundaryCaptureError> {
    if !joint.root.vars.is_empty()
        || joint.root.never
        || !joint.root.builtins.is_empty()
        || !joint.root.cons.is_empty()
        || !joint.root.funs.is_empty()
        || !joint.root.records.is_empty()
        || !joint.root.record_spreads.is_empty()
        || !joint.root.poly_variants.is_empty()
        || !joint.root.rows.is_empty()
        || joint.root.tuples.len() != 1
    {
        return Err(BoundaryCaptureError::MalformedJointComponent);
    }
    let roots = joint.root.tuples.remove(0).items;
    (roots.len() == expected)
        .then_some(roots)
        .ok_or(BoundaryCaptureError::MalformedJointComponent)
}

fn rewrite_binders(
    vars: &[TypeVar],
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) -> Vec<TypeVar> {
    let mut vars = vars
        .iter()
        .filter_map(|var| rewrite_binder(*var, substitutions))
        .collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars
}

fn rewrite_binder(
    var: TypeVar,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) -> Option<TypeVar> {
    let mut current = var;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(current) {
            return Some(current);
        }
        match substitutions.get(&current).copied() {
            None => return Some(current),
            Some(None) => return None,
            Some(Some(next)) => current = next,
        }
    }
}

fn insert_boundary_bound(
    bounds: &mut Vec<CapturedBoundaryBound>,
    bound: CapturedBoundaryBound,
) -> Result<(), BoundaryCaptureError> {
    let Some(existing) = bounds.iter().find(|existing| existing.var == bound.var) else {
        bounds.push(bound);
        return Ok(());
    };
    if existing.bounds == bound.bounds {
        return Ok(());
    }
    Err(BoundaryCaptureError::ConflictingBoundaryBound { var: bound.var })
}

pub(super) fn validate_and_prune_cache_interface(
    mut schemes: Vec<CanonicalSchemeDraft>,
    boundary: Vec<CapturedBoundaryBound>,
) -> Result<CanonicalCacheInterfaceDraft, BoundaryCaptureError> {
    let mut boundary_map = FxHashMap::<TypeVar, CompactBounds>::default();
    for bound in boundary {
        if let Some(existing) = boundary_map.get(&bound.var) {
            if existing != &bound.bounds {
                return Err(BoundaryCaptureError::ConflictingBoundaryBound { var: bound.var });
            }
            continue;
        }
        boundary_map.insert(bound.var, bound.bounds);
    }
    let boundary_binders = boundary_map.keys().copied().collect::<FxHashSet<_>>();
    let mut local_binders = FxHashSet::default();
    let mut quantified_binders = FxHashSet::default();
    let mut recursive_binders = FxHashSet::default();
    let mut binder_schemes = Vec::new();
    let mut pending = VecDeque::new();

    for scheme in &mut schemes {
        let recursive = scheme
            .generalized
            .compact
            .rec_vars
            .iter()
            .map(|rec| rec.var)
            .collect::<FxHashSet<_>>();
        let quantified = scheme
            .generalized
            .quantifiers
            .iter()
            .copied()
            .filter(|var| !recursive.contains(var))
            .collect::<FxHashSet<_>>();
        if let Some(var) = quantified
            .iter()
            .chain(recursive.iter())
            .copied()
            .find(|var| boundary_binders.contains(var))
        {
            return Err(BoundaryCaptureError::ConflictingBinderClass { var });
        }
        if let Some(var) = quantified.intersection(&recursive_binders).copied().next() {
            return Err(BoundaryCaptureError::ConflictingBinderClass { var });
        }
        if let Some(var) = recursive.intersection(&quantified_binders).copied().next() {
            return Err(BoundaryCaptureError::ConflictingBinderClass { var });
        }
        quantified_binders.extend(quantified.iter().copied());
        recursive_binders.extend(recursive.iter().copied());
        local_binders.extend(quantified.iter().copied());
        local_binders.extend(recursive.iter().copied());

        for var in generalized_compact_boundary_vars(&scheme.generalized) {
            if !boundary_binders.contains(&var) {
                return Err(BoundaryCaptureError::UnboundSchemeVariable {
                    def: scheme.def,
                    var,
                });
            }
            pending.push_back(var);
        }
        let mut quantified = quantified.into_iter().collect::<Vec<_>>();
        quantified.sort_by_key(|var| var.0);
        let mut recursive = recursive.into_iter().collect::<Vec<_>>();
        recursive.sort_by_key(|var| var.0);
        binder_schemes.push(CanonicalSchemeBinders {
            def: scheme.def,
            quantified,
            recursive,
        });
    }

    let mut reachable = FxHashSet::default();
    while let Some(var) = pending.pop_front() {
        if !reachable.insert(var) {
            continue;
        }
        let bounds = boundary_map
            .get(&var)
            .ok_or(BoundaryCaptureError::MissingBoundaryBound { var })?;
        for dependency in compact_boundary_bound_vars(bounds) {
            if local_binders.contains(&dependency) {
                return Err(BoundaryCaptureError::BoundaryDependsOnLocalBinder {
                    boundary: var,
                    local: dependency,
                });
            }
            if !boundary_binders.contains(&dependency) {
                return Err(BoundaryCaptureError::MissingBoundaryBound { var: dependency });
            }
            pending.push_back(dependency);
        }
    }

    boundary_map.retain(|var, _| reachable.contains(var));
    let mut boundary = boundary_map
        .into_iter()
        .map(|(var, bounds)| CapturedBoundaryBound { var, bounds })
        .collect::<Vec<_>>();
    boundary.sort_by_key(|bound| bound.var.0);
    binder_schemes.sort_by_key(|scheme| scheme.def.0);
    schemes.sort_by_key(|scheme| scheme.def.0);
    Ok(CanonicalCacheInterfaceDraft {
        schemes,
        binders: CanonicalBinderClasses {
            schemes: binder_schemes,
            boundary: boundary.iter().map(|bound| bound.var).collect(),
        },
        boundary: CapturedBoundaryInterface { bounds: boundary },
    })
}
