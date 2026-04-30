use std::collections::{HashMap, HashSet};
use std::time::Duration;

use crate::profile::ProfileClock as Instant;

use crate::ids::DefId;
use crate::ref_table::{RefTable, ResolvedRef};
use crate::scheme::{
    collect_compact_role_constraint_free_vars,
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars,
    instantiate_as_view_with_subst_profiled,
};
use crate::simplify::compact::{
    CompactBounds, CompactTypeScheme, compact_neg_expr, compact_pos_expr,
    compact_type_vars_in_order, compact_type_vars_in_order_profiled,
};
use crate::simplify::cooccur::{
    CompactRoleConstraint, coalesce_by_co_occurrence,
    coalesce_by_co_occurrence_with_role_constraints,
};
use crate::solve::Infer;

use super::ready_components;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CommitReadyProfile {
    pub total: Duration,
    pub ready_scan: Duration,
    pub compact: Duration,
    pub compact_var_side: Duration,
    pub compact_pos_ref: Duration,
    pub compact_neg_ref: Duration,
    pub compact_reachable_rec_vars: Duration,
    pub role_constraints: Duration,
    pub cooccur: Duration,
    pub freeze: Duration,
    pub instantiate: Duration,
    pub instantiate_build_subst: Duration,
    pub instantiate_subst_body: Duration,
    pub instantiate_constrain: Duration,
    pub instantiate_role_constraints: Duration,
    pub prune_edges: Duration,
    pub ready_components: usize,
    pub committed_components: usize,
    pub compacted_defs: usize,
    pub instantiated_refs: usize,
    pub instantiate_counts_by_def: HashMap<DefId, usize>,
}

impl CommitReadyProfile {
    pub fn merge(&mut self, other: &Self) {
        self.total += other.total;
        self.ready_scan += other.ready_scan;
        self.compact += other.compact;
        self.compact_var_side += other.compact_var_side;
        self.compact_pos_ref += other.compact_pos_ref;
        self.compact_neg_ref += other.compact_neg_ref;
        self.compact_reachable_rec_vars += other.compact_reachable_rec_vars;
        self.role_constraints += other.role_constraints;
        self.cooccur += other.cooccur;
        self.freeze += other.freeze;
        self.instantiate += other.instantiate;
        self.instantiate_build_subst += other.instantiate_build_subst;
        self.instantiate_subst_body += other.instantiate_subst_body;
        self.instantiate_constrain += other.instantiate_constrain;
        self.instantiate_role_constraints += other.instantiate_role_constraints;
        self.prune_edges += other.prune_edges;
        self.ready_components += other.ready_components;
        self.committed_components += other.committed_components;
        self.compacted_defs += other.compacted_defs;
        self.instantiated_refs += other.instantiated_refs;
        for (def, count) in &other.instantiate_counts_by_def {
            *self.instantiate_counts_by_def.entry(*def).or_default() += *count;
        }
    }
}

pub fn compact_ready_components(infer: &Infer) -> HashMap<usize, Vec<(DefId, CompactTypeScheme)>> {
    let mut out = HashMap::new();
    for component_idx in ready_components(infer) {
        let defs = infer.components[component_idx]
            .iter()
            .copied()
            .filter_map(|def| {
                let tv = infer.def_tvs.borrow().get(&def).copied()?;
                Some((def, tv))
            })
            .collect::<Vec<_>>();
        let roots = defs.iter().map(|(_, tv)| *tv).collect::<Vec<_>>();
        let schemes = compact_type_vars_in_order(infer, &roots)
            .into_iter()
            .zip(defs)
            .map(|(compact, (def, _))| (def, coalesce_by_co_occurrence(&compact)))
            .collect::<Vec<_>>();
        out.insert(component_idx, schemes);
    }
    out
}

pub fn commit_ready_components(infer: &Infer, refs: &RefTable) -> Vec<usize> {
    let refs_by_def = refs_by_def(refs);
    let target_defs = infer
        .components
        .iter()
        .flat_map(|component| component.iter().copied())
        .collect::<HashSet<_>>();
    commit_ready_components_with_refs_by_def(infer, &refs_by_def, &target_defs)
}

pub fn commit_ready_components_with_refs_by_def(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    target_defs: &HashSet<DefId>,
) -> Vec<usize> {
    commit_ready_components_with_refs_by_def_profiled(
        infer,
        refs_by_def,
        target_defs,
        &mut CommitReadyProfile::default(),
    )
}

pub fn commit_ready_components_with_refs_by_def_profiled(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    target_defs: &HashSet<DefId>,
    profile: &mut CommitReadyProfile,
) -> Vec<usize> {
    let relevant_components = infer
        .components
        .iter()
        .enumerate()
        .map(|(idx, _)| idx)
        .collect::<HashSet<_>>();
    drain_ready_components_with_refs_by_def_profiled(
        infer,
        refs_by_def,
        relevant_components,
        target_defs,
        profile,
    )
}

pub fn commit_ready_components_in_set_with_refs_by_def_profiled(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    relevant_components: &HashSet<usize>,
    target_defs: &HashSet<DefId>,
    profile: &mut CommitReadyProfile,
) -> Vec<usize> {
    drain_ready_components_with_refs_by_def_profiled(
        infer,
        refs_by_def,
        relevant_components.clone(),
        target_defs,
        profile,
    )
}

pub fn refs_by_def(refs: &RefTable) -> HashMap<DefId, Vec<ResolvedRef>> {
    let mut refs_by_def = HashMap::new();
    for resolved in refs.resolved().values() {
        refs_by_def
            .entry(resolved.def_id)
            .or_insert_with(Vec::new)
            .push(*resolved);
    }
    refs_by_def
}

pub fn refs_by_owner(refs: &RefTable) -> HashMap<DefId, Vec<ResolvedRef>> {
    let mut refs_by_owner = HashMap::new();
    for resolved in refs.resolved().values() {
        let Some(owner) = resolved.owner else {
            continue;
        };
        refs_by_owner
            .entry(owner)
            .or_insert_with(Vec::new)
            .push(*resolved);
    }
    refs_by_owner
}

fn ready_components_in_set(infer: &Infer, relevant_components: &HashSet<usize>) -> Vec<usize> {
    let mut ready = relevant_components
        .iter()
        .copied()
        .filter(|&idx| *infer.component_pending_selections[idx].borrow() == 0)
        .filter(|&idx| {
            !infer.component_edges[idx]
                .borrow()
                .iter()
                .any(|edge| relevant_components.contains(edge))
        })
        .collect::<Vec<_>>();
    ready.sort_unstable();
    ready
}

fn drain_ready_components_with_refs_by_def_profiled(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    mut relevant_components: HashSet<usize>,
    target_defs: &HashSet<DefId>,
    profile: &mut CommitReadyProfile,
) -> Vec<usize> {
    let mut committed_all = Vec::new();
    loop {
        let ready_scan_start = Instant::now();
        let ready = ready_components_in_set(infer, &relevant_components);
        profile.ready_scan += ready_scan_start.elapsed();
        if ready.is_empty() {
            break;
        }
        let committed = commit_selected_ready_components_with_refs_by_def_profiled(
            infer,
            refs_by_def,
            target_defs,
            ready,
            profile,
        );
        if committed.is_empty() {
            break;
        }
        let committed_set = committed.iter().copied().collect::<HashSet<_>>();
        relevant_components.retain(|idx| !committed_set.contains(idx));
        committed_all.extend(committed);
        infer.flush_compact_lower_instances();
    }
    committed_all
}

fn commit_selected_ready_components_with_refs_by_def_profiled(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    target_defs: &HashSet<DefId>,
    ready: Vec<usize>,
    profile: &mut CommitReadyProfile,
) -> Vec<usize> {
    let total_start = Instant::now();
    profile.ready_components += ready.len();
    let mut committed = Vec::new();
    for &component_idx in &ready {
        let defs = infer.components[component_idx]
            .iter()
            .copied()
            .filter_map(|def| {
                let has_external_refs =
                    def_has_external_refs(infer, refs_by_def, component_idx, def)
                        && !infer.is_frozen_ref_committed(def);
                let needs_compact = target_defs.contains(&def)
                    && infer.compact_schemes.borrow().get(&def).is_none();
                let needs_frozen =
                    has_external_refs && infer.frozen_schemes.borrow().get(&def).is_none();
                let def_tv = infer.def_tvs.borrow().get(&def).copied()?;
                Some(CommitDef {
                    def,
                    tv: def_tv,
                    has_external_refs,
                    needs_compact,
                    needs_frozen,
                })
            })
            .collect::<Vec<_>>();

        if defs
            .iter()
            .all(|item| !(item.needs_compact || item.has_external_refs))
        {
            committed.push(component_idx);
            continue;
        }

        let compact_items = defs
            .iter()
            .filter(|item| item.needs_compact || item.has_external_refs)
            .map(|item| (item.def, item.tv))
            .collect::<Vec<_>>();
        let compact_start = Instant::now();
        let roots = compact_items.iter().map(|(_, tv)| *tv).collect::<Vec<_>>();
        let (compacted, compact_profile) = compact_type_vars_in_order_profiled(infer, &roots);
        profile.compact += compact_start.elapsed();
        profile.compact_var_side += compact_profile.compact_var_side;
        profile.compact_pos_ref += compact_profile.compact_pos_ref;
        profile.compact_neg_ref += compact_profile.compact_neg_ref;
        profile.compact_reachable_rec_vars += compact_profile.compact_reachable_rec_vars;
        let compacted_by_def = compact_items
            .into_iter()
            .zip(compacted)
            .map(|((def, _), compact)| (def, compact))
            .collect::<HashMap<_, _>>();

        let mut changed = false;
        for item in defs.into_iter() {
            if !(item.needs_compact || item.has_external_refs) {
                continue;
            }
            let Some(compact) = compacted_by_def.get(&item.def) else {
                continue;
            };
            let mut frozen = infer.frozen_schemes.borrow().get(&item.def).cloned();

            if item.needs_compact || item.needs_frozen {
                let compact_role_constraints = if item.needs_compact {
                    let role_constraints_start = Instant::now();
                    let constraints = compact_role_constraints(infer, item.def);
                    profile.role_constraints += role_constraints_start.elapsed();
                    Some(constraints)
                } else {
                    None
                };

                let cooccur_start = Instant::now();
                let (scheme, compact_role_constraints) =
                    if let Some(constraints) = compact_role_constraints {
                        coalesce_by_co_occurrence_with_role_constraints(compact, &constraints)
                    } else {
                        (coalesce_by_co_occurrence(compact), Vec::new())
                    };
                profile.cooccur += cooccur_start.elapsed();

                let freeze_start = Instant::now();
                let extra_quantified =
                    collect_compact_role_constraint_free_vars(&compact_role_constraints);
                let new_frozen = freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
                    infer,
                    scheme.clone(),
                    extra_quantified.as_slice(),
                    &infer.non_generic_vars_of(item.def),
                );
                profile.freeze += freeze_start.elapsed();
                if item.needs_compact {
                    infer.store_compact_scheme(item.def, scheme);
                    infer.store_compact_role_constraints(item.def, compact_role_constraints);
                    profile.compacted_defs += 1;
                }
                infer.store_frozen_scheme(item.def, new_frozen.clone());
                frozen = Some(new_frozen);
                changed = true;
            }

            let Some(frozen) = frozen else {
                continue;
            };

            if item.has_external_refs {
                infer.mark_frozen_ref_committed(item.def);
                changed = true;
            }

            if let Some(resolved_refs) = refs_by_def.get(&item.def) {
                for resolved in resolved_refs {
                    if resolved
                        .owner
                        .and_then(|owner| infer.def_to_component.get(&owner).copied())
                        == Some(component_idx)
                    {
                        continue;
                    }
                    let instantiate_start = Instant::now();
                    let (instance, instantiate_profile) = instantiate_as_view_with_subst_profiled(
                        infer,
                        &frozen,
                        infer.level_of(resolved.ref_tv),
                        &[],
                    );
                    profile.instantiate_build_subst += instantiate_profile.build_subst;
                    let constrain_start = Instant::now();
                    profile.instantiate_subst_body += instantiate_profile.subst_body;
                    infer.constrain_instantiated_ref_instance(instance.clone(), resolved.ref_tv);
                    profile.instantiate_constrain += constrain_start.elapsed();
                    if let Some(owner) = resolved.owner {
                        let role_constraints_start = Instant::now();
                        infer.instantiate_role_constraints_for_owner(
                            item.def,
                            owner,
                            instance.subst.as_slice(),
                        );
                        profile.instantiate_role_constraints += role_constraints_start.elapsed();
                    }
                    profile.instantiate += instantiate_start.elapsed();
                    profile.instantiated_refs += 1;
                    *profile
                        .instantiate_counts_by_def
                        .entry(item.def)
                        .or_default() += 1;
                }
            }
        }
        if changed {
            committed.push(component_idx);
        }
    }
    if !committed.is_empty() {
        let prune_start = Instant::now();
        let committed_set = committed.iter().copied().collect::<HashSet<_>>();
        for edges in &infer.component_edges {
            edges
                .borrow_mut()
                .retain(|edge| !committed_set.contains(edge));
        }
        profile.prune_edges += prune_start.elapsed();
    }
    profile.committed_components += committed.len();
    profile.total += total_start.elapsed();
    committed
}

fn compact_role_constraints(infer: &Infer, def: DefId) -> Vec<CompactRoleConstraint> {
    infer
        .role_constraints_of(def)
        .into_iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role,
            args: constraint
                .args
                .into_iter()
                .map(|arg| CompactBounds {
                    self_var: None,
                    lower: compact_pos_expr(infer, arg.pos),
                    upper: compact_neg_expr(infer, arg.neg),
                })
                .collect(),
        })
        .collect()
}

fn def_has_external_refs(
    infer: &Infer,
    refs_by_def: &HashMap<DefId, Vec<ResolvedRef>>,
    component_idx: usize,
    def: DefId,
) -> bool {
    refs_by_def.get(&def).is_some_and(|resolved_refs| {
        resolved_refs.iter().any(|resolved| {
            resolved
                .owner
                .and_then(|owner| infer.def_to_component.get(&owner).copied())
                != Some(component_idx)
        })
    })
}

struct CommitDef {
    def: DefId,
    tv: crate::ids::TypeVar,
    has_external_refs: bool,
    needs_compact: bool,
    needs_frozen: bool,
}
