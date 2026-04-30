use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ids::DefId;
use crate::ref_table::{RefTable, ResolvedRef};
use crate::solve::Infer;
use crate::types::{Neg, Pos};
use smallvec::SmallVec;

pub mod close;

pub use self::close::*;

// ── ComponentScc ─────────────────────────────────────────────────────────────

/// `Infer.components` / `Infer.component_edges` 上で計算した SCC。
/// `components` には元の component index が入る。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComponentScc {
    pub components: Vec<usize>,
}

// ── エントリポイント ──────────────────────────────────────────────────────────

pub fn compute_component_sccs(infer: &Infer) -> Vec<ComponentScc> {
    let graph = infer
        .component_edges
        .iter()
        .map(|edges| edges.borrow().iter().copied().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    compute_sccs_from_graph(&graph)
}

pub fn compress_components(infer: &mut Infer, sccs: &[ComponentScc]) {
    let mut component_to_scc = HashMap::new();
    for (new_idx, scc) in sccs.iter().enumerate() {
        for &old_idx in &scc.components {
            component_to_scc.insert(old_idx, new_idx);
        }
    }

    let mut new_components = Vec::with_capacity(sccs.len());
    let mut new_component_edges = Vec::with_capacity(sccs.len());
    let mut new_pending = Vec::with_capacity(sccs.len());
    let mut new_def_to_component = FxHashMap::default();

    for (new_idx, scc) in sccs.iter().enumerate() {
        let mut merged_defs = Vec::new();
        let mut pending = 0usize;
        let mut outgoing = BTreeSet::new();

        for &old_idx in &scc.components {
            merged_defs.extend(infer.components[old_idx].iter().copied());
            pending += *infer.component_pending_selections[old_idx].borrow();

            for &edge in infer.component_edges[old_idx].borrow().iter() {
                let Some(&target_idx) = component_to_scc.get(&edge) else {
                    continue;
                };
                if target_idx != new_idx {
                    outgoing.insert(target_idx);
                }
            }
        }

        merged_defs.sort_by_key(|def| def.0);
        let component = SmallVec::<[crate::ids::DefId; 1]>::from_vec(merged_defs);
        for &def in &component {
            new_def_to_component.insert(def, new_idx);
        }

        new_components.push(component);
        new_component_edges.push(RefCell::new(SmallVec::from_iter(outgoing.into_iter())));
        new_pending.push(RefCell::new(pending));
    }

    infer.components = new_components;
    infer.def_to_component = new_def_to_component;
    infer.component_edges = new_component_edges;
    infer.component_pending_selections = new_pending;
}

pub fn share_type_vars_within_sccs(infer: &Infer, refs: &RefTable, sccs: &[ComponentScc]) {
    let refs_by_owner = refs_by_owner(refs);
    share_type_vars_within_sccs_with_refs_by_owner(infer, &refs_by_owner, sccs);
}

pub fn share_type_vars_within_sccs_with_refs_by_owner(
    infer: &Infer,
    refs_by_owner: &HashMap<DefId, Vec<ResolvedRef>>,
    sccs: &[ComponentScc],
) {
    for (new_idx, _scc) in sccs.iter().enumerate() {
        let mut defs_in_scc = HashSet::new();
        for &def in &infer.components[new_idx] {
            defs_in_scc.insert(def);
        }

        for &owner in &defs_in_scc {
            let Some(resolved_refs) = refs_by_owner.get(&owner) else {
                continue;
            };
            for resolved in resolved_refs {
                if !defs_in_scc.contains(&resolved.def_id) {
                    continue;
                }
                let Some(def_tv) = infer.def_tvs.borrow().get(&resolved.def_id).copied() else {
                    continue;
                };
                infer.constrain(Pos::Var(def_tv), Neg::Var(resolved.ref_tv));
            }
        }
    }
}

/// Tarjan が返す reverse-topological order を前提に、
/// 先頭から「外向き辺がない SCC」だけを抜き出す。
/// 辺を持つ SCC が出た時点でそこで打ち切る。
pub fn sink_component_prefix(infer: &Infer) -> Vec<usize> {
    let mut out = Vec::new();
    for (idx, edges) in infer.component_edges.iter().enumerate() {
        if !edges.borrow().is_empty() {
            break;
        }
        out.push(idx);
    }
    out
}

// ── Tarjan ───────────────────────────────────────────────────────────────────

fn compute_sccs_from_graph(graph: &[Vec<usize>]) -> Vec<ComponentScc> {
    let mut tarjan = Tarjan::new(graph);
    for node in 0..graph.len() {
        if tarjan.index_of[node].is_none() {
            tarjan.visit(node);
        }
    }
    tarjan.result
}

/// `sink_component_prefix` のうち、selection pending がない SCC だけ返す。
pub fn ready_components(infer: &Infer) -> Vec<usize> {
    sink_component_prefix(infer)
        .into_iter()
        .filter(|&idx| *infer.component_pending_selections[idx].borrow() == 0)
        .collect()
}

pub fn component_closure_from_defs(infer: &Infer, roots: &HashSet<DefId>) -> HashSet<usize> {
    let mut out = HashSet::new();
    let mut pending_components = roots
        .iter()
        .filter_map(|def| infer.def_to_component.get(def).copied())
        .collect::<Vec<_>>();

    while let Some(component_idx) = pending_components.pop() {
        if !out.insert(component_idx) {
            continue;
        }
        pending_components.extend(
            infer.component_edges[component_idx]
                .borrow()
                .iter()
                .copied(),
        );
    }

    out
}

pub fn component_closure_from_defs_with_refs_by_owner(
    infer: &Infer,
    refs_by_owner: &HashMap<DefId, Vec<ResolvedRef>>,
    roots: &HashSet<DefId>,
) -> HashSet<usize> {
    let mut out = HashSet::new();
    let mut seen_defs = HashSet::new();
    let mut pending_defs = roots.iter().copied().collect::<Vec<_>>();
    let mut pending_components = Vec::new();

    loop {
        if let Some(def) = pending_defs.pop() {
            if !seen_defs.insert(def) {
                continue;
            }
            if let Some(component_idx) = infer.def_to_component.get(&def).copied() {
                pending_components.push(component_idx);
            }
            if let Some(resolved_refs) = refs_by_owner.get(&def) {
                pending_defs.extend(resolved_refs.iter().map(|resolved| resolved.def_id));
            }
            continue;
        }

        let Some(component_idx) = pending_components.pop() else {
            break;
        };
        if !out.insert(component_idx) {
            continue;
        }

        pending_components.extend(
            infer.component_edges[component_idx]
                .borrow()
                .iter()
                .copied(),
        );
        for &def in &infer.components[component_idx] {
            if seen_defs.insert(def) {
                if let Some(resolved_refs) = refs_by_owner.get(&def) {
                    pending_defs.extend(resolved_refs.iter().map(|resolved| resolved.def_id));
                }
            }
        }
    }

    out
}

struct Tarjan<'a> {
    graph: &'a [Vec<usize>],
    next_index: usize,
    index_of: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    result: Vec<ComponentScc>,
}

impl<'a> Tarjan<'a> {
    fn new(graph: &'a [Vec<usize>]) -> Self {
        Self {
            graph,
            next_index: 0,
            index_of: vec![None; graph.len()],
            lowlink: vec![0; graph.len()],
            stack: Vec::new(),
            on_stack: vec![false; graph.len()],
            result: Vec::new(),
        }
    }

    fn visit(&mut self, node: usize) {
        let index = self.next_index;
        self.next_index += 1;
        self.index_of[node] = Some(index);
        self.lowlink[node] = index;
        self.stack.push(node);
        self.on_stack[node] = true;

        for &next in &self.graph[node] {
            if self.index_of[next].is_none() {
                self.visit(next);
                self.lowlink[node] = self.lowlink[node].min(self.lowlink[next]);
            } else if self.on_stack[next] {
                self.lowlink[node] = self.lowlink[node].min(self.index_of[next].unwrap());
            }
        }

        if self.lowlink[node] != index {
            return;
        }

        let mut components = Vec::new();
        loop {
            let current = self.stack.pop().expect("tarjan stack should contain root");
            self.on_stack[current] = false;
            components.push(current);
            if current == node {
                break;
            }
        }
        components.sort_unstable();
        self.result.push(ComponentScc { components });
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use super::{
        commit_ready_components, commit_ready_components_in_set_with_refs_by_def_profiled,
        compact_ready_components, component_closure_from_defs,
        component_closure_from_defs_with_refs_by_owner, compress_components,
        compute_sccs_from_graph, ready_components, share_type_vars_within_sccs,
        sink_component_prefix,
    };
    use crate::fresh_def_id;
    use crate::fresh_ref_id;
    use crate::fresh_type_var;
    use crate::ref_table::RefTable;
    use crate::solve::Infer;
    use crate::symbols::{Name, Path};
    use crate::types::Pos;

    #[test]
    fn compute_component_sccs_finds_cycle() {
        let graph = vec![vec![1], vec![2], vec![0, 3], vec![]];

        let mut sccs = compute_sccs_from_graph(&graph)
            .into_iter()
            .map(|scc| scc.components)
            .collect::<Vec<_>>();
        sccs.sort();

        assert_eq!(sccs, vec![vec![0, 1, 2], vec![3]]);
    }

    #[test]
    fn share_type_vars_within_sccs_adds_def_to_ref_constraint() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_a_tv = fresh_type_var();
        let ref_tv = fresh_type_var();
        let ref_id = fresh_ref_id();
        let refs = {
            let mut refs = RefTable::default();
            refs.resolve(ref_id, def_b, ref_tv, Some(def_a));
            refs
        };

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_level(def_a_tv, 0);
        infer.register_level(ref_tv, 0);
        infer.register_def_tv(def_b, def_a_tv);
        infer.add_edge(def_a, def_b);
        infer.add_edge(def_b, def_a);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);
        share_type_vars_within_sccs(&infer, &refs, &sccs);

        assert!(infer.lowers_of(ref_tv).contains(&Pos::Var(def_a_tv)));
    }

    #[test]
    fn compress_components_rewrites_component_state() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_def(def_c);
        infer.add_edge(def_a, def_b);
        infer.add_edge(def_b, def_a);
        infer.add_edge(def_b, def_c);
        infer.increment_pending_selection(def_a);
        infer.increment_pending_selection(def_b);
        infer.increment_pending_selection(def_c);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        assert_eq!(infer.components.len(), 2);
        assert_eq!(
            infer.def_to_component[&def_a],
            infer.def_to_component[&def_b]
        );
        assert_ne!(
            infer.def_to_component[&def_a],
            infer.def_to_component[&def_c]
        );

        let ab_idx = infer.def_to_component[&def_a];
        let c_idx = infer.def_to_component[&def_c];
        assert_eq!(*infer.component_pending_selections[ab_idx].borrow(), 2);
        assert_eq!(*infer.component_pending_selections[c_idx].borrow(), 1);
        assert!(infer.component_edges[ab_idx].borrow().contains(&c_idx));
    }

    #[test]
    fn ready_components_take_sink_prefix_then_filter_pending() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_def(def_c);

        infer.add_edge(def_a, def_b);
        infer.add_edge(def_b, def_a);
        infer.add_edge(def_c, def_a);
        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let ab_idx = infer.def_to_component[&def_a];
        let c_idx = infer.def_to_component[&def_c];

        assert_eq!(sink_component_prefix(&infer), vec![ab_idx]);
        assert_eq!(ready_components(&infer), vec![ab_idx]);

        infer.increment_pending_selection(def_c);
        assert_eq!(
            ready_components(&infer),
            vec![ab_idx],
            "pending on a non-sink SCC should not affect sink candidates",
        );
        infer.increment_pending_selection(def_a);
        assert!(
            ready_components(&infer).is_empty(),
            "pending selections should filter out sink SCCs"
        );
        assert_eq!(
            sink_component_prefix(&infer),
            vec![ab_idx],
            "edge-based extraction should be unaffected by pending selections",
        );
        assert_ne!(ab_idx, c_idx);
    }

    #[test]
    fn compact_ready_components_builds_coalesced_schemes_for_ready_sccs() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let tv_a = fresh_type_var();
        let tv_b = fresh_type_var();

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_level(tv_a, 0);
        infer.register_level(tv_b, 0);
        infer.register_def_tv(def_a, tv_a);
        infer.register_def_tv(def_b, tv_b);
        infer.add_edge(def_b, def_a);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let a_idx = infer.def_to_component[&def_a];
        infer.add_lower(tv_a, Pos::Var(tv_a));

        let compacted = compact_ready_components(&infer);
        assert!(compacted.contains_key(&a_idx));
        assert_eq!(compacted[&a_idx].len(), 1);
        assert_eq!(compacted[&a_idx][0].0, def_a);
    }

    #[test]
    fn commit_ready_components_stores_schemes_and_constrains_all_refs() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let tv_a = fresh_type_var();
        let ref_tv_1 = fresh_type_var();
        let ref_tv_2 = fresh_type_var();
        let ref_id_1 = fresh_ref_id();
        let ref_id_2 = fresh_ref_id();

        infer.register_def(def_a);
        infer.register_level(tv_a, 0);
        infer.register_level(ref_tv_1, 0);
        infer.register_level(ref_tv_2, 0);
        infer.register_def_tv(def_a, tv_a);
        let int = Pos::Con(
            Path {
                segments: vec![Name("int".to_string())],
            },
            vec![],
        );
        infer.add_lower(tv_a, int.clone());

        let mut refs = RefTable::default();
        refs.resolve(ref_id_1, def_a, ref_tv_1, None);
        refs.resolve(ref_id_2, def_a, ref_tv_2, None);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);
        let ready = commit_ready_components(&infer, &refs);

        let a_idx = infer.def_to_component[&def_a];
        assert_eq!(ready, vec![a_idx]);
        assert!(infer.compact_schemes.borrow().get(&def_a).is_some());
        assert!(infer.lowers_of(ref_tv_1).contains(&int));
        assert!(infer.lowers_of(ref_tv_2).contains(&int));
    }

    #[test]
    fn component_closure_from_defs_follows_dependency_edges() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_def(def_c);
        infer.add_edge(def_a, def_b);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let roots = HashSet::from([def_a]);
        let closure = component_closure_from_defs(&infer, &roots);

        assert!(closure.contains(&infer.def_to_component[&def_a]));
        assert!(closure.contains(&infer.def_to_component[&def_b]));
        assert!(!closure.contains(&infer.def_to_component[&def_c]));
    }

    #[test]
    fn component_closure_from_defs_with_refs_by_owner_follows_refs() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_def(def_c);

        let refs_by_owner = HashMap::from([(
            def_a,
            vec![crate::ref_table::ResolvedRef {
                def_id: def_b,
                ref_tv: fresh_type_var(),
                owner: Some(def_a),
            }],
        )]);
        let roots = HashSet::from([def_a]);
        let closure =
            component_closure_from_defs_with_refs_by_owner(&infer, &refs_by_owner, &roots);

        assert!(closure.contains(&infer.def_to_component[&def_a]));
        assert!(closure.contains(&infer.def_to_component[&def_b]));
        assert!(!closure.contains(&infer.def_to_component[&def_c]));
    }

    #[test]
    fn commit_ready_components_in_set_skips_irrelevant_sinks() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();
        let tv_a = fresh_type_var();
        let tv_b = fresh_type_var();
        let tv_c = fresh_type_var();
        let int = Pos::Con(
            Path {
                segments: vec![Name("int".to_string())],
            },
            vec![],
        );

        infer.register_def(def_a);
        infer.register_def(def_b);
        infer.register_def(def_c);
        infer.register_level(tv_a, 0);
        infer.register_level(tv_b, 0);
        infer.register_level(tv_c, 0);
        infer.register_def_tv(def_a, tv_a);
        infer.register_def_tv(def_b, tv_b);
        infer.register_def_tv(def_c, tv_c);
        infer.add_lower(tv_a, int.clone());
        infer.add_lower(tv_b, int.clone());
        infer.add_lower(tv_c, int.clone());
        infer.add_edge(def_a, def_b);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let relevant_components = HashSet::from([
            infer.def_to_component[&def_a],
            infer.def_to_component[&def_b],
        ]);
        let target_defs = HashSet::from([def_a, def_b]);
        let refs_by_def = HashMap::new();
        let mut profile = super::CommitReadyProfile::default();

        let committed = commit_ready_components_in_set_with_refs_by_def_profiled(
            &infer,
            &refs_by_def,
            &relevant_components,
            &target_defs,
            &mut profile,
        );
        assert!(committed.contains(&infer.def_to_component[&def_b]));
        assert!(committed.contains(&infer.def_to_component[&def_a]));
        assert!(infer.compact_schemes.borrow().get(&def_b).is_some());
        assert!(infer.compact_schemes.borrow().get(&def_a).is_some());
        assert!(infer.compact_schemes.borrow().get(&def_c).is_none());
        assert!(!committed.contains(&infer.def_to_component[&def_c]));
    }

    #[test]
    fn commit_ready_components_in_set_ignores_irrelevant_non_sink_prefix() {
        let mut infer = Infer::new();
        let def_a = fresh_def_id();
        let def_b = fresh_def_id();
        let def_c = fresh_def_id();
        let tv_a = fresh_type_var();
        let tv_b = fresh_type_var();
        let tv_c = fresh_type_var();
        let int = Pos::Con(
            Path {
                segments: vec![Name("int".to_string())],
            },
            vec![],
        );

        infer.register_def(def_c);
        infer.register_def(def_b);
        infer.register_def(def_a);
        infer.register_level(tv_a, 0);
        infer.register_level(tv_b, 0);
        infer.register_level(tv_c, 0);
        infer.register_def_tv(def_a, tv_a);
        infer.register_def_tv(def_b, tv_b);
        infer.register_def_tv(def_c, tv_c);
        infer.add_lower(tv_a, int.clone());
        infer.add_lower(tv_b, int.clone());
        infer.add_lower(tv_c, int);
        infer.add_edge(def_c, def_b);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let relevant_components = HashSet::from([infer.def_to_component[&def_a]]);
        let target_defs = HashSet::from([def_a]);
        let refs_by_def = HashMap::new();
        let mut profile = super::CommitReadyProfile::default();

        let ready = commit_ready_components_in_set_with_refs_by_def_profiled(
            &infer,
            &refs_by_def,
            &relevant_components,
            &target_defs,
            &mut profile,
        );
        assert_eq!(ready, vec![infer.def_to_component[&def_a]]);
        assert!(infer.compact_schemes.borrow().get(&def_a).is_some());
        assert!(infer.compact_schemes.borrow().get(&def_b).is_none());
        assert!(infer.compact_schemes.borrow().get(&def_c).is_none());
    }

    #[test]
    fn commit_ready_components_in_set_skips_non_target_defs_inside_ready_component() {
        let mut infer = Infer::new();
        let def_target = fresh_def_id();
        let def_helper = fresh_def_id();
        let tv_target = fresh_type_var();
        let tv_helper = fresh_type_var();
        let int = Pos::Con(
            Path {
                segments: vec![Name("int".to_string())],
            },
            vec![],
        );

        infer.register_def(def_target);
        infer.register_def(def_helper);
        infer.register_level(tv_target, 0);
        infer.register_level(tv_helper, 0);
        infer.register_def_tv(def_target, tv_target);
        infer.register_def_tv(def_helper, tv_helper);
        infer.add_lower(tv_target, int.clone());
        infer.add_lower(tv_helper, int);
        infer.add_edge(def_target, def_helper);
        infer.add_edge(def_helper, def_target);

        let sccs = super::compute_component_sccs(&infer);
        compress_components(&mut infer, &sccs);

        let relevant_components = HashSet::from([infer.def_to_component[&def_target]]);
        let target_defs = HashSet::from([def_target]);
        let refs_by_def = HashMap::new();
        let mut profile = super::CommitReadyProfile::default();

        let ready = commit_ready_components_in_set_with_refs_by_def_profiled(
            &infer,
            &refs_by_def,
            &relevant_components,
            &target_defs,
            &mut profile,
        );

        assert_eq!(ready, vec![infer.def_to_component[&def_target]]);
        assert!(infer.compact_schemes.borrow().get(&def_target).is_some());
        assert!(infer.compact_schemes.borrow().get(&def_helper).is_none());
        assert_eq!(profile.compacted_defs, 1);
    }
}
