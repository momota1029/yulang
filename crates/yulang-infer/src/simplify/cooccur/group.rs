use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ids::TypeVar;

use super::{CompactBounds, CompactRoleConstraint, CompactType, CompactTypeScheme};

pub(super) fn analyze_group_co_occurrences_with_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> GroupCoOccurrences {
    let mut ctx = GroupCoOccurrenceContext::default();
    ctx.collect_root_bounds(&scheme.cty);
    let mut rec_vars = scheme.rec_vars.iter().collect::<Vec<_>>();
    rec_vars.sort_by_key(|(tv, _)| tv.0);
    for (_, bounds) in rec_vars {
        ctx.collect_bounds(bounds);
    }
    for constraint in constraints {
        for arg in &constraint.args {
            ctx.collect_bounds(arg);
        }
    }
    ctx.analysis
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct GroupCoOccurrences {
    pub(super) types: HashMap<TypeVar, GroupOccurrenceInfo>,
    pub(super) effect_types: HashMap<TypeVar, GroupOccurrenceInfo>,
    pub(super) effects: HashMap<TypeVar, GroupOccurrenceInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct GroupOccurrenceInfo {
    positive: HashSet<u64>,
    negative: HashSet<u64>,
}

pub(super) fn indistinguishable_group_replacements(
    occurrences: &HashMap<TypeVar, GroupOccurrenceInfo>,
    require_bipolar: bool,
) -> HashMap<TypeVar, TypeVar> {
    let mut parent = occurrences
        .keys()
        .copied()
        .map(|tv| (tv, tv))
        .collect::<HashMap<_, _>>();

    let mut positive_groups = BTreeMap::<Vec<u64>, Vec<TypeVar>>::new();
    let mut negative_groups = BTreeMap::<Vec<u64>, Vec<TypeVar>>::new();
    for (&tv, info) in occurrences {
        if require_bipolar && (info.positive.is_empty() || info.negative.is_empty()) {
            continue;
        }
        if !info.positive.is_empty() {
            let mut groups = info.positive.iter().copied().collect::<Vec<_>>();
            groups.sort_unstable();
            positive_groups.entry(groups).or_default().push(tv);
        }
        if !info.negative.is_empty() {
            let mut groups = info.negative.iter().copied().collect::<Vec<_>>();
            groups.sort_unstable();
            negative_groups.entry(groups).or_default().push(tv);
        }
    }

    for vars in positive_groups
        .into_values()
        .chain(negative_groups.into_values())
    {
        let mut vars = vars;
        vars.sort_by_key(|tv| tv.0);
        if let Some((&first, rest)) = vars.split_first() {
            for &tv in rest {
                union_group_parent(&mut parent, first, tv);
            }
        }
    }

    let mut replacements = HashMap::new();
    for tv in parent.keys().copied().collect::<Vec<_>>() {
        let root = find_group_parent(&mut parent, tv);
        if root != tv {
            replacements.insert(tv, root);
        }
    }
    replacements
}

#[derive(Default)]
struct GroupCoOccurrenceContext {
    next_group: u64,
    analysis: GroupCoOccurrences,
}

impl GroupCoOccurrenceContext {
    fn collect_root_bounds(&mut self, bounds: &CompactBounds) {
        self.collect_type(&bounds.lower, true);
        self.collect_root_upper_shared_direct_vars(bounds);
        let group = self.fresh_group();
        self.collect_type_children_in_group(&bounds.upper, false, group);
    }

    fn collect_bounds(&mut self, bounds: &CompactBounds) {
        self.collect_type(&bounds.lower, true);
        self.collect_type(&bounds.upper, false);
    }

    fn collect_type(&mut self, ty: &CompactType, positive: bool) {
        let group = self.fresh_group();
        self.collect_type_in_group(ty, positive, group);
    }

    fn collect_type_in_group(&mut self, ty: &CompactType, positive: bool, group: u64) {
        for tv in sorted_type_vars(&ty.vars) {
            insert_group_occurrence(&mut self.analysis.types, tv, positive, group);
        }
        self.collect_type_children_in_group(ty, positive, group);
    }

    fn collect_type_children_in_group(&mut self, ty: &CompactType, positive: bool, group: u64) {
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_type(&arg.lower, true);
                self.collect_type(&arg.upper, false);
            }
        }
        for fun in &ty.funs {
            self.collect_type(&fun.arg, !positive);
            self.collect_effect_type_in_group(&fun.arg_eff, !positive, group);
            self.collect_effect_type_in_group(&fun.ret_eff, positive, group);
            self.collect_effect_in_group(&fun.arg_eff, !positive, group);
            self.collect_effect_in_group(&fun.ret_eff, positive, group);
            self.collect_type(&fun.ret, positive);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_type(&field.value, positive);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_type(&field.value, positive);
            }
            self.collect_type(&spread.tail, positive);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_type(payload, positive);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_type(item, positive);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_type(item, positive);
            }
        }
    }

    fn collect_effect_type_in_group(&mut self, ty: &CompactType, positive: bool, group: u64) {
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_effect_atom_arg_type_in_group(&arg.lower, true, group);
                self.collect_effect_atom_arg_type_in_group(&arg.upper, false, group);
            }
        }
        for fun in &ty.funs {
            self.collect_effect_type_in_group(&fun.arg_eff, !positive, group);
            self.collect_effect_type_in_group(&fun.ret_eff, positive, group);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_effect_type_in_group(&field.value, positive, group);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_effect_type_in_group(&field.value, positive, group);
            }
            self.collect_effect_type_in_group(&spread.tail, positive, group);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_effect_type_in_group(payload, positive, group);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_effect_type_in_group(item, positive, group);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_effect_type_in_group(item, positive, group);
            }
        }
    }

    fn collect_effect_atom_arg_type_in_group(
        &mut self,
        ty: &CompactType,
        positive: bool,
        group: u64,
    ) {
        for tv in sorted_type_vars(&ty.vars) {
            insert_group_occurrence(&mut self.analysis.effect_types, tv, positive, group);
        }

        for con in &ty.cons {
            for arg in &con.args {
                self.collect_effect_atom_arg_type_in_group(&arg.lower, true, group);
                self.collect_effect_atom_arg_type_in_group(&arg.upper, false, group);
            }
        }
        for fun in &ty.funs {
            self.collect_effect_atom_arg_type_in_group(&fun.arg, !positive, group);
            self.collect_effect_type_in_group(&fun.arg_eff, !positive, group);
            self.collect_effect_type_in_group(&fun.ret_eff, positive, group);
            self.collect_effect_atom_arg_type_in_group(&fun.ret, positive, group);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_effect_atom_arg_type_in_group(&field.value, positive, group);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_effect_atom_arg_type_in_group(&field.value, positive, group);
            }
            self.collect_effect_atom_arg_type_in_group(&spread.tail, positive, group);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_effect_atom_arg_type_in_group(payload, positive, group);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_effect_atom_arg_type_in_group(item, positive, group);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_effect_atom_arg_type_in_group(item, positive, group);
            }
            self.collect_effect_atom_arg_type_in_group(&row.tail, positive, group);
        }
    }

    fn collect_effect_in_group(&mut self, ty: &CompactType, positive: bool, group: u64) {
        for tv in sorted_type_vars(&ty.vars) {
            insert_group_occurrence(&mut self.analysis.effects, tv, positive, group);
        }

        for fun in &ty.funs {
            self.collect_effect_in_group(&fun.arg_eff, !positive, group);
            self.collect_effect_in_group(&fun.ret_eff, positive, group);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_effect_in_group(&field.value, positive, group);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_effect_in_group(&field.value, positive, group);
            }
            self.collect_effect_in_group(&spread.tail, positive, group);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_effect_in_group(payload, positive, group);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_effect_in_group(item, positive, group);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_effect_in_group(item, positive, group);
            }
            self.collect_effect_in_group(&row.tail, positive, group);
        }
    }

    fn fresh_group(&mut self) -> u64 {
        let group = self.next_group;
        self.next_group += 1;
        group
    }

    fn collect_root_upper_shared_direct_vars(&mut self, bounds: &CompactBounds) {
        let shared = bounds
            .upper
            .vars
            .intersection(&bounds.lower.vars)
            .copied()
            .collect::<Vec<_>>();
        if shared.is_empty() {
            return;
        }

        let group = self.fresh_group();
        for tv in shared {
            insert_group_occurrence(&mut self.analysis.types, tv, false, group);
        }
    }
}

fn sorted_type_vars(vars: &HashSet<TypeVar>) -> Vec<TypeVar> {
    let mut vars = vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars
}

fn insert_group_occurrence(
    map: &mut HashMap<TypeVar, GroupOccurrenceInfo>,
    tv: TypeVar,
    positive: bool,
    group: u64,
) {
    let entry = map.entry(tv).or_default();
    if positive {
        entry.positive.insert(group);
    } else {
        entry.negative.insert(group);
    }
}

fn union_group_parent(parent: &mut HashMap<TypeVar, TypeVar>, lhs: TypeVar, rhs: TypeVar) {
    let lhs_root = find_group_parent(parent, lhs);
    let rhs_root = find_group_parent(parent, rhs);
    if lhs_root == rhs_root {
        return;
    }
    let (root, child) = if lhs_root.0 <= rhs_root.0 {
        (lhs_root, rhs_root)
    } else {
        (rhs_root, lhs_root)
    };
    parent.insert(child, root);
}

fn find_group_parent(parent: &mut HashMap<TypeVar, TypeVar>, tv: TypeVar) -> TypeVar {
    let parent_tv = parent.get(&tv).copied().unwrap_or(tv);
    if parent_tv == tv {
        parent_tv
    } else {
        let root = find_group_parent(parent, parent_tv);
        parent.insert(tv, root);
        root
    }
}
