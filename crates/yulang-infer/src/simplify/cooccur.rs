use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

mod analysis;
mod group;
mod passes;
mod representative;

use crate::ids::TypeVar;
use crate::solve::effect_row::normalize_rewritten_bounds;
use crate::symbols::Path;
use crate::types::RecordField;

use super::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRow, CompactType,
    CompactTypeScheme, CompactVariant, merge_compact_bounds, merge_compact_types,
};
use super::polar::apply_polar_variable_removal;
use super::role_constraints::rewrite_role_constraints;
use analysis::analyze_co_occurrences_with_role_constraints;
use group::analyze_group_co_occurrences_with_role_constraints;
use passes::{
    apply_exact_row_unifications, apply_exact_sandwich_removal,
    apply_group_co_occurrence_substitutions, apply_one_sided_exact_alias_collapse,
    apply_shadow_var_collapse,
};
use representative::lower_representatives_for_subst;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoOccurrences {
    pub positive: HashMap<TypeVar, HashSet<AlongItem>>,
    pub negative: HashMap<TypeVar, HashSet<AlongItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AlongItem {
    Var(TypeVar),
    Exact(ExactKey),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactRoleConstraint {
    pub role: Path,
    pub args: Vec<CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(super) struct ExactSignature {
    positive: Vec<ExactKey>,
    negative: Vec<ExactKey>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct ExactInfo {
    positive: HashMap<TypeVar, HashSet<ExactKey>>,
    negative: HashMap<TypeVar, HashSet<ExactKey>>,
    signatures: HashMap<TypeVar, ExactSignature>,
    has_concrete_row: HashSet<TypeVar>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExactKey {
    digest: u64,
    kind: ExactKeyKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) enum ExactKeyKind {
    Other,
    Fun,
    EmptyRow,
    ConcreteRow,
}

pub fn analyze_co_occurrences(scheme: &CompactTypeScheme) -> CoOccurrences {
    analyze_co_occurrences_with_role_constraints(scheme, &[])
}

pub fn coalesce_by_co_occurrence(scheme: &CompactTypeScheme) -> CompactTypeScheme {
    coalesce_by_co_occurrence_with_role_constraints(scheme, &[]).0
}

pub fn coalesce_by_co_occurrence_with_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    let output = coalesce_by_co_occurrence_with_role_constraints_report(scheme, constraints);
    (output.scheme, output.constraints)
}

pub fn coalesce_by_co_occurrence_with_role_constraints_report(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> CoalesceOutput {
    coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
    )
}

fn coalesce_by_co_occurrence_with_role_constraints_report_inner(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    use_representatives: bool,
) -> CoalesceOutput {
    let mut current_scheme = scheme.clone();
    let mut current_constraints = constraints.to_vec();
    let mut rounds = Vec::new();

    loop {
        let protected_vars = centered_constraint_vars(&current_constraints);
        let mut analysis =
            analyze_co_occurrences_with_role_constraints(&current_scheme, &current_constraints);
        let mut rec_vars = current_scheme.rec_vars.clone();
        let mut all_vars = collect_all_vars(&current_scheme, &analysis);
        let group_analysis = analyze_group_co_occurrences_with_role_constraints(
            &current_scheme,
            &current_constraints,
        );
        let exact_info = ExactInfo::from_analysis(&analysis);
        all_vars.extend(group_analysis.types.keys().copied());
        all_vars.extend(group_analysis.effect_types.keys().copied());
        all_vars.extend(group_analysis.effects.keys().copied());
        all_vars.sort_by_key(|tv| tv.0);
        all_vars.dedup();
        all_vars.sort_by_key(|tv| std::cmp::Reverse(tv.0));

        let mut subst = HashMap::<TypeVar, Option<TypeVar>>::new();
        apply_group_co_occurrence_substitutions(
            &group_analysis,
            &mut analysis,
            &mut rec_vars,
            &protected_vars,
            &mut subst,
        );
        apply_polar_variable_removal(&all_vars, &analysis, &rec_vars, &protected_vars, &mut subst);
        apply_exact_row_unifications(
            &all_vars,
            &exact_info,
            &rec_vars,
            &protected_vars,
            &mut subst,
        );
        apply_exact_sandwich_removal(&all_vars, &exact_info, &protected_vars, &mut subst);
        apply_shadow_var_collapse(&all_vars, &analysis, &protected_vars, &mut subst);
        apply_one_sided_exact_alias_collapse(&all_vars, &analysis, &protected_vars, &mut subst);

        let representatives = lower_representatives_for_subst(
            &current_scheme,
            &current_constraints,
            &rec_vars,
            &subst,
        );
        let rewritten_scheme = if use_representatives {
            rewrite_scheme_with_representatives(
                &current_scheme,
                &rec_vars,
                &subst,
                &representatives,
            )
        } else {
            rewrite_scheme(&current_scheme, &rec_vars, &subst)
        };
        let rewritten_constraints = if use_representatives {
            rewrite_constraints_with_representatives(
                &rewritten_scheme,
                &current_constraints,
                &subst,
                &representatives,
            )
        } else {
            rewrite_role_constraints(&rewritten_scheme, &current_constraints, &subst)
        };

        if rewritten_scheme == current_scheme && rewritten_constraints == current_constraints {
            return CoalesceOutput {
                scheme: rewritten_scheme,
                constraints: rewritten_constraints,
                rounds,
            };
        }

        if !subst.is_empty() {
            rounds.push(CoalesceRound {
                subst,
                representatives,
            });
        }

        current_scheme = rewritten_scheme;
        current_constraints = rewritten_constraints;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoalesceOutput {
    pub scheme: CompactTypeScheme,
    pub constraints: Vec<CompactRoleConstraint>,
    pub rounds: Vec<CoalesceRound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoalesceRound {
    pub subst: HashMap<TypeVar, Option<TypeVar>>,
    pub representatives: HashMap<TypeVar, CompactType>,
}

fn centered_constraint_vars(constraints: &[CompactRoleConstraint]) -> HashSet<TypeVar> {
    constraints
        .iter()
        .flat_map(|constraint| constraint.args.iter().filter_map(centered_constraint_var))
        .collect()
}

fn centered_constraint_var(bounds: &CompactBounds) -> Option<TypeVar> {
    bounds.self_var.or_else(|| {
        let lower = single_compact_var(&bounds.lower);
        let upper = single_compact_var(&bounds.upper);
        match (lower, upper) {
            (Some(lhs), Some(rhs)) if lhs == rhs => Some(lhs),
            (Some(tv), None) | (None, Some(tv)) => Some(tv),
            _ => None,
        }
    })
}

fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1)
        .then(|| ty.vars.iter().copied().next())
        .flatten()
}

pub(crate) fn rewrite_scheme_with_subst(
    scheme: &CompactTypeScheme,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactTypeScheme {
    rewrite_scheme(scheme, &scheme.rec_vars, subst)
}

fn collect_all_vars(scheme: &CompactTypeScheme, analysis: &CoOccurrences) -> Vec<TypeVar> {
    let mut vars = scheme.rec_vars.keys().copied().collect::<HashSet<_>>();
    vars.extend(analysis.positive.keys().copied());
    vars.extend(analysis.negative.keys().copied());
    vars.into_iter().collect()
}

fn rewrite_scheme(
    scheme: &CompactTypeScheme,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactTypeScheme {
    rewrite_scheme_with_representatives(scheme, rec_vars, subst, &HashMap::new())
}

fn rewrite_scheme_with_representatives(
    scheme: &CompactTypeScheme,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactTypeScheme {
    let mut rewritten_rec_vars = HashMap::new();
    let mut rec_vars = rec_vars.iter().collect::<Vec<_>>();
    rec_vars.sort_by_key(|(tv, _)| tv.0);
    for (&tv, bounds) in rec_vars {
        if is_trivial_self_bounds(tv, bounds) {
            continue;
        }
        let Some(key) = rewrite_var(tv, subst) else {
            continue;
        };
        let rewritten = rewrite_bounds_with_representatives(bounds, subst, representatives);
        rewritten_rec_vars
            .entry(key)
            .and_modify(|existing: &mut CompactBounds| {
                *existing = merge_compact_bounds(true, existing.clone(), rewritten.clone());
            })
            .or_insert(rewritten);
    }

    CompactTypeScheme {
        cty: rewrite_bounds_with_representatives(&scheme.cty, subst, representatives),
        rec_vars: rewritten_rec_vars,
    }
}

pub(crate) fn rewrite_bounds(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactBounds {
    rewrite_bounds_with_representatives(bounds, subst, &HashMap::new())
}

fn rewrite_constraints_with_representatives(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> Vec<CompactRoleConstraint> {
    let rewritten = constraints
        .iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| rewrite_bounds_with_representatives(arg, subst, representatives))
                .collect(),
        })
        .collect::<Vec<_>>();
    rewrite_role_constraints(scheme, &rewritten, &HashMap::new())
}

fn rewrite_bounds_with_representatives(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactBounds {
    normalize_rewritten_bounds(CompactBounds {
        self_var: bounds.self_var.and_then(|tv| rewrite_var(tv, subst)),
        lower: rewrite_compact_type(&bounds.lower, subst, representatives),
        upper: rewrite_compact_type(&bounds.upper, subst, representatives),
    })
}

fn rewrite_compact_type(
    ty: &CompactType,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactType {
    let mut vars = HashSet::new();
    let mut representative_parts = CompactType::default();
    for &tv in &ty.vars {
        match rewrite_var_with_representative(tv, subst, representatives) {
            VarRewrite::Keep(tv) => {
                vars.insert(tv);
            }
            VarRewrite::Representative(representative) => {
                representative_parts =
                    merge_compact_types(true, representative_parts, representative);
            }
            VarRewrite::Remove => {}
        }
    }
    let cons = ty
        .cons
        .iter()
        .map(|con| CompactCon {
            path: con.path.clone(),
            args: con
                .args
                .iter()
                .map(|arg| rewrite_bounds_with_representatives(arg, subst, representatives))
                .collect(),
        })
        .collect();
    let funs = ty
        .funs
        .iter()
        .map(|fun| CompactFun {
            arg: rewrite_compact_type(&fun.arg, subst, representatives),
            arg_eff: rewrite_compact_type(&fun.arg_eff, subst, representatives),
            ret_eff: rewrite_compact_type(&fun.ret_eff, subst, representatives),
            ret: rewrite_compact_type(&fun.ret, subst, representatives),
        })
        .collect();
    let records = ty
        .records
        .iter()
        .map(|record| CompactRecord {
            fields: record
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: rewrite_compact_type(&field.value, subst, representatives),
                    optional: field.optional,
                })
                .collect(),
        })
        .collect();
    let variants = ty
        .variants
        .iter()
        .map(|variant| CompactVariant {
            items: variant
                .items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| rewrite_compact_type(payload, subst, representatives))
                            .collect(),
                    )
                })
                .collect(),
        })
        .collect();
    let tuples = ty
        .tuples
        .iter()
        .map(|tuple| {
            tuple
                .iter()
                .map(|item| rewrite_compact_type(item, subst, representatives))
                .collect()
        })
        .collect();
    let rows = ty
        .rows
        .iter()
        .map(|row| CompactRow {
            items: row
                .items
                .iter()
                .map(|item| rewrite_compact_type(item, subst, representatives))
                .collect(),
            tail: Box::new(rewrite_compact_type(&row.tail, subst, representatives)),
        })
        .collect();
    let rewritten = CompactType {
        vars,
        prims: ty.prims.clone(),
        cons,
        funs,
        records,
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| crate::simplify::compact::CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_compact_type(&field.value, subst, representatives),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(rewrite_compact_type(&spread.tail, subst, representatives)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        variants,
        tuples,
        rows,
    };
    merge_compact_types(true, rewritten, representative_parts)
}

enum VarRewrite {
    Keep(TypeVar),
    Representative(CompactType),
    Remove,
}

fn rewrite_var_with_representative(
    tv: TypeVar,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> VarRewrite {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(next) = subst.get(&cur) {
        if let Some(representative) = representatives
            .get(&cur)
            .or_else(|| representatives.get(&tv))
            .cloned()
        {
            return VarRewrite::Representative(representative);
        }
        if !seen.insert(cur) {
            break;
        }
        match *next {
            Some(next) if next != cur => cur = next,
            Some(_) => break,
            None => {
                return representatives
                    .get(&tv)
                    .cloned()
                    .map(VarRewrite::Representative)
                    .unwrap_or(VarRewrite::Remove);
            }
        }
    }
    representatives
        .get(&cur)
        .or_else(|| representatives.get(&tv))
        .cloned()
        .map(VarRewrite::Representative)
        .unwrap_or(VarRewrite::Keep(cur))
}

fn rewrite_var(tv: TypeVar, subst: &HashMap<TypeVar, Option<TypeVar>>) -> Option<TypeVar> {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(next) = subst.get(&cur) {
        if !seen.insert(cur) {
            break;
        }
        match *next {
            Some(next) if next != cur => cur = next,
            Some(_) => break,
            None => return None,
        }
    }
    Some(cur)
}

pub(crate) fn is_effectively_recursive(
    tv: TypeVar,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
) -> bool {
    rec_vars
        .get(&tv)
        .is_some_and(|bounds| !is_trivial_self_bounds(tv, bounds))
}

fn is_trivial_self_bounds(tv: TypeVar, bounds: &CompactBounds) -> bool {
    (is_empty_compact_type(&bounds.lower) && is_only_self_var(&bounds.upper, tv))
        || (is_only_self_var(&bounds.lower, tv) && is_empty_compact_type(&bounds.upper))
}

fn is_only_self_var(ty: &CompactType, tv: TypeVar) -> bool {
    ty.vars.len() == 1
        && ty.vars.contains(&tv)
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

pub(crate) fn has_matching_polar_signature(
    analysis: &CoOccurrences,
    lhs: TypeVar,
    rhs: TypeVar,
) -> bool {
    matching_occurrence_side(&analysis.positive, lhs, rhs)
        || matching_occurrence_side(&analysis.negative, lhs, rhs)
}

fn matching_occurrence_side(
    map: &HashMap<TypeVar, HashSet<AlongItem>>,
    lhs: TypeVar,
    rhs: TypeVar,
) -> bool {
    let Some(lhs_occurs) = map.get(&lhs) else {
        return false;
    };
    let Some(rhs_occurs) = map.get(&rhs) else {
        return false;
    };
    !lhs_occurs.is_empty() && lhs_occurs == rhs_occurs
}

fn exact_occurrences(analysis: &CoOccurrences, positive: bool, tv: TypeVar) -> HashSet<ExactKey> {
    let occurs = if positive {
        analysis.positive.get(&tv)
    } else {
        analysis.negative.get(&tv)
    };
    let Some(occurs) = occurs else {
        return HashSet::new();
    };
    occurs
        .iter()
        .filter_map(|item| match item {
            AlongItem::Exact(exact) => Some(*exact),
            AlongItem::Var(_) => None,
        })
        .collect()
}

impl ExactInfo {
    fn from_analysis(analysis: &CoOccurrences) -> Self {
        let mut info = Self::default();
        let all_vars = analysis
            .positive
            .keys()
            .chain(analysis.negative.keys())
            .copied()
            .collect::<HashSet<_>>();
        for tv in all_vars {
            let positive = exact_occurrences(analysis, true, tv);
            let negative = exact_occurrences(analysis, false, tv);
            if positive
                .iter()
                .chain(negative.iter())
                .any(|exact| exact.kind == ExactKeyKind::ConcreteRow)
            {
                info.has_concrete_row.insert(tv);
            }
            let mut positive_key = positive.iter().cloned().collect::<Vec<_>>();
            positive_key.sort();
            let mut negative_key = negative.iter().cloned().collect::<Vec<_>>();
            negative_key.sort();
            info.signatures.insert(
                tv,
                ExactSignature {
                    positive: positive_key,
                    negative: negative_key,
                },
            );
            info.positive.insert(tv, positive);
            info.negative.insert(tv, negative);
        }
        info
    }

    pub(super) fn signature(&self, tv: TypeVar) -> ExactSignature {
        self.signatures.get(&tv).cloned().unwrap_or_default()
    }

    pub(super) fn exact_occurrences(
        &self,
        positive: bool,
        tv: TypeVar,
    ) -> Option<&HashSet<ExactKey>> {
        let map = if positive {
            &self.positive
        } else {
            &self.negative
        };
        map.get(&tv)
    }

    pub(super) fn has_concrete_row(&self, tv: TypeVar) -> bool {
        self.has_concrete_row.contains(&tv)
    }
}

pub(super) fn exact_key_from_hash(kind: ExactKeyKind, value: impl Hash) -> ExactKey {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    ExactKey {
        digest: hasher.finish(),
        kind,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::{
        AlongItem, ExactKeyKind, analyze_co_occurrences,
        analyze_group_co_occurrences_with_role_constraints, coalesce_by_co_occurrence,
        coalesce_by_co_occurrence_with_role_constraints_report,
        coalesce_by_co_occurrence_with_role_constraints_report_inner, exact_occurrences,
    };
    use crate::fresh_type_var;
    use crate::simplify::compact::merge_compact_types;
    use crate::simplify::compact::{
        CompactBounds, CompactCon, CompactRecordSpread, CompactRow, CompactType, CompactTypeScheme,
    };
    use crate::symbols::{Name, Path};
    use crate::types::RecordField;

    #[test]
    fn analyze_co_occurrences_collects_positive_group() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a, b]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert_eq!(
            analysis.positive[&a],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
        assert_eq!(
            analysis.positive[&b],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
    }

    #[test]
    fn analyze_co_occurrences_collects_exact_along_items() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(analysis.positive[&a].iter().any(
            |item| matches!(item, AlongItem::Exact(exact) if exact.kind == ExactKeyKind::Other)
        ));
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_same_signature_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(coalesced.cty.lower.funs[0].arg.vars.len(), 1);
        assert_eq!(coalesced.cty.lower.funs[0].ret.vars.len(), 1);

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&b), Some(&Some(a)));
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&a), Some(&None));
    }

    #[test]
    fn coalesce_report_records_lower_representative_for_removed_var() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&a), Some(&None));
        assert_eq!(
            report.rounds[0].representatives.get(&a),
            Some(&CompactType {
                prims: HashSet::from([int_path]),
                ..CompactType::default()
            })
        );
    }

    #[test]
    fn coalesce_rewrites_removed_var_to_lower_representative() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced =
            coalesce_by_co_occurrence_with_role_constraints_report_inner(&scheme, &[], true).scheme;
        assert!(coalesced.cty.lower.vars.is_empty());
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(
            coalesced.cty.lower.funs[0].ret,
            CompactType {
                prims: HashSet::from([int_path]),
                ..CompactType::default()
            }
        );
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].arg.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_effect_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].ret_eff.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_effect_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].arg_eff.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_effect_arg_type_vars() {
        let a = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![CompactType {
                                    cons: vec![CompactCon {
                                        path: eff_path,
                                        args: vec![CompactBounds {
                                            self_var: None,
                                            lower: CompactType {
                                                vars: HashSet::from([a]),
                                                ..CompactType::default()
                                            },
                                            upper: CompactType::default(),
                                        }],
                                    }],
                                    ..CompactType::default()
                                }],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.funs[0].arg_eff.rows[0].items[0].cons[0].args[0];
        assert!(arg.lower.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_effect_arg_type_vars() {
        let a = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![CompactType {
                                    cons: vec![CompactCon {
                                        path: eff_path,
                                        args: vec![CompactBounds {
                                            self_var: None,
                                            lower: CompactType::default(),
                                            upper: CompactType {
                                                vars: HashSet::from([a]),
                                                ..CompactType::default()
                                            },
                                        }],
                                    }],
                                    ..CompactType::default()
                                }],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.funs[0].arg_eff.rows[0].items[0].cons[0].args[0];
        assert!(arg.upper.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_primitive_sandwich() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
    }

    #[test]
    fn analyze_co_occurrences_tracks_root_upper_along_items() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType::default(),
                upper: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert_eq!(
            analysis.negative[&a],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
        assert_eq!(
            analysis.negative[&b],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
    }

    #[test]
    fn analyze_co_occurrences_ignores_root_upper_direct_vars() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType::default(),
                upper: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(!analysis.negative.contains_key(&a));
        assert!(exact_occurrences(&analysis, false, a).is_empty());
    }

    #[test]
    fn analyze_group_co_occurrences_ignores_root_upper_direct_vars() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType::default(),
                upper: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_group_co_occurrences_with_role_constraints(&scheme, &[]);
        assert!(!analysis.types.contains_key(&a));
        assert!(!analysis.effect_types.contains_key(&a));
        assert!(!analysis.effects.contains_key(&a));
    }

    #[test]
    fn analyze_co_occurrences_tracks_record_spread_tail_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    record_spreads: vec![CompactRecordSpread {
                        fields: vec![RecordField::required(
                            Name("x".to_string()),
                            CompactType::default(),
                        )],
                        tail: Box::new(CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        }),
                        tail_wins: true,
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(
            analysis.positive.contains_key(&a),
            "record spread tail vars should participate in positive co-occurrence analysis",
        );
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_function_sandwich() {
        let a = fresh_type_var();
        let fun = crate::simplify::compact::CompactFun {
            arg: CompactType::default(),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: CompactType::default(),
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    funs: vec![fun.clone()],
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    funs: vec![fun],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(coalesced.cty.upper.funs.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_exact_row_sandwich() {
        let a = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let row = CompactType {
            rows: vec![CompactRow {
                items: vec![CompactType {
                    prims: HashSet::from([io_path]),
                    ..CompactType::default()
                }],
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    rows: row.rows.clone(),
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    rows: row.rows,
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.rows.len(), 1);
        assert_eq!(coalesced.cty.upper.rows.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_record_spread_sandwich() {
        let a = fresh_type_var();
        let spread = CompactRecordSpread {
            fields: vec![RecordField::required(
                Name("x".to_string()),
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
            )],
            tail: Box::new(CompactType::default()),
            tail_wins: true,
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    record_spreads: vec![spread.clone()],
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    record_spreads: vec![spread],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.record_spreads.len(), 1);
        assert_eq!(coalesced.cty.upper.record_spreads.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_nested_constructor_arg_sandwich() {
        let a = fresh_type_var();
        let opt_path = Path {
            segments: vec![Name("opt".to_string())],
        };
        let tuple_payload = CompactType {
            tuples: vec![vec![
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
            ]],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    cons: vec![CompactCon {
                        path: opt_path.clone(),
                        args: vec![CompactBounds {
                            self_var: None,
                            lower: merge_compact_types(
                                true,
                                CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                tuple_payload.clone(),
                            ),
                            upper: merge_compact_types(
                                false,
                                CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                tuple_payload.clone(),
                            ),
                        }],
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.cons[0].args[0];
        assert!(arg.lower.vars.is_empty());
        assert!(arg.upper.vars.is_empty());
        assert_eq!(arg.lower.tuples.len(), 1);
        assert_eq!(arg.upper.tuples.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_coalesces_effect_atom_interval_with_direct_arg() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let ref_path = Path {
            segments: vec![Name("ref".to_string())],
        };
        let var_path = Path {
            segments: vec![Name("var".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    cons: vec![CompactCon {
                        path: ref_path,
                        args: vec![
                            CompactBounds {
                                self_var: None,
                                lower: CompactType {
                                    rows: vec![CompactRow {
                                        items: vec![CompactType {
                                            cons: vec![CompactCon {
                                                path: var_path,
                                                args: vec![CompactBounds {
                                                    self_var: None,
                                                    lower: CompactType {
                                                        vars: HashSet::from([a, b]),
                                                        ..CompactType::default()
                                                    },
                                                    upper: CompactType {
                                                        vars: HashSet::from([a, b]),
                                                        ..CompactType::default()
                                                    },
                                                }],
                                            }],
                                            ..CompactType::default()
                                        }],
                                        tail: Box::new(CompactType::default()),
                                    }],
                                    ..CompactType::default()
                                },
                                upper: CompactType::default(),
                            },
                            CompactBounds {
                                self_var: None,
                                lower: CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                upper: CompactType {
                                    vars: HashSet::from([b]),
                                    ..CompactType::default()
                                },
                            },
                        ],
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let con = &coalesced.cty.lower.cons[0];
        let row_item_con = &con.args[0].lower.rows[0].items[0].cons[0];
        assert_eq!(row_item_con.args[0].lower.vars, HashSet::from([a]));
        assert_eq!(row_item_con.args[0].upper.vars, HashSet::from([a]));
        assert_eq!(con.args[1].lower.vars, HashSet::from([a]));
        assert_eq!(con.args[1].upper.vars, HashSet::from([a]));
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_indistinguishable_effect_arg_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let effect_item = |tv| CompactType {
            cons: vec![CompactCon {
                path: eff_path.clone(),
                args: vec![CompactBounds {
                    self_var: None,
                    lower: CompactType {
                        vars: HashSet::from([tv]),
                        ..CompactType::default()
                    },
                    upper: CompactType {
                        vars: HashSet::from([tv]),
                        ..CompactType::default()
                    },
                }],
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![effect_item(a), effect_item(b)],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![effect_item(a), effect_item(b)],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        let arg_items = &fun.arg_eff.rows[0].items;
        let ret_items = &fun.ret_eff.rows[0].items;
        for item in arg_items.iter().chain(ret_items.iter()) {
            let vars = &item.cons[0].args[0].lower.vars;
            assert_eq!(vars.len(), 1);
            assert_eq!(*vars.iter().next().unwrap(), a);
            let upper_vars = &item.cons[0].args[0].upper.vars;
            assert_eq!(upper_vars.len(), 1);
            assert_eq!(*upper_vars.iter().next().unwrap(), a);
        }
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_indistinguishable_effect_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        assert_eq!(fun.arg_eff.vars.len(), 1);
        assert_eq!(fun.ret_eff.vars.len(), 1);
        assert_eq!(fun.arg_eff.vars, fun.ret_eff.vars);
    }
}
