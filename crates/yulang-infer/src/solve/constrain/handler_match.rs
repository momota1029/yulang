use std::fmt::Write as _;

use rustc_hash::FxHashSet;

use super::{Infer, StepCache};
use crate::diagnostic::{ConstraintCause, TypeOrigin};
use crate::ids::{NegId, PosId, TypeVar};
use crate::simplify::compact::{
    CompactBounds, CompactType, CompactTypeScheme,
    coalesce_nested_tail_function_effect_residuals_in_scheme, compact_neg_expr, compact_pos_expr,
    compact_type_var,
};
use crate::simplify::cooccur::coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars;
use crate::solve::{
    EffectSubtractability, HandlerMatchEdge, ShiftKeep, effect_atom_families_overlap,
};
use crate::types::EffectAtom;
use crate::types::{Neg, Pos};

const MISSING_SUBTRACTABILITY_COMPACT_LIMIT: usize = 4;
const MISSING_SUBTRACTABILITY_ORIGIN_LIMIT: usize = 32;
const FULL_MISSING_SUBTRACTABILITY_REPORT_ENV: &str = "YULANG_DEBUG_FULL_SUBTRACTABILITY";

impl Infer {
    pub fn record_effect_boundary_keep(&self, effect: TypeVar, keep: ShiftKeep) {
        let mut keeps = self.effect_boundary_keeps.borrow_mut();
        match keeps.get(&effect).cloned() {
            Some(existing) => {
                keeps.insert(effect, merge_shift_keep(existing, keep));
            }
            None => {
                if keep != ShiftKeep::Surface {
                    keeps.insert(effect, keep);
                }
            }
        }
    }

    pub fn effect_boundary_keep(&self, effect: TypeVar) -> ShiftKeep {
        self.effect_boundary_keeps
            .borrow()
            .get(&effect)
            .cloned()
            .unwrap_or(ShiftKeep::Surface)
    }

    pub fn record_effect_subtractability(
        &self,
        effect: TypeVar,
        subtractability: EffectSubtractability,
    ) {
        let mut subtractables = self.effect_subtractables.borrow_mut();
        match subtractables.get(&effect).cloned() {
            Some(existing) => {
                subtractables.insert(
                    effect,
                    merge_effect_subtractability(existing, subtractability),
                );
            }
            None => {
                subtractables.insert(effect, subtractability);
            }
        }
    }

    pub fn effect_subtractability(&self, effect: TypeVar) -> Option<EffectSubtractability> {
        self.effect_subtractables.borrow().get(&effect).cloned()
    }

    pub fn require_effect_subtractability(
        &self,
        effect: TypeVar,
        context: &'static str,
    ) -> EffectSubtractability {
        self.effect_subtractability(effect).unwrap_or_else(|| {
            panic!(
                "{}",
                self.missing_effect_subtractability_report(effect, context)
            )
        })
    }

    fn missing_effect_subtractability_report(
        &self,
        effect: TypeVar,
        context: &'static str,
    ) -> String {
        let scheme = compact_type_var(self, effect);
        let lower_refs = self.lower_refs_of(effect);
        let upper_refs = self.upper_refs_of(effect);
        let lower_compacts = lower_refs
            .iter()
            .copied()
            .map(|lower| compact_pos_expr(self, lower))
            .collect::<Vec<_>>();
        let upper_compacts = upper_refs
            .iter()
            .copied()
            .map(|upper| compact_neg_expr(self, upper))
            .collect::<Vec<_>>();

        let (coalesced_ignore_levels, exposed_tail_vars) =
            coalesce_missing_subtractability_scheme_ignore_levels(&scheme);

        let mut vars = FxHashSet::default();
        collect_compact_bounds_vars(&scheme.cty, &mut vars);
        for bounds in scheme.rec_vars.values() {
            collect_compact_bounds_vars(bounds, &mut vars);
        }
        collect_compact_bounds_vars(&coalesced_ignore_levels.cty, &mut vars);
        for bounds in coalesced_ignore_levels.rec_vars.values() {
            collect_compact_bounds_vars(bounds, &mut vars);
        }
        vars.extend(exposed_tail_vars.iter().copied());
        for lower in &lower_compacts {
            collect_compact_type_vars(lower, &mut vars);
        }
        for upper in &upper_compacts {
            collect_compact_type_vars(upper, &mut vars);
        }

        let mut origin_vars = vars
            .into_iter()
            .filter_map(|tv| self.origin_of(tv).map(|origin| (tv, origin)))
            .collect::<Vec<_>>();
        origin_vars.sort_by_key(|(tv, _)| tv.0);
        let origin_count = origin_vars.len();
        origin_vars.truncate(MISSING_SUBTRACTABILITY_ORIGIN_LIMIT);

        let full_report = std::env::var_os(FULL_MISSING_SUBTRACTABILITY_REPORT_ENV).is_some();
        let mut report = String::new();
        let _ = writeln!(
            report,
            "missing effect subtractability for {effect:?} while {context}"
        );
        if let Some(origin) = self.origin_of(effect) {
            let _ = writeln!(
                report,
                "direct_origin: {}",
                format_origin_var(self, effect, &origin)
            );
        } else {
            let _ = writeln!(report, "direct_origin: none");
        }
        let _ = writeln!(
            report,
            "direct_bound_counts: lower={}, upper={}",
            lower_refs.len(),
            upper_refs.len()
        );
        let _ = writeln!(
            report,
            "coalesced_ignore_levels_type: {}",
            crate::display::format_coalesced_scheme(&coalesced_ignore_levels)
        );
        let _ = writeln!(
            report,
            "coalesced_ignore_levels_compact: {}",
            crate::display::format_compact_scheme(&coalesced_ignore_levels)
        );
        let _ = writeln!(
            report,
            "coalesced_ignore_levels_exposed_tail_vars: {:?}",
            sorted_type_vars(exposed_tail_vars.iter().copied())
        );
        let _ = writeln!(
            report,
            "compact_lower_from_variable: {}",
            format_compact_type_sample(&scheme.cty.lower, true)
        );
        let _ = writeln!(
            report,
            "compact_upper_from_variable: {}",
            format_compact_type_sample(&scheme.cty.upper, false)
        );
        let _ = writeln!(
            report,
            "recursive_compact_var_count: {}",
            scheme.rec_vars.len()
        );
        push_compact_type_samples(
            &mut report,
            "lower_compacts_from_direct_lowers",
            &lower_compacts,
            MISSING_SUBTRACTABILITY_COMPACT_LIMIT,
            true,
        );

        if full_report {
            push_compact_type_samples(
                &mut report,
                "upper_compacts_from_direct_uppers",
                &upper_compacts,
                usize::MAX,
                false,
            );
            let _ = writeln!(report, "compact_scheme_for_variable: {scheme:#?}");
        } else {
            let _ = writeln!(
                report,
                "upper_compacts_from_direct_uppers: hidden; set {FULL_MISSING_SUBTRACTABILITY_REPORT_ENV}=1 for full report"
            );
        }

        let _ = writeln!(
            report,
            "compact_origin_vars: showing {}/{}",
            origin_vars.len(),
            origin_count
        );
        for (tv, origin) in &origin_vars {
            let _ = writeln!(report, "  {}", format_origin_var(self, *tv, origin));
        }
        report
    }

    pub fn copy_effect_subtractability(&self, from: TypeVar, to: TypeVar) {
        if let Some(subtractability) = self.effect_subtractability(from) {
            self.record_effect_subtractability(to, subtractability);
        }
    }

    pub fn record_handler_match(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        cause: ConstraintCause,
    ) {
        self.record_handler_match_inner(actual, handled, residual, false, cause);
    }

    pub fn record_open_handler_match(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        cause: ConstraintCause,
    ) {
        self.record_handler_match_inner(actual, handled, residual, true, cause);
    }

    fn record_handler_match_inner(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        solve_open_rows: bool,
        cause: ConstraintCause,
    ) {
        let keep = self.effect_boundary_keep(actual);
        let mut cache = StepCache::default();
        let index = {
            let mut edges = self.handler_matches.borrow_mut();
            let index = edges.len();
            edges.push(HandlerMatchEdge {
                actual,
                keep,
                handled,
                residual,
                solve_open_rows,
                cause: cause.clone(),
            });
            index
        };
        self.record_handler_match_dependent(actual, index);
        self.solve_handler_matches_for(actual, &cause, &mut cache);
    }

    pub(super) fn solve_handler_matches_for(
        &self,
        actual: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let indices = self
            .handler_match_dependents
            .borrow()
            .get(&actual)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();

        for index in indices {
            let Some(edge) = self.handler_matches.borrow().get(index).cloned() else {
                continue;
            };
            let mut seen = FxHashSet::default();
            self.solve_handler_match_var(index, actual, &edge, cause, cache, &mut seen);
        }
    }

    fn record_handler_match_dependent(&self, actual: TypeVar, index: usize) {
        let mut dependents = self.handler_match_dependents.borrow_mut();
        let entry = dependents.entry(actual).or_default();
        if !entry.contains(&index) {
            entry.push(index);
        }
    }

    fn solve_handler_match_var(
        &self,
        index: usize,
        actual: TypeVar,
        edge: &HandlerMatchEdge,
        cause: &ConstraintCause,
        cache: &mut StepCache,
        seen: &mut FxHashSet<TypeVar>,
    ) {
        if !seen.insert(actual) {
            return;
        }

        for lower in self.lower_refs_of(actual) {
            self.solve_handler_match_lower(index, lower, edge, cause, cache, seen);
        }
        for instance in self.compact_lower_instances_of(actual) {
            let lower = self.materialize_compact_lower_instance(&instance);
            self.solve_handler_match_lower(index, lower, edge, cause, cache, seen);
        }
    }

    fn solve_handler_match_lower(
        &self,
        index: usize,
        lower: PosId,
        edge: &HandlerMatchEdge,
        cause: &ConstraintCause,
        cache: &mut StepCache,
        seen: &mut FxHashSet<TypeVar>,
    ) {
        match self.arena.get_pos(lower).clone() {
            Pos::Var(source) | Pos::Raw(source) => {
                self.record_handler_match_dependent(source, index);
                self.solve_handler_match_var(index, source, edge, cause, cache, seen);
                if edge.solve_open_rows && source != edge.actual && self.is_through(source) {
                    self.constrain_step(
                        self.arena.alloc_pos(Pos::Var(source)),
                        self.arena.alloc_neg(Neg::Var(edge.residual)),
                        cause,
                        cache,
                    );
                }
            }
            Pos::Union(left, right) => {
                self.solve_handler_match_lower(index, left, edge, cause, cache, seen);
                self.solve_handler_match_lower(index, right, edge, cause, cache, seen);
            }
            Pos::Atom(_) => {
                self.solve_handler_match_row(vec![lower], self.arena.bot, edge, cause, cache);
            }
            Pos::Row(items, tail) => {
                self.solve_handler_match_row(items, tail, edge, cause, cache);
            }
            _ => {}
        }
    }

    fn solve_handler_match_row(
        &self,
        items: Vec<PosId>,
        tail: PosId,
        edge: &HandlerMatchEdge,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let mut unmatched = items;
        for handled in &edge.handled {
            let Some(index) = unmatched
                .iter()
                .position(|item| self.handler_match_row_items_match(*item, *handled))
            else {
                continue;
            };
            let matched = unmatched.remove(index);
            self.constrain_row_item_match(matched, *handled, cause, cache);
        }

        let include_open_tail = edge.solve_open_rows;
        let residual = self.handler_match_residual_lower(unmatched, tail, include_open_tail);
        if let Some(residual) = residual {
            self.constrain_step(
                residual,
                self.arena.alloc_neg(Neg::Var(edge.residual)),
                cause,
                cache,
            );
        }
    }

    fn handler_match_residual_lower(
        &self,
        unmatched: Vec<PosId>,
        tail: PosId,
        include_open_tail: bool,
    ) -> Option<PosId> {
        let tail_is_empty = self.pos_tail_is_empty_row(tail);
        if unmatched.is_empty() {
            return (!tail_is_empty && include_open_tail).then_some(tail);
        }

        let tail = if include_open_tail && !tail_is_empty {
            tail
        } else {
            self.arena.bot
        };
        Some(self.pos_effect_union(unmatched, tail))
    }

    fn pos_tail_is_empty_row(&self, tail: PosId) -> bool {
        self.pos_effect_lower_is_empty(tail)
    }

    fn handler_match_row_items_match(&self, pos: PosId, neg: NegId) -> bool {
        match (self.arena.get_pos(pos), self.arena.get_neg(neg)) {
            (Pos::Atom(pos_atom), Neg::Atom(neg_atom)) => {
                pos_atom.path == neg_atom.path && pos_atom.args.len() == neg_atom.args.len()
            }
            (Pos::Var(pos), Neg::Var(neg)) => pos == neg,
            (Pos::Bot, Neg::Top) => true,
            _ => false,
        }
    }
}

fn coalesce_missing_subtractability_scheme_ignore_levels(
    scheme: &CompactTypeScheme,
) -> (CompactTypeScheme, std::collections::HashSet<TypeVar>) {
    let mut scheme = scheme.clone();
    let exposed_tail_vars = coalesce_nested_tail_function_effect_residuals_in_scheme(&mut scheme);
    let (scheme, _) = coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars(
        &scheme,
        &[],
        |_| None,
        &exposed_tail_vars,
    );
    (scheme, exposed_tail_vars)
}

fn collect_compact_bounds_vars(bounds: &CompactBounds, out: &mut FxHashSet<TypeVar>) {
    collect_compact_type_vars(&bounds.lower, out);
    collect_compact_type_vars(&bounds.upper, out);
}

fn collect_compact_type_vars(ty: &CompactType, out: &mut FxHashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_vars(&fun.arg, out);
        collect_compact_type_vars(&fun.arg_eff, out);
        collect_compact_type_vars(&fun.ret_eff, out);
        collect_compact_type_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_vars(&field.value, out);
        }
        collect_compact_type_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_vars(item, out);
        }
        collect_compact_type_vars(&row.tail, out);
    }
}

fn sorted_type_vars(vars: impl IntoIterator<Item = TypeVar>) -> Vec<TypeVar> {
    let mut vars = vars.into_iter().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars
}

fn format_origin_var(infer: &Infer, tv: TypeVar, origin: &TypeOrigin) -> String {
    let label = origin.label.as_deref().unwrap_or("-");
    let source = match origin.file_span {
        Some(file_span) => match infer.file_info(file_span.file) {
            Some(info) => format!(
                "{}:{:?} ({:?})",
                info.path.display(),
                file_span.range,
                info.origin
            ),
            None => format!("FileId({}):{:?}", file_span.file.0, file_span.range),
        },
        None => match origin.span {
            Some(span) => format!("span {span:?}"),
            None => "no source span".to_string(),
        },
    };
    format!(
        "{tv:?}: kind={:?}, label={label:?}, source={source}",
        origin.kind
    )
}

fn push_compact_type_samples(
    report: &mut String,
    label: &str,
    items: &[CompactType],
    limit: usize,
    positive: bool,
) {
    let shown = items.len().min(limit);
    let _ = writeln!(report, "{label}: showing {shown}/{}", items.len());
    for (idx, item) in items.iter().take(limit).enumerate() {
        let _ = writeln!(
            report,
            "{label}[{idx}]: {}",
            format_compact_type_sample(item, positive)
        );
    }
}

fn format_compact_type_sample(ty: &CompactType, positive: bool) -> String {
    let rec_vars = std::collections::HashMap::new();
    let ty = crate::display::format::compact_side_to_type(&rec_vars, ty, positive);
    crate::display::format_type(&ty)
}

fn merge_shift_keep(existing: ShiftKeep, incoming: ShiftKeep) -> ShiftKeep {
    match (existing, incoming) {
        (ShiftKeep::CallBoundary, _) | (_, ShiftKeep::CallBoundary) => ShiftKeep::CallBoundary,
        (ShiftKeep::None, _) | (_, ShiftKeep::None) => ShiftKeep::None,
        (ShiftKeep::Surface, keep) | (keep, ShiftKeep::Surface) => keep,
        (ShiftKeep::Set(mut lhs), ShiftKeep::Set(rhs)) => {
            for path in rhs {
                if !lhs.contains(&path) {
                    lhs.push(path);
                }
            }
            ShiftKeep::Set(lhs)
        }
    }
}

fn merge_effect_subtractability(
    existing: EffectSubtractability,
    incoming: EffectSubtractability,
) -> EffectSubtractability {
    match (existing, incoming) {
        (EffectSubtractability::Empty, _) | (_, EffectSubtractability::Empty) => {
            EffectSubtractability::Empty
        }
        (EffectSubtractability::All, keep) | (keep, EffectSubtractability::All) => keep,
        (EffectSubtractability::Set(lhs), EffectSubtractability::Set(rhs)) => {
            EffectSubtractability::set(intersect_atom_families(lhs, &rhs))
        }
        (EffectSubtractability::Set(atoms), EffectSubtractability::AllExcept(excluded))
        | (EffectSubtractability::AllExcept(excluded), EffectSubtractability::Set(atoms)) => {
            EffectSubtractability::set(remove_excluded_atom_families(atoms, &excluded))
        }
        (EffectSubtractability::AllExcept(lhs), EffectSubtractability::AllExcept(rhs)) => {
            EffectSubtractability::all_except(union_atom_families(lhs, rhs))
        }
    }
}

fn intersect_atom_families(lhs: Vec<EffectAtom>, rhs: &[EffectAtom]) -> Vec<EffectAtom> {
    lhs.into_iter()
        .filter(|atom| {
            rhs.iter()
                .any(|rhs| effect_atom_families_overlap(atom, rhs))
        })
        .collect()
}

fn remove_excluded_atom_families(
    atoms: Vec<EffectAtom>,
    excluded: &[EffectAtom],
) -> Vec<EffectAtom> {
    atoms
        .into_iter()
        .filter(|atom| {
            !excluded
                .iter()
                .any(|excluded| effect_atom_families_overlap(atom, excluded))
        })
        .collect()
}

fn union_atom_families(mut lhs: Vec<EffectAtom>, rhs: Vec<EffectAtom>) -> Vec<EffectAtom> {
    for atom in rhs {
        if !lhs
            .iter()
            .any(|existing| effect_atom_families_overlap(existing, &atom))
        {
            lhs.push(atom);
        }
    }
    lhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::ConstraintCause;
    use crate::fresh_type_var;
    use crate::symbols::{Name, Path};
    use crate::types::EffectAtom;

    #[test]
    fn handler_match_subtracts_closed_surface_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.bot,
            ),
            Neg::Var(actual),
        );

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            !has_handler_row_upper(&infer, actual, residual, "io"),
            "handler_match should solve residual rows without adding an ordinary row upper bound"
        );
        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "closed empty residual is represented by bottom, not by a synthetic empty row lower"
        );
    }

    #[test]
    fn handler_match_subtracts_indirect_lower_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let source = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(Pos::Var(source), Neg::Var(actual));
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(source),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            tail_flows_to_residual(&infer, tail, residual),
            "ordinary row constraints should propagate an open tail to the residual"
        );
        assert!(
            !has_handler_row_upper(&infer, source, residual, "io"),
            "handler subtraction should not push handled row uppers back into the source"
        );
    }

    #[test]
    fn handler_match_subtracts_indirect_through_lower_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let source = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.mark_through(tail);
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(source),
        );
        infer.constrain(Pos::Var(source), Neg::Var(actual));

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).into_iter().any(|lower| {
                matches!(infer.arena.get_pos(lower), Pos::Var(open_tail) if open_tail == tail)
            }),
            "handler_match should expose through tails as residual lower bounds"
        );
    }

    #[test]
    fn handler_match_does_not_open_naked_actual_var() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(EffectAtom {
                path: path("io"),
                args: Vec::new(),
            }))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "naked handler_match actual must stay pending"
        );
    }

    #[test]
    fn handler_match_subtracts_open_surface_row_to_tail() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            tail_flows_to_residual(&infer, tail, residual),
            "open surface subtraction should be handled by row decomposition"
        );
    }

    #[test]
    fn handler_match_passes_unhandled_open_row_items_to_residual() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let handled = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        let unhandled = EffectAtom {
            path: path("outer"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(unhandled.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(handled))],
            residual,
            ConstraintCause::unknown(),
        );

        let (has_item, has_tail) =
            infer
                .lower_refs_of(residual)
                .into_iter()
                .fold((false, false), |mut acc, lower| {
                    let lower = pos_effect_contains_item_and_tail(&infer, lower, &unhandled, tail);
                    acc.0 |= lower.0;
                    acc.1 |= lower.1;
                    acc
                });
        assert!(
            has_item && has_tail,
            "open handler_match must pass unhandled row items through to the residual"
        );
    }

    #[test]
    fn handler_match_set_keep_subtracts_captured_path_to_tail() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.record_effect_boundary_keep(actual, ShiftKeep::Set(vec![path("io")]));
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            tail_flows_to_residual(&infer, tail, residual),
            "boundary keep metadata should not change the ordinary row constraint"
        );
        assert!(
            matches!(
                infer.handler_matches.borrow().first().map(|edge| &edge.keep),
                Some(ShiftKeep::Set(paths)) if paths == &vec![path("io")]
            ),
            "boundary keep should remain available as exported evidence"
        );
    }

    #[test]
    fn handler_match_keeps_open_surface_rows_pending_by_default() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "default handler_match should not solve from open surface rows"
        );
    }

    #[test]
    fn handler_match_constrains_atom_args_from_open_rows() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let actual_pos = fresh_type_var();
        let actual_neg = fresh_type_var();
        let handled_pos = fresh_type_var();
        let handled_neg = fresh_type_var();
        let effect_path = path("parse");

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(EffectAtom {
                path: effect_path.clone(),
                args: vec![(handled_pos, handled_neg)],
            }))],
            residual,
            ConstraintCause::unknown(),
        );
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(EffectAtom {
                    path: effect_path,
                    args: vec![(actual_pos, actual_neg)],
                }))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        assert!(
            infer.upper_refs_of(actual_pos).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(tv) if tv == handled_neg)
            }),
            "matched atom args should connect the source pos side to the handler neg side"
        );
        assert!(
            infer.upper_refs_of(handled_pos).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(tv) if tv == actual_neg)
            }),
            "matched atom args should connect the handler pos side to the source neg side"
        );
        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "open surface rows still keep residual subtraction pending by default"
        );
    }

    fn path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }

    fn has_handler_row_upper(
        infer: &Infer,
        actual: crate::ids::TypeVar,
        residual: crate::ids::TypeVar,
        path_name: &str,
    ) -> bool {
        infer.upper_refs_of(actual).into_iter().any(|upper| {
            let Neg::Row(items, tail) = infer.arena.get_neg(upper) else {
                return false;
            };
            matches!(infer.arena.get_neg(tail), Neg::Var(tv) if tv == residual)
                && items.iter().any(|item| {
                    matches!(
                        infer.arena.get_neg(*item),
                        Neg::Atom(atom) if atom.path == path(path_name)
                    )
                })
        })
    }

    fn tail_flows_to_residual(
        infer: &Infer,
        tail: crate::ids::TypeVar,
        residual: crate::ids::TypeVar,
    ) -> bool {
        infer
            .upper_refs_of(tail)
            .into_iter()
            .any(|upper| match infer.arena.get_neg(upper) {
                Neg::Var(tv) => tv == residual,
                Neg::Row(items, row_tail) => {
                    items.is_empty()
                        && matches!(infer.arena.get_neg(row_tail), Neg::Var(tv) if tv == residual)
                }
                _ => false,
            })
    }

    fn pos_effect_contains_item_and_tail(
        infer: &Infer,
        pos: crate::ids::PosId,
        atom: &EffectAtom,
        tail: crate::ids::TypeVar,
    ) -> (bool, bool) {
        match infer.arena.get_pos(pos) {
            Pos::Atom(candidate) => (candidate == *atom, false),
            Pos::Var(tv) | Pos::Raw(tv) => (false, tv == tail),
            Pos::Row(items, row_tail) => {
                let mut out = pos_effect_contains_item_and_tail(infer, row_tail, atom, tail);
                for item in items {
                    let item_out = pos_effect_contains_item_and_tail(infer, item, atom, tail);
                    out.0 |= item_out.0;
                    out.1 |= item_out.1;
                }
                out
            }
            Pos::Union(lhs, rhs) => {
                let lhs = pos_effect_contains_item_and_tail(infer, lhs, atom, tail);
                let rhs = pos_effect_contains_item_and_tail(infer, rhs, atom, tail);
                (lhs.0 || rhs.0, lhs.1 || rhs.1)
            }
            _ => (false, false),
        }
    }
}
