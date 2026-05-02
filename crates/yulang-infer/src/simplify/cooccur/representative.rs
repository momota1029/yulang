use std::collections::{HashMap, HashSet};

use super::{CompactRoleConstraint, is_empty_compact_type};
use crate::ids::TypeVar;
use crate::simplify::compact::{
    CompactBounds, CompactType, CompactTypeScheme, merge_compact_types,
};

pub(super) fn lower_representatives_for_subst(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> HashMap<TypeVar, CompactType> {
    let candidates = collect_lower_representatives(scheme, constraints, rec_vars);
    let mut representatives = HashMap::new();
    let mut vars = subst.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    for var in vars {
        let representative = matches!(subst.get(&var), Some(None))
            .then(|| candidates.get(&var).cloned())
            .flatten();
        if let Some(representative) = representative
            && !is_empty_compact_type(&representative)
        {
            representatives.insert(var, representative);
        }
    }
    representatives
}

fn collect_lower_representatives(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    rec_vars: &HashMap<TypeVar, CompactBounds>,
) -> HashMap<TypeVar, CompactType> {
    let mut ctx = RepresentativeContext {
        scheme,
        rec_vars,
        out: HashMap::new(),
        expanded: HashSet::new(),
    };
    ctx.collect_bounds(&scheme.cty);
    for constraint in constraints {
        for arg in &constraint.args {
            ctx.collect_bounds(arg);
        }
    }
    ctx.out
}

struct RepresentativeContext<'a> {
    scheme: &'a CompactTypeScheme,
    rec_vars: &'a HashMap<TypeVar, CompactBounds>,
    out: HashMap<TypeVar, CompactType>,
    expanded: HashSet<(TypeVar, bool)>,
}

impl RepresentativeContext<'_> {
    fn collect_bounds(&mut self, bounds: &CompactBounds) {
        self.collect_type(&bounds.lower, true);
        self.collect_type(&bounds.upper, false);
    }

    fn collect_type(&mut self, ty: &CompactType, positive: bool) {
        if positive {
            let representative = concrete_representative_part(ty);
            if !is_empty_compact_type(&representative) {
                for &tv in &ty.vars {
                    self.add_representative(tv, representative.clone());
                }
            }
        }

        for &tv in &ty.vars {
            if self.expanded.insert((tv, positive))
                && let Some(bounds) = self
                    .scheme
                    .rec_vars
                    .get(&tv)
                    .or_else(|| self.rec_vars.get(&tv))
            {
                let side = if positive {
                    &bounds.lower
                } else {
                    &bounds.upper
                };
                self.collect_type(side, positive);
            }
        }

        self.collect_type_children(ty, positive);
    }

    fn collect_type_children(&mut self, ty: &CompactType, positive: bool) {
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_bounds(arg);
            }
        }
        for fun in &ty.funs {
            self.collect_type(&fun.arg, !positive);
            self.collect_type(&fun.arg_eff, !positive);
            self.collect_type(&fun.ret_eff, positive);
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
            self.collect_type(&row.tail, positive);
        }
    }

    fn add_representative(&mut self, tv: TypeVar, representative: CompactType) {
        self.out
            .entry(tv)
            .and_modify(|existing| {
                *existing = merge_compact_types(true, existing.clone(), representative.clone());
            })
            .or_insert(representative);
    }
}

fn concrete_representative_part(ty: &CompactType) -> CompactType {
    CompactType {
        vars: HashSet::new(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .filter(|con| con.args.iter().all(|arg| !bounds_contains_vars(arg)))
            .cloned()
            .collect(),
        funs: ty
            .funs
            .iter()
            .filter(|fun| {
                !type_contains_vars(&fun.arg)
                    && !type_contains_vars(&fun.arg_eff)
                    && !type_contains_vars(&fun.ret_eff)
                    && !type_contains_vars(&fun.ret)
            })
            .cloned()
            .collect(),
        records: ty
            .records
            .iter()
            .filter(|record| {
                record
                    .fields
                    .iter()
                    .all(|field| !type_contains_vars(&field.value))
            })
            .cloned()
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .filter(|spread| {
                spread
                    .fields
                    .iter()
                    .all(|field| !type_contains_vars(&field.value))
                    && !type_contains_vars(&spread.tail)
            })
            .cloned()
            .collect(),
        variants: ty
            .variants
            .iter()
            .filter(|variant| {
                variant
                    .items
                    .iter()
                    .flat_map(|(_, payloads)| payloads)
                    .all(|payload| !type_contains_vars(payload))
            })
            .cloned()
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .filter(|tuple| tuple.iter().all(|item| !type_contains_vars(item)))
            .cloned()
            .collect(),
        rows: ty
            .rows
            .iter()
            .filter(|row| {
                row.items.iter().all(|item| !type_contains_vars(item))
                    && !type_contains_vars(&row.tail)
            })
            .cloned()
            .collect(),
    }
}

fn bounds_contains_vars(bounds: &CompactBounds) -> bool {
    bounds.self_var.is_some()
        || type_contains_vars(&bounds.lower)
        || type_contains_vars(&bounds.upper)
}

fn type_contains_vars(ty: &CompactType) -> bool {
    if !ty.vars.is_empty() {
        return true;
    }
    ty.cons
        .iter()
        .any(|con| con.args.iter().any(bounds_contains_vars))
        || ty.funs.iter().any(|fun| {
            type_contains_vars(&fun.arg)
                || type_contains_vars(&fun.arg_eff)
                || type_contains_vars(&fun.ret_eff)
                || type_contains_vars(&fun.ret)
        })
        || ty.records.iter().any(|record| {
            record
                .fields
                .iter()
                .any(|field| type_contains_vars(&field.value))
        })
        || ty.record_spreads.iter().any(|spread| {
            spread
                .fields
                .iter()
                .any(|field| type_contains_vars(&field.value))
                || type_contains_vars(&spread.tail)
        })
        || ty.variants.iter().any(|variant| {
            variant
                .items
                .iter()
                .flat_map(|(_, payloads)| payloads)
                .any(type_contains_vars)
        })
        || ty
            .tuples
            .iter()
            .any(|tuple| tuple.iter().any(type_contains_vars))
        || ty
            .rows
            .iter()
            .any(|row| row.items.iter().any(type_contains_vars) || type_contains_vars(&row.tail))
}
