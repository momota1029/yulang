//! Projection-based substitutions for role impl members.
//!
//! Impl member checking records both the actual inferred compact surface and a
//! requirement projection. This module extracts variable substitutions that are
//! structurally justified by matching those two compact shapes.

use poly::types::{RecordField, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{CompactBounds, CompactRoot, CompactType, CompactVarSubstitution};

pub(super) fn role_impl_member_projection_substitutions(
    actual: &CompactRoot,
    projection: &CompactRoot,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = ProjectionSubstitutions::default();
    collect_projection_type_substitutions(&actual.root, &projection.root, &mut substitutions);
    substitutions.finish()
}

#[derive(Default)]
struct ProjectionSubstitutions {
    targets: FxHashMap<TypeVar, TypeVar>,
    conflicts: FxHashSet<TypeVar>,
}

impl ProjectionSubstitutions {
    fn record(&mut self, source: TypeVar, target: TypeVar) {
        if source == target || self.conflicts.contains(&source) {
            return;
        }
        match self.targets.get(&source).copied() {
            Some(existing) if existing != target => {
                self.targets.remove(&source);
                self.conflicts.insert(source);
            }
            Some(_) => {}
            None => {
                self.targets.insert(source, target);
            }
        }
    }

    fn finish(self) -> Vec<CompactVarSubstitution> {
        let mut substitutions = self
            .targets
            .into_iter()
            .filter(|(source, _)| !self.conflicts.contains(source))
            .map(|(source, target)| CompactVarSubstitution {
                source,
                target: Some(target),
            })
            .collect::<Vec<_>>();
        substitutions.sort_by_key(|substitution| substitution.source.0);
        substitutions
    }
}

fn collect_projection_type_substitutions(
    actual: &CompactType,
    projection: &CompactType,
    substitutions: &mut ProjectionSubstitutions,
) {
    if let ([actual], [projection]) = (actual.vars.as_slice(), projection.vars.as_slice()) {
        substitutions.record(actual.var, projection.var);
    }
    for (path, actual_entries) in &actual.cons {
        let Some(projection_entries) = projection.cons.get(path) else {
            continue;
        };
        for (actual, projection) in actual_entries.iter().zip(projection_entries) {
            collect_projection_bounds_substitutions(actual, projection, substitutions);
        }
    }
    for (actual, projection) in actual.funs.iter().zip(&projection.funs) {
        collect_projection_type_substitutions(&actual.arg, &projection.arg, substitutions);
        collect_projection_type_substitutions(&actual.arg_eff, &projection.arg_eff, substitutions);
        collect_projection_type_substitutions(&actual.ret_eff, &projection.ret_eff, substitutions);
        collect_projection_type_substitutions(&actual.ret, &projection.ret, substitutions);
    }
    for (actual, projection) in actual.tuples.iter().zip(&projection.tuples) {
        if actual.items.len() != projection.items.len() {
            continue;
        }
        for (actual, projection) in actual.items.iter().zip(&projection.items) {
            collect_projection_type_substitutions(actual, projection, substitutions);
        }
    }
    for (actual, projection) in actual.records.iter().zip(&projection.records) {
        collect_projection_record_field_substitutions(
            &actual.fields,
            &projection.fields,
            substitutions,
        );
    }
    for (actual, projection) in actual.record_spreads.iter().zip(&projection.record_spreads) {
        collect_projection_record_field_substitutions(
            &actual.fields,
            &projection.fields,
            substitutions,
        );
        collect_projection_type_substitutions(&actual.tail, &projection.tail, substitutions);
    }
    for (actual, projection) in actual.poly_variants.iter().zip(&projection.poly_variants) {
        collect_projection_variant_substitutions(&actual.items, &projection.items, substitutions);
    }
    for (actual, projection) in actual.rows.iter().zip(&projection.rows) {
        for (path, actual_entries) in &actual.items {
            let Some(projection_entries) = projection.items.get(path) else {
                continue;
            };
            for (actual, projection) in actual_entries.iter().zip(projection_entries) {
                collect_projection_bounds_substitutions(actual, projection, substitutions);
            }
        }
        collect_projection_type_substitutions(&actual.tail, &projection.tail, substitutions);
    }
}

fn collect_projection_bounds_substitutions(
    actual: &CompactBounds,
    projection: &CompactBounds,
    substitutions: &mut ProjectionSubstitutions,
) {
    match (actual, projection) {
        (
            CompactBounds::Interval {
                lower: actual_lower,
                upper: actual_upper,
            },
            CompactBounds::Interval {
                lower: projection_lower,
                upper: projection_upper,
            },
        ) => {
            collect_projection_type_substitutions(actual_lower, projection_lower, substitutions);
            collect_projection_type_substitutions(actual_upper, projection_upper, substitutions);
        }
        (
            CompactBounds::Con {
                path: actual_path,
                args: actual_args,
            },
            CompactBounds::Con {
                path: projection_path,
                args: projection_args,
            },
        ) if actual_path == projection_path && actual_args.len() == projection_args.len() => {
            for (actual, projection) in actual_args.iter().zip(projection_args) {
                collect_projection_bounds_substitutions(actual, projection, substitutions);
            }
        }
        (
            CompactBounds::Fun {
                arg: actual_arg,
                arg_eff: actual_arg_eff,
                ret_eff: actual_ret_eff,
                ret: actual_ret,
            },
            CompactBounds::Fun {
                arg: projection_arg,
                arg_eff: projection_arg_eff,
                ret_eff: projection_ret_eff,
                ret: projection_ret,
            },
        ) => {
            collect_projection_bounds_substitutions(actual_arg, projection_arg, substitutions);
            collect_projection_bounds_substitutions(
                actual_arg_eff,
                projection_arg_eff,
                substitutions,
            );
            collect_projection_bounds_substitutions(
                actual_ret_eff,
                projection_ret_eff,
                substitutions,
            );
            collect_projection_bounds_substitutions(actual_ret, projection_ret, substitutions);
        }
        (
            CompactBounds::Record {
                fields: actual_fields,
            },
            CompactBounds::Record {
                fields: projection_fields,
            },
        ) => collect_projection_bound_record_field_substitutions(
            actual_fields,
            projection_fields,
            substitutions,
        ),
        (
            CompactBounds::PolyVariant {
                items: actual_items,
            },
            CompactBounds::PolyVariant {
                items: projection_items,
            },
        ) => collect_projection_bound_variant_substitutions(
            actual_items,
            projection_items,
            substitutions,
        ),
        (
            CompactBounds::Tuple {
                items: actual_items,
            },
            CompactBounds::Tuple {
                items: projection_items,
            },
        ) if actual_items.len() == projection_items.len() => {
            for (actual, projection) in actual_items.iter().zip(projection_items) {
                collect_projection_bounds_substitutions(actual, projection, substitutions);
            }
        }
        _ => {}
    }
}

fn collect_projection_record_field_substitutions(
    actual_fields: &[RecordField<CompactType>],
    projection_fields: &[RecordField<CompactType>],
    substitutions: &mut ProjectionSubstitutions,
) {
    for actual in actual_fields {
        let Some(projection) = projection_fields
            .iter()
            .find(|field| field.name == actual.name && field.optional == actual.optional)
        else {
            continue;
        };
        collect_projection_type_substitutions(&actual.value, &projection.value, substitutions);
    }
}

fn collect_projection_bound_record_field_substitutions(
    actual_fields: &[RecordField<CompactBounds>],
    projection_fields: &[RecordField<CompactBounds>],
    substitutions: &mut ProjectionSubstitutions,
) {
    for actual in actual_fields {
        let Some(projection) = projection_fields
            .iter()
            .find(|field| field.name == actual.name && field.optional == actual.optional)
        else {
            continue;
        };
        collect_projection_bounds_substitutions(&actual.value, &projection.value, substitutions);
    }
}

fn collect_projection_variant_substitutions(
    actual_items: &[(String, Vec<CompactType>)],
    projection_items: &[(String, Vec<CompactType>)],
    substitutions: &mut ProjectionSubstitutions,
) {
    for (name, actual_payloads) in actual_items {
        let Some((_, projection_payloads)) = projection_items
            .iter()
            .find(|(projection_name, _)| projection_name == name)
        else {
            continue;
        };
        if actual_payloads.len() != projection_payloads.len() {
            continue;
        }
        for (actual, projection) in actual_payloads.iter().zip(projection_payloads) {
            collect_projection_type_substitutions(actual, projection, substitutions);
        }
    }
}

fn collect_projection_bound_variant_substitutions(
    actual_items: &[(String, Vec<CompactBounds>)],
    projection_items: &[(String, Vec<CompactBounds>)],
    substitutions: &mut ProjectionSubstitutions,
) {
    for (name, actual_payloads) in actual_items {
        let Some((_, projection_payloads)) = projection_items
            .iter()
            .find(|(projection_name, _)| projection_name == name)
        else {
            continue;
        };
        if actual_payloads.len() != projection_payloads.len() {
            continue;
        }
        for (actual, projection) in actual_payloads.iter().zip(projection_payloads) {
            collect_projection_bounds_substitutions(actual, projection, substitutions);
        }
    }
}
