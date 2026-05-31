use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, TypeVar};
use crate::scheme::{OwnedSchemeInstance, compact_neg_type, compact_pos_type};
use crate::simplify::compact::{
    CompactBounds, CompactType, compact_root_fun_body_lower, single_substituted_compact_var,
    subst_compact_con, subst_compact_fun, subst_compact_record, subst_compact_record_spread,
    subst_compact_row, subst_compact_type, subst_compact_variant, subst_lookup_small,
};
use crate::types::Pos;

impl Infer {
    pub(super) fn constrain_compact_instance_to_neg(
        &self,
        instance: &OwnedSchemeInstance,
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut StepCache,
    ) {
        let normalized_root_body = compact_root_fun_body_lower(&instance.scheme.compact);
        let lower = normalized_root_body
            .as_ref()
            .unwrap_or(&instance.scheme.compact.cty.lower);
        let parts = compact_pos_parts_with_subst(self, lower, instance.subst.as_slice());
        for part in parts {
            self.constrain_step_with_hint(part, neg, cause, origin_hint, cache);
        }
    }

    pub(super) fn compact_instance_root_upper_parts(
        &self,
        instance: &OwnedSchemeInstance,
    ) -> Vec<NegId> {
        compact_neg_parts_with_subst(
            self,
            &instance.scheme.compact.cty.upper,
            instance.subst.as_slice(),
        )
    }

    pub(super) fn max_level_scheme_instance(&self, instance: &OwnedSchemeInstance) -> u32 {
        let mut max = max_level_compact_bounds(
            self,
            &instance.scheme.compact.cty,
            instance.subst.as_slice(),
        );
        for bounds in instance.scheme.compact.rec_vars.values() {
            max = max.max(max_level_compact_bounds(
                self,
                bounds,
                instance.subst.as_slice(),
            ));
        }
        max
    }
}

pub(super) fn compact_instance_direct_var(instance: &OwnedSchemeInstance) -> Option<TypeVar> {
    single_substituted_compact_var(
        &instance.scheme.compact.cty.lower,
        instance.subst.as_slice(),
    )
}

fn compact_pos_parts_with_subst(
    infer: &Infer,
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
) -> Vec<crate::ids::PosId> {
    if compact_type_is_empty(ty) {
        return vec![infer.alloc_pos(Pos::Bot)];
    }

    let mut parts = Vec::new();
    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(
        vars.into_iter()
            .map(|tv| infer.alloc_pos(Pos::Var(subst_lookup_small(subst, tv)))),
    );

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by_key(path_key);
    for path in prims {
        let mut fragment = CompactType::default();
        fragment.prims.insert(path);
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }

    for con in &ty.cons {
        let mut fragment = CompactType::default();
        fragment.cons.push(subst_compact_con(con, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for fun in &ty.funs {
        let mut fragment = CompactType::default();
        fragment.funs.push(subst_compact_fun(fun, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for record in &ty.records {
        let mut fragment = CompactType::default();
        fragment.records.push(subst_compact_record(record, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for spread in &ty.record_spreads {
        let mut fragment = CompactType::default();
        fragment
            .record_spreads
            .push(subst_compact_record_spread(spread, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for variant in &ty.variants {
        let mut fragment = CompactType::default();
        fragment
            .variants
            .push(subst_compact_variant(variant, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for tuple in &ty.tuples {
        let mut fragment = CompactType::default();
        fragment.tuples.push(
            tuple
                .iter()
                .map(|item| subst_compact_type(item, subst))
                .collect(),
        );
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for row in &ty.rows {
        let mut fragment = CompactType::default();
        fragment.rows.push(subst_compact_row(row, subst));
        parts.push(compact_pos_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    parts
}

fn compact_neg_parts_with_subst(
    infer: &Infer,
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
) -> Vec<crate::ids::NegId> {
    if compact_type_is_empty(ty) {
        return Vec::new();
    }

    let mut parts = Vec::new();
    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(
        vars.into_iter()
            .map(|tv| infer.alloc_neg(crate::types::Neg::Var(subst_lookup_small(subst, tv)))),
    );

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by_key(path_key);
    for path in prims {
        let mut fragment = CompactType::default();
        fragment.prims.insert(path);
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }

    for con in &ty.cons {
        let mut fragment = CompactType::default();
        fragment.cons.push(subst_compact_con(con, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for fun in &ty.funs {
        let mut fragment = CompactType::default();
        fragment.funs.push(subst_compact_fun(fun, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for record in &ty.records {
        let mut fragment = CompactType::default();
        fragment.records.push(subst_compact_record(record, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for spread in &ty.record_spreads {
        let mut fragment = CompactType::default();
        fragment
            .record_spreads
            .push(subst_compact_record_spread(spread, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for variant in &ty.variants {
        let mut fragment = CompactType::default();
        fragment
            .variants
            .push(subst_compact_variant(variant, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for tuple in &ty.tuples {
        let mut fragment = CompactType::default();
        fragment.tuples.push(
            tuple
                .iter()
                .map(|item| subst_compact_type(item, subst))
                .collect(),
        );
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    for row in &ty.rows {
        let mut fragment = CompactType::default();
        fragment.rows.push(subst_compact_row(row, subst));
        parts.push(compact_neg_type(
            &infer.arena,
            &fragment,
            &dummy_compact_scheme(),
            false,
        ));
    }
    parts
}

fn max_level_compact_bounds(
    infer: &Infer,
    bounds: &CompactBounds,
    subst: &[(TypeVar, TypeVar)],
) -> u32 {
    max_level_compact_type(infer, &bounds.lower, subst).max(max_level_compact_type(
        infer,
        &bounds.upper,
        subst,
    ))
}

fn max_level_compact_type(infer: &Infer, ty: &CompactType, subst: &[(TypeVar, TypeVar)]) -> u32 {
    let mut max = ty
        .vars
        .iter()
        .map(|tv| infer.level_of(subst_lookup_small(subst, *tv)))
        .max()
        .unwrap_or(0);
    for con in &ty.cons {
        for arg in &con.args {
            max = max.max(max_level_compact_bounds(infer, arg, subst));
        }
    }
    for fun in &ty.funs {
        max = max.max(max_level_compact_type(infer, &fun.arg, subst));
        max = max.max(max_level_compact_type(infer, &fun.arg_eff, subst));
        max = max.max(max_level_compact_type(infer, &fun.ret_eff, subst));
        max = max.max(max_level_compact_type(infer, &fun.ret, subst));
    }
    for record in &ty.records {
        for field in &record.fields {
            max = max.max(max_level_compact_type(infer, &field.value, subst));
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            max = max.max(max_level_compact_type(infer, &field.value, subst));
        }
        max = max.max(max_level_compact_type(infer, &spread.tail, subst));
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                max = max.max(max_level_compact_type(infer, payload, subst));
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            max = max.max(max_level_compact_type(infer, item, subst));
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            max = max.max(max_level_compact_type(infer, item, subst));
        }
        max = max.max(max_level_compact_type(infer, &row.tail, subst));
    }
    max
}

fn dummy_compact_scheme() -> crate::simplify::compact::CompactTypeScheme {
    crate::simplify::compact::CompactTypeScheme::default()
}

fn compact_type_is_empty(ty: &CompactType) -> bool {
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

fn path_key(path: &crate::symbols::Path) -> Vec<String> {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect()
}
