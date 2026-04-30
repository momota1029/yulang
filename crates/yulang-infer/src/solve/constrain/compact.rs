use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, TypeVar};
use crate::scheme::{OwnedSchemeInstance, compact_pos_type};
use crate::simplify::compact::{
    CompactBounds, CompactType, single_substituted_compact_var, subst_compact_con,
    subst_compact_fun, subst_compact_record, subst_compact_row, subst_compact_type,
    subst_compact_variant, subst_lookup_small,
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
        let parts = compact_pos_parts_with_subst(
            self,
            &instance.scheme.compact.cty.lower,
            instance.subst.as_slice(),
        );
        for part in parts {
            self.constrain_step_with_hint(part, neg, cause, origin_hint, cache);
        }
    }

    pub(super) fn compact_instance_preserves_through(
        &self,
        instance: &OwnedSchemeInstance,
    ) -> bool {
        compact_type_preserves_through(
            self,
            &instance.scheme.compact.cty.lower,
            instance.subst.as_slice(),
        )
    }

    pub(super) fn lower_levels_scheme_instance(
        &self,
        instance: &OwnedSchemeInstance,
        target_lvl: u32,
    ) {
        lower_levels_compact_bounds(
            self,
            &instance.scheme.compact.cty,
            instance.subst.as_slice(),
            target_lvl,
        );
        for bounds in instance.scheme.compact.rec_vars.values() {
            lower_levels_compact_bounds(self, bounds, instance.subst.as_slice(), target_lvl);
        }
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

fn compact_type_preserves_through(
    infer: &Infer,
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
) -> bool {
    if compact_type_is_empty(ty) {
        return true;
    }
    if let Some(tv) = single_substituted_compact_var(ty, subst) {
        return infer.is_through(tv);
    }
    if ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.vars.is_empty()
        && ty.rows.len() == 1
    {
        let row = &ty.rows[0];
        if row.items.is_empty() {
            return compact_type_preserves_through(infer, &row.tail, subst);
        }
    }
    false
}

fn lower_levels_compact_bounds(
    infer: &Infer,
    bounds: &CompactBounds,
    subst: &[(TypeVar, TypeVar)],
    target_lvl: u32,
) {
    lower_levels_compact_type(infer, &bounds.lower, subst, target_lvl);
    lower_levels_compact_type(infer, &bounds.upper, subst, target_lvl);
}

fn lower_levels_compact_type(
    infer: &Infer,
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
    target_lvl: u32,
) {
    for tv in &ty.vars {
        let tv = subst_lookup_small(subst, *tv);
        if infer.level_of(tv) > target_lvl {
            infer.register_level(tv, target_lvl);
        }
    }
    for con in &ty.cons {
        for arg in &con.args {
            lower_levels_compact_bounds(infer, arg, subst, target_lvl);
        }
    }
    for fun in &ty.funs {
        lower_levels_compact_type(infer, &fun.arg, subst, target_lvl);
        lower_levels_compact_type(infer, &fun.arg_eff, subst, target_lvl);
        lower_levels_compact_type(infer, &fun.ret_eff, subst, target_lvl);
        lower_levels_compact_type(infer, &fun.ret, subst, target_lvl);
    }
    for record in &ty.records {
        for field in &record.fields {
            lower_levels_compact_type(infer, &field.value, subst, target_lvl);
        }
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                lower_levels_compact_type(infer, payload, subst, target_lvl);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            lower_levels_compact_type(infer, item, subst, target_lvl);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            lower_levels_compact_type(infer, item, subst, target_lvl);
        }
        lower_levels_compact_type(infer, &row.tail, subst, target_lvl);
    }
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
