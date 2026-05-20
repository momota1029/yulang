use crate::ids::{DefId, TypeVar};
use crate::scheme::{FrozenScheme, compact_neg_type, compact_pos_type};

use crate::scheme::SmallSubst;
use crate::simplify::compact::{CompactBounds, CompactTypeScheme, subst_compact_bounds};

use super::{Infer, RoleConstraint, RoleConstraintArg};

mod candidate;
mod compact_lookup;
mod compact_match;
mod compact_repr;
mod compact_var;
mod constraint_subst;
mod effect_method;
mod extension;
mod method;
mod ref_method;
mod role_method;
mod scheme_arg;

pub(crate) use candidate::{role_candidate_input_subst, select_most_specific_role_candidates};
pub(super) use compact_repr::concrete_tv_repr;
pub(crate) use role_method::CastMethodResolution;

impl Infer {
    pub(crate) fn resolved_selection_def(&self, result_tv: TypeVar) -> Option<DefId> {
        self.resolved_selections.borrow().get(&result_tv).copied()
    }

    pub(crate) fn resolved_ref_field_projection(
        &self,
        result_tv: TypeVar,
    ) -> Option<super::RefFieldProjection> {
        self.resolved_ref_field_projections
            .borrow()
            .get(&result_tv)
            .cloned()
    }

    pub fn instantiate_role_constraints_for_owner(
        &self,
        source_def: DefId,
        owner: DefId,
        subst: &[(TypeVar, TypeVar)],
    ) {
        let scheme = self.frozen_schemes.borrow().get(&source_def).cloned();
        self.instantiate_role_constraints_for_owner_with_scheme(
            source_def,
            owner,
            subst,
            scheme.as_ref(),
        );
    }

    pub fn instantiate_role_constraints_for_owner_with_scheme(
        &self,
        source_def: DefId,
        owner: DefId,
        subst: &[(TypeVar, TypeVar)],
        frozen_scheme: Option<&FrozenScheme>,
    ) {
        if self.is_role_method_def(source_def) {
            return;
        }
        let subst = self.translate_frozen_subst_to_original_with_scheme(frozen_scheme, subst);
        let compact_constraints = self.compact_role_constraints_of(source_def);
        if !compact_constraints.is_empty() {
            if std::env::var_os("YULANG_DEBUG_ROLE_REF").is_some() {
                eprintln!(
                    "-- instantiate_compact_role_constraints_for_owner source={:?} owner={:?} constraints={:?} subst={:?}",
                    source_def, owner, compact_constraints, subst
                );
            }
            for constraint in compact_constraints {
                self.add_role_constraint(
                    owner,
                    RoleConstraint {
                        role: constraint.role,
                        args: constraint
                            .args
                            .iter()
                            .map(|arg| materialize_compact_role_arg(&self.arena, arg, &subst))
                            .collect(),
                    },
                );
            }
            return;
        }
        let constraints = self.role_constraints_of(source_def);
        if std::env::var_os("YULANG_DEBUG_ROLE_REF").is_some() {
            eprintln!(
                "-- instantiate_role_constraints_for_owner source={:?} owner={:?} constraints={:?} subst={:?}",
                source_def, owner, constraints, subst
            );
        }
        for constraint in constraints {
            self.add_role_constraint(
                owner,
                constraint_subst::subst_role_constraint(self, &constraint, subst.as_slice()),
            );
        }
    }

    fn translate_frozen_subst_to_original_with_scheme(
        &self,
        frozen_scheme: Option<&FrozenScheme>,
        subst: &[(TypeVar, TypeVar)],
    ) -> SmallSubst {
        let Some(scheme) = frozen_scheme else {
            return subst.iter().copied().collect();
        };
        let mut translated = SmallSubst::with_capacity(subst.len());
        for (from, to) in subst {
            let original = scheme
                .quantified_sources
                .iter()
                .find_map(|(source, frozen)| (*frozen == *from).then_some(*source))
                .unwrap_or(*from);
            if let Some(slot) = translated
                .iter_mut()
                .find(|(existing, _)| *existing == original)
            {
                slot.1 = *to;
            } else {
                translated.push((original, *to));
            }
        }
        translated
    }
}

fn materialize_compact_role_arg(
    arena: &crate::types::arena::TypeArena,
    arg: &CompactBounds,
    subst: &[(TypeVar, TypeVar)],
) -> RoleConstraintArg {
    let arg = subst_compact_bounds(arg, subst);
    RoleConstraintArg {
        pos: compact_pos_type(arena, &arg.lower, &CompactTypeScheme::default(), false),
        neg: compact_neg_type(arena, &arg.upper, &CompactTypeScheme::default(), false),
    }
}
