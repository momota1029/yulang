//! Taint analysis used to resolve roles that can unblock method selection.
//!
//! Unresolved method selections mark the type variables they flow through. Role
//! solving can then focus on only the role predicates that mention those vars.

use poly::expr::SelectId;
use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{CompactBounds, CompactRoleArg, CompactRoleConstraint, CompactType};

use super::AnalysisSession;

pub(super) type MethodTaintIndex = FxHashMap<TypeVar, Vec<SelectId>>;

pub(super) fn build_method_taint_index(session: &AnalysisSession) -> MethodTaintIndex {
    let mut index = MethodTaintIndex::default();
    let mut selects = session.selections.unresolved().collect::<Vec<_>>();
    selects.sort_by_key(|select| select.0);
    for select in selects {
        let Some(use_site) = session.selections.get(select) else {
            continue;
        };
        let mut builder = MethodTaintBuilder {
            session,
            select,
            index: &mut index,
            visited: FxHashSet::default(),
        };
        builder.visit_var(use_site.method_value, TaintPolarity::Positive);
    }
    index
}

pub(super) fn compact_role_constraint_has_method_taint(
    constraint: &CompactRoleConstraint,
    method_taint: &MethodTaintIndex,
) -> bool {
    compact_role_constraint_has_method_taint_inner::<false>(constraint, method_taint)
}

pub(super) fn compact_role_constraint_has_method_taint_recording_owner_dependencies(
    constraint: &CompactRoleConstraint,
    method_taint: &MethodTaintIndex,
) -> bool {
    compact_role_constraint_has_method_taint_inner::<true>(constraint, method_taint)
}

fn compact_role_constraint_has_method_taint_inner<const RECORD_OWNER_DEPENDENCIES: bool>(
    constraint: &CompactRoleConstraint,
    method_taint: &MethodTaintIndex,
) -> bool {
    constraint.inputs.iter().any(|arg| {
        compact_role_arg_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
    }) || constraint.associated.iter().any(|associated| {
        compact_role_arg_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
            &associated.value,
            method_taint,
        )
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TaintPolarity {
    Positive,
    Negative,
}

impl TaintPolarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

struct MethodTaintBuilder<'a, 'b> {
    session: &'a AnalysisSession,
    select: SelectId,
    index: &'b mut MethodTaintIndex,
    visited: FxHashSet<(TypeVar, TaintPolarity)>,
}

impl<'a, 'b> MethodTaintBuilder<'a, 'b> {
    fn visit_var(&mut self, var: TypeVar, polarity: TaintPolarity) {
        push_unique_select(self.index.entry(var).or_default(), self.select);
        if !self.visited.insert((var, polarity)) {
            return;
        }
        let Some(bounds) = self.session.infer.constraints().bounds().of(var) else {
            return;
        };
        match polarity {
            TaintPolarity::Positive => {
                let uppers = bounds
                    .uppers()
                    .iter()
                    .map(|bound| bound.neg)
                    .collect::<Vec<_>>();
                for upper in uppers {
                    self.visit_neg(upper, polarity);
                }
            }
            TaintPolarity::Negative => {
                let lowers = bounds
                    .lowers()
                    .iter()
                    .map(|bound| bound.pos)
                    .collect::<Vec<_>>();
                for lower in lowers {
                    self.visit_pos(lower, polarity);
                }
            }
        }
    }

    fn visit_pos(&mut self, pos: PosId, polarity: TaintPolarity) {
        match self.session.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.visit_var(var, polarity),
            Pos::Con(_, args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Pos::Tuple(items) => {
                for item in items {
                    self.visit_pos(item, polarity);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_neg(arg, polarity.flipped());
                self.visit_neg(arg_eff, polarity.flipped());
                self.visit_pos(ret_eff, polarity);
                self.visit_pos(ret, polarity);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.visit_pos(field.value, polarity);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { fields, tail } => {
                for field in fields {
                    self.visit_pos(field.value, polarity);
                }
                self.visit_pos(tail, polarity);
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_pos(payload, polarity);
                    }
                }
            }
            Pos::Row(items) => {
                for item in items {
                    self.visit_pos(item, polarity);
                }
            }
            Pos::NonSubtract(pos, _) => self.visit_pos(pos, polarity),
            Pos::Stack { inner, .. } => self.visit_pos(inner, polarity),
            Pos::Union(left, right) => {
                self.visit_pos(left, polarity);
                self.visit_pos(right, polarity);
            }
            Pos::Bot => {}
        }
    }

    fn visit_neg(&mut self, neg: NegId, polarity: TaintPolarity) {
        match self.session.infer.constraints().types().neg(neg).clone() {
            Neg::Var(var) => self.visit_var(var, polarity),
            Neg::Con(_, args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.visit_neg(item, polarity);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_pos(arg, polarity.flipped());
                self.visit_pos(arg_eff, polarity.flipped());
                self.visit_neg(ret_eff, polarity);
                self.visit_neg(ret, polarity);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.visit_neg(field.value, polarity);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_neg(payload, polarity);
                    }
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.visit_neg(item, polarity);
                }
                self.visit_neg(tail, polarity);
            }
            Neg::Intersection(left, right) => {
                self.visit_neg(left, polarity);
                self.visit_neg(right, polarity);
            }
            Neg::Stack { inner, .. } => self.visit_neg(inner, polarity),
            Neg::Top | Neg::Bot => {}
        }
    }

    fn visit_neu(&mut self, neu: NeuId) {
        match self.session.infer.constraints().types().neu(neu).clone() {
            Neu::Bounds(lower, upper) => {
                self.visit_pos(lower, TaintPolarity::Positive);
                self.visit_neg(upper, TaintPolarity::Negative);
            }
            Neu::Con(_, args) | Neu::Tuple(args) => {
                for arg in args {
                    self.visit_neu(arg);
                }
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.visit_neu(arg);
                self.visit_neu(arg_eff);
                self.visit_neu(ret_eff);
                self.visit_neu(ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.visit_neu(field.value);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.visit_neu(payload);
                    }
                }
            }
        }
    }
}

fn push_unique_select(items: &mut Vec<SelectId>, select: SelectId) {
    if !items.contains(&select) {
        items.push(select);
    }
}

fn compact_role_arg_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    arg: &CompactRoleArg,
    method_taint: &MethodTaintIndex,
) -> bool {
    compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&arg.bounds, method_taint)
}

fn compact_bounds_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    bounds: &CompactBounds,
    method_taint: &MethodTaintIndex,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(lower, method_taint)
                || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(upper, method_taint)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            args.iter().any(|arg| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
            })
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                    arg_eff,
                    method_taint,
                )
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                    ret_eff,
                    method_taint,
                )
                || compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(ret, method_taint)
        }
        CompactBounds::Record { fields } => fields.iter().any(|field| {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        }),
        CompactBounds::PolyVariant { items } => items.iter().any(|(_, payloads)| {
            payloads.iter().any(|payload| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(payload, method_taint)
            })
        }),
    }
}

fn compact_type_has_method_taint<const RECORD_OWNER_DEPENDENCIES: bool>(
    ty: &CompactType,
    method_taint: &MethodTaintIndex,
) -> bool {
    ty.vars.iter().any(|var| {
        if RECORD_OWNER_DEPENDENCIES {
            super::record_owner_method_taint_read(var.var);
        }
        method_taint
            .get(&var.var)
            .is_some_and(|selects| !selects.is_empty())
    }) || ty.cons.values().any(|args| {
        args.iter().any(|arg| {
            compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
        })
    }) || ty.funs.iter().any(|fun| {
        compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&fun.arg, method_taint)
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                &fun.arg_eff,
                method_taint,
            )
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(
                &fun.ret_eff,
                method_taint,
            )
            || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&fun.ret, method_taint)
    }) || ty.records.iter().any(|record| {
        record.fields.iter().any(|field| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        })
    }) || ty.record_spreads.iter().any(|spread| {
        spread.fields.iter().any(|field| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&field.value, method_taint)
        }) || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&spread.tail, method_taint)
    }) || ty.poly_variants.iter().any(|variant| {
        variant.items.iter().any(|(_, payloads)| {
            payloads.iter().any(|payload| {
                compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(payload, method_taint)
            })
        })
    }) || ty.tuples.iter().any(|tuple| {
        tuple.items.iter().any(|item| {
            compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(item, method_taint)
        })
    }) || ty.rows.iter().any(|row| {
        row.items.values().any(|args| {
            args.iter().any(|arg| {
                compact_bounds_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(arg, method_taint)
            })
        }) || compact_type_has_method_taint::<RECORD_OWNER_DEPENDENCIES>(&row.tail, method_taint)
    })
}
