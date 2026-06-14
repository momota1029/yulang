use std::collections::{HashMap, HashSet};

use super::types::{MonoVarId, TypeArena, TypeId, TypeKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeInterval {
    pub lower: TypeId,
    pub upper: TypeId,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VarBounds {
    pub lower: HashSet<TypeId>,
    pub upper: HashSet<TypeId>,
}

#[derive(Debug, Default)]
pub struct ConstraintGraph {
    bounds: HashMap<MonoVarId, VarBounds>,
    subtype_edges: HashSet<(MonoVarId, MonoVarId)>,
}

impl ConstraintGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bounds(&self, var: MonoVarId) -> VarBounds {
        self.bounds.get(&var).cloned().unwrap_or_default()
    }

    pub fn subtype_edges(&self) -> &HashSet<(MonoVarId, MonoVarId)> {
        &self.subtype_edges
    }

    pub fn constrain_subtype(&mut self, arena: &TypeArena, lower: TypeId, upper: TypeId) {
        if lower == upper || lower == arena.never() || upper == arena.any() {
            return;
        }

        match (arena.kind(lower), arena.kind(upper)) {
            (TypeKind::Var(lower), TypeKind::Var(upper)) => {
                self.add_subtype_edge(*lower, *upper);
            }
            (TypeKind::Var(var), _) => {
                self.add_upper_bound(*var, upper);
            }
            (_, TypeKind::Var(var)) => {
                self.add_lower_bound(*var, lower);
            }
            (
                TypeKind::Fun {
                    param: lower_param,
                    param_effect: lower_param_effect,
                    ret_effect: lower_ret_effect,
                    ret: lower_ret,
                },
                TypeKind::Fun {
                    param: upper_param,
                    param_effect: upper_param_effect,
                    ret_effect: upper_ret_effect,
                    ret: upper_ret,
                },
            ) => {
                self.constrain_subtype(arena, *upper_param, *lower_param);
                self.constrain_subtype(arena, *upper_param_effect, *lower_param_effect);
                self.constrain_subtype(arena, *lower_ret_effect, *upper_ret_effect);
                self.constrain_subtype(arena, *lower_ret, *upper_ret);
            }
            (
                TypeKind::EffectiveThunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                TypeKind::EffectiveThunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_subtype(arena, *lower_effect, *upper_effect);
                self.constrain_subtype(arena, *lower_value, *upper_value);
            }
            (
                TypeKind::Named {
                    path: lower_path,
                    args: lower_args,
                },
                TypeKind::Named {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                for (lower_arg, upper_arg) in lower_args.iter().zip(upper_args) {
                    self.constrain_invariant_type_arg(arena, *lower_arg, *upper_arg);
                }
            }
            (TypeKind::Tuple(lower_items), TypeKind::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower_item, upper_item) in lower_items.iter().zip(upper_items) {
                    self.constrain_subtype(arena, *lower_item, *upper_item);
                }
            }
            _ => {}
        }
    }

    pub fn constrain_interval_to_var(
        &mut self,
        arena: &TypeArena,
        interval: TypeInterval,
        var: MonoVarId,
    ) {
        let var_ty = arena.var_type(var);
        self.constrain_subtype(arena, interval.lower, var_ty);
        self.constrain_subtype(arena, var_ty, interval.upper);
    }

    fn constrain_invariant_type_arg(&mut self, arena: &TypeArena, lower: TypeId, upper: TypeId) {
        self.constrain_subtype(arena, lower, upper);
        self.constrain_subtype(arena, upper, lower);
    }

    fn add_subtype_edge(&mut self, lower: MonoVarId, upper: MonoVarId) {
        if !self.subtype_edges.insert((lower, upper)) {
            return;
        }

        let lower_bounds = self.bounds(lower).lower;
        let upper_bounds = self.bounds(upper).upper;
        for bound in lower_bounds {
            self.add_lower_bound(upper, bound);
        }
        for bound in upper_bounds {
            self.add_upper_bound(lower, bound);
        }
    }

    fn add_lower_bound(&mut self, var: MonoVarId, ty: TypeId) {
        if !self.bounds.entry(var).or_default().lower.insert(ty) {
            return;
        }

        let targets = self
            .subtype_edges
            .iter()
            .filter_map(|(lower, upper)| (*lower == var).then_some(*upper))
            .collect::<Vec<_>>();
        for target in targets {
            self.add_lower_bound(target, ty);
        }
    }

    fn add_upper_bound(&mut self, var: MonoVarId, ty: TypeId) {
        if !self.bounds.entry(var).or_default().upper.insert(ty) {
            return;
        }

        let sources = self
            .subtype_edges
            .iter()
            .filter_map(|(lower, upper)| (*upper == var).then_some(*lower))
            .collect::<Vec<_>>();
        for source in sources {
            self.add_upper_bound(source, ty);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::TypeVarKind;
    use yulang_erased_ir::{Name, Path};

    fn path(name: &str) -> Path {
        Path::from_name(Name(name.to_string()))
    }

    #[test]
    fn interval_compared_with_var_adds_lower_and_upper_constraints() {
        let mut arena = TypeArena::new();
        let (alpha_pos, alpha_pos_ty) = arena.fresh_var(TypeVarKind::Value);
        let (beta_neg, beta_neg_ty) = arena.fresh_var(TypeVarKind::Value);
        let (gamma, _) = arena.fresh_var(TypeVarKind::Value);
        let mut graph = ConstraintGraph::new();

        graph.constrain_interval_to_var(
            &arena,
            TypeInterval {
                lower: alpha_pos_ty,
                upper: beta_neg_ty,
            },
            gamma,
        );

        assert!(
            graph.subtype_edges().contains(&(alpha_pos, gamma)),
            "α+ should become a lower edge into γ"
        );
        assert!(
            graph.subtype_edges().contains(&(gamma, beta_neg)),
            "β- should become an upper edge out of γ"
        );
    }

    #[test]
    fn invariant_nominal_arguments_constrain_both_directions() {
        let mut arena = TypeArena::new();
        let (alpha, alpha_ty) = arena.fresh_var(TypeVarKind::Value);
        let int = arena.named(path("int"), Vec::new());
        let lower = arena.named(path("list"), vec![alpha_ty]);
        let upper = arena.named(path("list"), vec![int]);
        let mut graph = ConstraintGraph::new();

        graph.constrain_subtype(&arena, lower, upper);

        let bounds = graph.bounds(alpha);
        assert!(bounds.lower.contains(&int));
        assert!(bounds.upper.contains(&int));
    }
}
