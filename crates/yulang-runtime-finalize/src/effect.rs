use yulang_runtime_ir::Type as RuntimeType;
use yulang_typed_ir as typed_ir;

use crate::types::{LowerSubstitutions, materialize_core_type, runtime_type_is_closed};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectLane {
    ret_effect: typed_ir::Type,
}

impl EffectLane {
    pub(crate) fn from_return_effect(ret_effect: typed_ir::Type) -> Self {
        Self { ret_effect }
    }

    pub(crate) fn solve(&self, substitutions: &LowerSubstitutions) -> EffectSolution {
        let closed_effect = materialize_core_type(self.ret_effect.clone(), substitutions);
        let is_closed = runtime_type_is_closed(&RuntimeType::Core(closed_effect.clone()));
        EffectSolution {
            closed_effect,
            is_closed,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectSolution {
    pub(crate) closed_effect: typed_ir::Type,
    pub(crate) is_closed: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effect_lane_closes_return_effect_from_substitution() {
        let lane =
            EffectLane::from_return_effect(typed_ir::Type::Var(typed_ir::TypeVar("e".into())));
        let substitutions =
            LowerSubstitutions::from_type_substitutions(&[typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("e".into()),
                ty: typed_ir::Type::Never,
            }])
            .unwrap();

        let solution = lane.solve(&substitutions);

        assert_eq!(solution.closed_effect, typed_ir::Type::Never);
        assert!(solution.is_closed);
    }

    #[test]
    fn effect_lane_keeps_open_return_effect_visible() {
        let lane =
            EffectLane::from_return_effect(typed_ir::Type::Var(typed_ir::TypeVar("e".into())));
        let solution = lane.solve(&LowerSubstitutions::default());

        assert_eq!(
            solution.closed_effect,
            typed_ir::Type::Var(typed_ir::TypeVar("e".into()))
        );
        assert!(!solution.is_closed);
    }
}
