//! Type inference slots paired with erased value structure.
//!
//! `LoweredComputation` is the target carrier for source lowering once the
//! typed AST bridge is retired. It keeps the computation boundary variables
//! (`tv` / `eff`) outside the erased IR so expression nodes do not expose
//! inferred types or effects to later stages.

use yulang_erased_ir::ErasedExpr;

use crate::ast::expr::ComputationTy;
use crate::ids::TypeVar;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredComputation {
    pub tv: TypeVar,
    pub eff: TypeVar,
    pub ir: ErasedExpr,
}

impl LoweredComputation {
    pub fn new(ty: ComputationTy, ir: ErasedExpr) -> Self {
        Self {
            tv: ty.value,
            eff: ty.effect,
            ir,
        }
    }

    pub fn from_parts(tv: TypeVar, eff: TypeVar, ir: ErasedExpr) -> Self {
        Self { tv, eff, ir }
    }

    pub fn computation_ty(&self) -> ComputationTy {
        ComputationTy::new(self.tv, self.eff)
    }

    pub fn into_ir(self) -> ErasedExpr {
        self.ir
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowered_computation_keeps_type_slots_outside_erased_ir() {
        let ty = ComputationTy::new(TypeVar(1), TypeVar(2));
        let lowered = LoweredComputation::new(ty, ErasedExpr::Lit(yulang_erased_ir::Lit::Unit));

        assert_eq!(lowered.computation_ty(), ty);
        assert_eq!(lowered.ir, ErasedExpr::Lit(yulang_erased_ir::Lit::Unit));
    }
}
