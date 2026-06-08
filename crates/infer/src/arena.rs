//! 推論中だけ使う作業 Arena。
//!
//! `poly::Arena` は最終 IR の器なので、constraint propagation の都合で揺れる state を入れない。
//! この `infer::Arena` が fresh ID と `ConstraintMachine` を所有し、lowering が制約を投げる入口になる。

use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, SubtractId, TypeIds, TypeVar};

use crate::constraints::{ConstraintMachine, ConstraintWeights};

/// lowering / inference run ごとの作業状態。
///
/// fresh `TypeVar` / `SubtractId` はここから発行する。solver 側が勝手に fresh var を作ると
/// 出自が追いにくくなるため、lowering が必要な slot を作り、constraint machine はその slot へ
/// 上下界と event を蓄積する。
pub struct Arena {
    type_ids: TypeIds,
    constraints: ConstraintMachine,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            type_ids: TypeIds::new(),
            constraints: ConstraintMachine::new(),
        }
    }

    pub fn fresh_type_var(&mut self) -> TypeVar {
        self.type_ids.fresh_type_var()
    }

    pub fn fresh_subtract_id(&mut self) -> SubtractId {
        self.type_ids.fresh_subtract_id()
    }

    pub fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.constraints.alloc_pos(pos)
    }

    pub fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.constraints.alloc_neg(neg)
    }

    pub fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.constraints.alloc_neu(neu)
    }

    pub fn subtype(&mut self, lower: PosId, upper: NegId) {
        self.constraints.subtype(lower, upper);
    }

    pub fn weighted_subtype(&mut self, lower: PosId, weights: ConstraintWeights, upper: NegId) {
        self.constraints.weighted_subtype(lower, weights, upper);
    }

    pub fn constraints(&self) -> &ConstraintMachine {
        &self.constraints
    }

    pub fn constraints_mut(&mut self) -> &mut ConstraintMachine {
        &mut self.constraints
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}
