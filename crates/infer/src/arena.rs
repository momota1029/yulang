//! 推論中だけ使う作業 Arena。
//!
//! `poly::Arena` は最終 IR の器なので、constraint propagation の都合で揺れる state を入れない。
//! この `infer::Arena` が fresh ID と `ConstraintMachine` を所有し、lowering が制約を投げる入口になる。

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, SubtractId, Subtractability, TypeIds, TypeVar,
};

use crate::constraints::{ConstraintMachine, ConstraintWeights, TypeLevel};

/// lowering / inference run ごとの作業状態。
///
/// fresh `TypeVar` / `SubtractId` はここから発行する。`TypeVar` には current level を付けておき、
/// constraint machine は浅い bound に深い変数が漏れる直前で extrusion をかける。
pub struct Arena {
    type_ids: TypeIds,
    current_level: TypeLevel,
    constraints: ConstraintMachine,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            type_ids: TypeIds::new(),
            current_level: TypeLevel::root(),
            constraints: ConstraintMachine::new(),
        }
    }

    pub fn fresh_type_var(&mut self) -> TypeVar {
        let var = self.type_ids.fresh_type_var();
        self.constraints.register_type_var(var, self.current_level);
        var
    }

    pub fn fresh_type_var_at(&mut self, level: TypeLevel) -> TypeVar {
        let var = self.type_ids.fresh_type_var();
        self.constraints.register_type_var(var, level);
        var
    }

    pub fn fresh_subtract_id(&mut self) -> SubtractId {
        self.type_ids.fresh_subtract_id()
    }

    pub fn current_level(&self) -> TypeLevel {
        self.current_level
    }

    pub fn enter_child_level(&mut self) -> TypeLevel {
        let previous = self.current_level;
        self.current_level = self.current_level.child();
        previous
    }

    pub fn restore_level(&mut self, previous: TypeLevel) {
        self.current_level = previous;
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

    pub fn subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        self.constraints.subtract_fact(effect, id, subtractability);
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
