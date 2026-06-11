//! lowering 中に引き回す型 slot と、最終的に残す型 table。
//!
//! 式や pattern に永続的な型 table は作らない。式の型は lowering の戻り値である
//! `Computation` として、その場の制約生成に使うだけにする。永続的に残すのは
//! generalize / instantiate の単位になる `DefId` と、use-site として意味を持つ `RefId` 側の情報。

use std::collections::HashMap;

use poly::expr::{DefId, ExprId};
use poly::types::TypeVar;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// expression lowering の戻り値。
///
/// `expr` は作った `poly::ExprId`、`value` は値型 slot、`effect` は計算 effect row の slot。
/// `evaluation` は値制限に使う「計算が発生したか」の情報で、effect row とは別に持つ。
/// pure effect でも expansive な式はあり得るため、この2つを混ぜない。
pub struct Computation {
    pub expr: ExprId,
    pub value: TypeVar,
    pub effect: TypeVar,
    pub effect_view: Option<EffectViewId>,
    pub evaluation: Evaluation,
}

impl Computation {
    pub fn new(expr: ExprId, value: TypeVar, effect: TypeVar, evaluation: Evaluation) -> Self {
        Self {
            expr,
            value,
            effect,
            effect_view: None,
            evaluation,
        }
    }

    pub fn with_effect_view(mut self, view: EffectViewId) -> Self {
        self.effect_view = Some(view);
        self
    }

    pub fn value(expr: ExprId, value: TypeVar, effect: TypeVar) -> Self {
        Self::new(expr, value, effect, Evaluation::Value)
    }

    pub fn computation(expr: ExprId, value: TypeVar, effect: TypeVar) -> Self {
        Self::new(expr, value, effect, Evaluation::Computation)
    }

    pub fn is_expansive(self) -> bool {
        self.evaluation.is_expansive()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EffectViewId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 値制限に使う評価性。
///
/// `Value` はその場で計算を起こさない値、`Computation` は式評価で計算が発生するもの。
/// effect row の具体的な中身とは独立に扱う。
pub enum Evaluation {
    Value,
    Computation,
}

impl Evaluation {
    pub fn is_expansive(self) -> bool {
        matches!(self, Self::Computation)
    }
}

#[derive(Debug, Clone, Default)]
/// 推論結果として永続的に残す型 table。
///
/// 現段階では `DefId -> TypeVar` だけを持つ。`ExprId` / `PatId` に型を持たせると、
/// lowering 中の一時情報が最終 IR に漏れ、あとで更新・削除の責務が曖昧になる。
pub struct Typing {
    defs: HashMap<DefId, TypeVar>,
}

impl Typing {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_def(&mut self, id: DefId, ty: TypeVar) -> Option<TypeVar> {
        self.defs.insert(id, ty)
    }

    pub fn def(&self, id: DefId) -> Option<TypeVar> {
        self.defs.get(&id).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computation_tracks_effect_and_expansiveness_separately() {
        let value = Computation::value(ExprId(0), TypeVar(0), TypeVar(1));
        let computation = Computation::computation(ExprId(1), TypeVar(2), TypeVar(3));

        assert_eq!(value.expr, ExprId(0));
        assert_eq!(value.effect, TypeVar(1));
        assert!(!value.is_expansive());
        assert_eq!(computation.expr, ExprId(1));
        assert_eq!(computation.effect, TypeVar(3));
        assert!(computation.is_expansive());
    }

    #[test]
    fn typing_records_only_def_types() {
        let mut typing = Typing::new();
        let def = DefId(2);

        typing.set_def(def, TypeVar(8));

        assert_eq!(typing.def(def), Some(TypeVar(8)));
    }
}
