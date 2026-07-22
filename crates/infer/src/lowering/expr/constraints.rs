//! Extracted expression lowering methods.

use super::super::*;
use super::*;

impl<'a> ExprLowerer<'a> {
    pub(in crate::lowering) fn fresh_exact_pure_effect(&mut self) -> TypeVar {
        let effect = self.fresh_type_var();
        let bot = self.alloc_pos(Pos::Bot);
        let empty = self.empty_neg_row();
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        let effect_lower = self.alloc_pos(Pos::Var(effect));
        self.session.infer.subtype(
            bot,
            effect_upper,
            crate::constraints::OriginId::unknown_internal(),
        );
        self.session.infer.subtype(
            effect_lower,
            empty,
            crate::constraints::OriginId::unknown_internal(),
        );
        effect
    }

    pub(in crate::lowering) fn empty_neg_row(&mut self) -> NegId {
        let top = self.alloc_neg(Neg::Top);
        self.alloc_neg(Neg::Row(Vec::new(), top))
    }

    pub(in crate::lowering) fn never_neg(&mut self) -> NegId {
        self.alloc_neg(Neg::Bot)
    }

    pub(in crate::lowering) fn constrain_lower(&mut self, var: TypeVar, lower: Pos) {
        self.constrain_lower_with_origin(
            var,
            lower,
            crate::constraints::OriginId::unknown_internal(),
        );
    }

    pub(in crate::lowering) fn constrain_lower_with_origin(
        &mut self,
        var: TypeVar,
        lower: Pos,
        origin: crate::constraints::OriginId,
    ) {
        let lower = self.alloc_pos(lower);
        let upper = self.alloc_neg(Neg::Var(var));
        self.session.infer.subtype(lower, upper, origin);
    }

    pub(in crate::lowering) fn constrain_upper(&mut self, var: TypeVar, upper: Neg) {
        self.constrain_upper_with_origin(
            var,
            upper,
            crate::constraints::OriginId::unknown_internal(),
        );
    }

    pub(in crate::lowering) fn constrain_upper_with_origin(
        &mut self,
        var: TypeVar,
        upper: Neg,
        origin: crate::constraints::OriginId,
    ) {
        let lower = self.alloc_pos(Pos::Var(var));
        let upper = self.alloc_neg(upper);
        self.session.infer.subtype(lower, upper, origin);
    }

    pub(in crate::lowering) fn constrain_exact_primitive(&mut self, var: TypeVar, name: &str) {
        self.constrain_exact_primitive_with_origin(
            var,
            name,
            crate::constraints::OriginId::unknown_internal(),
        );
    }

    pub(in crate::lowering) fn constrain_exact_primitive_with_origin(
        &mut self,
        var: TypeVar,
        name: &str,
        origin: crate::constraints::OriginId,
    ) {
        self.constrain_lower_with_origin(var, primitive_type(name), origin);
        self.constrain_upper_with_origin(var, primitive_neg_type(name), origin);
    }

    pub(in crate::lowering) fn subtype_var_to_var(&mut self, lower: TypeVar, upper: TypeVar) {
        self.subtype_var_to_var_with_origin(
            lower,
            upper,
            crate::constraints::OriginId::unknown_internal(),
        );
    }

    pub(in crate::lowering) fn subtype_var_to_var_with_origin(
        &mut self,
        lower: TypeVar,
        upper: TypeVar,
        origin: crate::constraints::OriginId,
    ) {
        let upper = self.alloc_neg(Neg::Var(upper));
        self.subtype(Pos::Var(lower), upper, origin);
    }

    pub(in crate::lowering) fn subtype_pos_to_var(&mut self, lower: PosId, upper: TypeVar) {
        self.subtype_pos_to_var_with_origin(
            lower,
            upper,
            crate::constraints::OriginId::unknown_internal(),
        );
    }

    pub(in crate::lowering) fn subtype_pos_to_var_with_origin(
        &mut self,
        lower: PosId,
        upper: TypeVar,
        origin: crate::constraints::OriginId,
    ) {
        let upper = self.alloc_neg(Neg::Var(upper));
        self.session.infer.subtype(lower, upper, origin);
    }

    pub(in crate::lowering) fn subtype(
        &mut self,
        lower: Pos,
        upper: NegId,
        origin: crate::constraints::OriginId,
    ) {
        let lower = self.alloc_pos(lower);
        self.session.infer.subtype(lower, upper, origin);
    }

    pub(in crate::lowering) fn wrap_pos_with_subtracts(
        &mut self,
        pos: PosId,
        subtracts: &[StackWeight],
    ) -> PosId {
        subtracts.iter().fold(pos, |inner, weight| {
            self.alloc_pos(Pos::NonSubtract(inner, weight.clone()))
        })
    }

    pub(in crate::lowering) fn alloc_pos(&mut self, pos: Pos) -> poly::types::PosId {
        self.session.infer.alloc_pos(pos)
    }

    pub(in crate::lowering) fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.session.infer.alloc_neg(neg)
    }
}
