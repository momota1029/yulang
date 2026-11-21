import Yulang.GeneralDeclarativeLowerKnown321

namespace Yulang.GeneralDeclarativeAliasMeaning321
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeBounds319 (bound_sound)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

theorem alias_sound {s : State} (read : Alias s a b) (m) (valid : Models s m) :
    Equivalent (m a).1 (m b).1 := by
  induction read with
  | bounds one two => exact ⟨bound_sound m valid.1 one,bound_sound m valid.1 two⟩
  | forward h => simpa only [value,environment] using valid.2 _ h
  | backward h =>
    have entailed := valid.2 _ h
    exact ⟨entailed.2,entailed.1⟩
  | trans _ _ ih jh => exact eqv_trans ih jh

end Yulang.GeneralDeclarativeAliasMeaning321
