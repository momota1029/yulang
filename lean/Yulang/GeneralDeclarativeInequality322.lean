import Yulang.GeneralDeclarativeEqualities322
import Yulang.GeneralDeclarativeBounds319
import Yulang.GeneralNominalIntervalLaws

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInequality322
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype common_pair_iff subtype_trans subtype_refl nominal nominal_regular_invariant_exact)
open GeneralNominalIntervalLaws (nominal_sandwich)

inductive Le (s : State) : Expr → Expr → Prop where
  | name : Bound s.normal a b → Le s (.variable a) (.variable b)
  | eqn : Derives s x y → Le s x y
  | refl (x : Expr) : Le s x x
  | trans : Le s x y → Le s y z → Le s x z
  | pair : Le s a b → Le s p q → Le s (.primitive .pair [a,p]) (.primitive .pair [b,q])
  | pairFirst : Le s (.primitive .pair [a,p]) (.primitive .pair [b,q]) → Le s a b
  | pairSecond : Le s (.primitive .pair [a,p]) (.primitive .pair [b,q]) → Le s p q

theorem sound {s : State} (proof : Le s a b) (m : Assignment) (valid : Models s m) :
    Subtype (value (environment m) .actual a) (value (environment m) .actual b) := by
  induction proof with
  | name h => exact bound_sound m valid.1 h
  | eqn e => exact (semantic e m valid).1
  | refl x => exact subtype_refl _
  | trans _ _ ih jh => exact subtype_trans ih jh
  | pair _ _ ih jh => exact (common_pair_iff ..).mpr ⟨ih,jh⟩
  | pairFirst _ ih => exact ((common_pair_iff ..).mp ih).1
  | pairSecond _ ih => exact ((common_pair_iff ..).mp ih).2

def Equal (s : State) (a b : Expr) : Prop := Le s a b ∧ Le s b a

theorem equal_sound {s : State} (proof : Equal s a b) (m : Assignment) (valid : Models s m) :
    Equivalent (value (environment m) .actual a) (value (environment m) .actual b) :=
  ⟨sound proof.1 m valid,sound proof.2 m valid⟩

/-- One-way comparability of nominal heads identifies every invariant
parameter. The heads here may themselves have been derived via logical
equations rather than stored at the compared endpoint names. -/
theorem invariant_at {s : State} (order : Le s (.nominal n xs) (.nominal k ys))
    (i : Nat) (one : xs[i]? = some x) (two : ys[i]? = some y)
    (m : Assignment) (valid : Models s m) :
    n = k ∧ Equivalent (value (environment m) .actual x) (value (environment m) .actual y) := by
  have invariant := (nominal_regular_invariant_exact ..).mp (sound order m valid)
  have emit (xs : List Expr) :
      values (environment m) .actual xs = xs.map (value (environment m) .actual) := by
    induction xs with
    | nil => rfl
    | cons first more ih => simp [values,ih]
  refine ⟨invariant.1,invariant.2.2 i
    (.inl (value (environment m) .actual x)) (.inl (value (environment m) .actual y)) ?_ ?_⟩
  · simp [emit,List.getElem?_map,one]
  · simp [emit,List.getElem?_map,two]

end Yulang.GeneralDeclarativeInequality322
