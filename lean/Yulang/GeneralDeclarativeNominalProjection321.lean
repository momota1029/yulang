import Yulang.GeneralDeclarativePoint320
import Yulang.GeneralNominalIntervalLaws
import Yulang.GeneralDeclarativeTrace321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalProjection321
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeTrace321 (Trace Links trace_model)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent ArgumentEquivalent nominal subtype_trans nominal_regular_invariant_exact)
open GeneralNominalIntervalLaws (nominal_sandwich)

/-- The two endpoint equations can use different logical names. Invariance
and the actual interval alone identify the center with the lower nominal. -/
theorem nominal_center {s : State} {arg : Capture}
    (bounds : Bounds s arg)
    (lo : (⟨arg.lower,.nominal left xs⟩ : Equation) ∈ s.equations)
    (hi : (⟨arg.upper,.nominal right ys⟩ : Equation) ∈ s.equations)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m arg.center).1 (value (environment m) .actual (.nominal left xs)) := by
  have limit := bounds_sound bounds m valid
  have l := valid.2 _ lo
  have h := valid.2 _ hi
  exact (nominal_sandwich left right
    ((values (environment m) .actual xs).map Sum.inl)
    ((values (environment m) .actual ys).map Sum.inl) _
    (subtype_trans l.2 limit.1) (subtype_trans limit.2 h.1)).1

theorem nominal_center_consequence {s : State} {arg : Capture}
    (bounds : Bounds s arg)
    (lo : (⟨arg.lower,.nominal left xs⟩ : Equation) ∈ s.equations)
    (hi : (⟨arg.upper,.nominal right ys⟩ : Equation) ∈ s.equations) :
    Entails s ⟨arg.center,.nominal left xs⟩ :=
  nominal_center bounds lo hi

theorem endpoint_parameters {s : State} {arg : Capture}
    (bounds : Bounds s arg)
    (lo : (⟨arg.lower,.nominal left xs⟩ : Equation) ∈ s.equations)
    (hi : (⟨arg.upper,.nominal right ys⟩ : Equation) ∈ s.equations)
    (m : Assignment) (valid : Models s m)
    (i : Nat) {a b}
    (first : ((values (environment m) .actual xs).map (fun t : CommonNominalFullCarrier.Ty => (Sum.inl t : CommonNominalFullCarrier.Argument)))[i]? = some (.inl a))
    (last : ((values (environment m) .actual ys).map (fun t : CommonNominalFullCarrier.Ty => (Sum.inl t : CommonNominalFullCarrier.Argument)))[i]? = some (.inl b)) :
    left = right ∧ Equivalent a b := by
  have limit := bounds_sound bounds m valid
  have l := valid.2 _ lo
  have h := valid.2 _ hi
  have relation := (nominal_regular_invariant_exact _ _ _ _).mp
    (subtype_trans l.2 (subtype_trans limit.1 (subtype_trans limit.2 h.1)))
  exact ⟨relation.1,relation.2.2 i _ _ first last⟩

/-- Only the LOWER constructor walk needs named capture readback for
nominal parameters. The upper equation is used for the invariant
sandwich, not to postulate equality between two independently named reads. -/
theorem actual_from_lower_constructor {s : State} {arg : Capture}
    (bounds : Bounds s arg)
    (lo : (⟨arg.lower,.nominal left xs⟩ : Equation) ∈ s.equations)
    (hi : (⟨arg.upper,.nominal right ys⟩ : Equation) ∈ s.equations)
    (trace : Trace s .actual arg.lower code seen)
    (links : Links s capture seen) (m : Assignment) (valid : Models s m) :
    Equivalent (m arg.center).1 (value (variables capture m) .actual code) :=
  eqv_trans (nominal_center bounds lo hi m valid)
    (eqv_trans (valid.2 _ lo |> fun eqv => ⟨eqv.2,eqv.1⟩)
      (trace_model m valid capture trace links))

end Yulang.GeneralDeclarativeNominalProjection321
