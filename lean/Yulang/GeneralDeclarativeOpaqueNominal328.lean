import Yulang.GeneralDeclarativeOpaqueConserve328
import Yulang.GeneralNominalIntervalLaws

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueNominal328
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeEntailment320 (Entails appendFacts conservative_append)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeGrowth327 (facts)
open CommonNominalFullCarrier (subtype_trans)

def point (n : Nat) : Capture := ⟨n,n,n⟩
def row (center tag low : Nat) : Equation := ⟨center,.nominal tag [.variable low]⟩
def ready (s : State) (center tag low : Nat) : State := appendFacts s [row center tag low]

theorem nominal_truth {s : State} (given : Bounds s arg)
    (lo : Entails s ⟨arg.lower,.nominal tag [.variable a]⟩)
    (hi : Entails s ⟨arg.upper,.nominal tag [.variable b]⟩) :
    Entails s (row arg.center tag a) := by
  intro m fit
  have l := lo m fit
  have h := hi m fit
  have found := bounds_sound given m fit
  exact (GeneralNominalIntervalLaws.nominal_sandwich tag tag [.inl (m a).1] [.inl (m b).1]
    (m arg.center).1 (subtype_trans l.2 found.1) (subtype_trans found.2 h.1)).1

/-- An invariant parameter does not require choosing a new actual
point. The ordinary shape equation is entailed; no body is unfolded
and the source provenance of the operand is unchanged. -/
theorem retains {s : State} (given : Bounds s arg)
    (lo : Entails s ⟨arg.lower,.nominal tag [.variable a]⟩)
    (hi : Entails s ⟨arg.upper,.nominal tag [.variable b]⟩) :
    Retains s (ready s arg.center tag a) keep := by
  refine ⟨facts _ _,?_⟩
  intro m fit
  have proved : ∀ row' ∈ [row arg.center tag a], Entails s row' := by
    intro row' included
    cases List.mem_singleton.mp included
    exact nominal_truth given lo hi
  exact ⟨m,(conservative_append proved m).mpr fit,fun _ _ => rfl⟩

theorem reads {s : State} (center tag low : Nat) :
    Derives (ready s center tag low) (.variable center) (.nominal tag [.variable low]) :=
  .row (List.mem_append_right _ List.mem_cons_self)

theorem point_bounded (s : State) (name : Nat) : Bounds s (point name) :=
  ⟨.refl _,.refl _⟩

end Yulang.GeneralDeclarativeOpaqueNominal328
