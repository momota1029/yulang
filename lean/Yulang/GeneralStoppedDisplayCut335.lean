import Yulang.GeneralStoppedDisplayProjection335
import Yulang.GeneralDeclarativeWitnessReadout334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralStoppedDisplayCut335
open GeneralStoppedDisplayProjection335
open GeneralNominalExamples (registry interpretation)
open GeneralDeclarationExamples (display)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeWitnessReadout334 (replay replay_exact)

abbrev sourceSpans : List (Nat × Capture) := [(0,point 1)]
abbrev protect : List Nat := [0,1]
def fallback (_ : Nat) : Capture := point 1
def targets (_ : GeneralDeclarations.Clause) (_ : Nat) : Nat := 0
abbrev closed : GeneralDeclarativeHead320.State :=
  ⟨⟨initialOrdinary.normal.ordinary ++ diagonal,[(0,0),(1,1)]⟩,[listRow,scalarRow]⟩

theorem literal_state : ordinary = closed := by
  change (⟨⟨ordinary.normal.ordinary,[(0,0),(1,1)]⟩,[listRow,scalarRow]⟩ : GeneralDeclarativeHead320.State) = closed
  rw [terminal_atoms]

abbrev reminted : Demand := ⟨0,[⟨2,1,3⟩],[]⟩

/-- The current ordinary emitter remints fresh lower/upper names
even for this literal point single binder. This is an actual compile
of the C276 reached final snapshot, not free postulated placement. -/
theorem actual_children :
    (compileBody registry interpretation parentDemand display ordinary sourceSpans protect fallback targets).map Prod.snd =
      some [reminted] := by rw [literal_state] <;> rfl

theorem not_same_literal_child :
    ∀ expected, compileBody registry interpretation parentDemand display ordinary sourceSpans protect fallback targets ≠
      some (expected,[childDemand]) := by
  intro expected same
  have impossible := Option.some.inj (actual_children.symm.trans
    (congrArg (Option.map Prod.snd) same))
  have first := List.cons.inj impossible
  have ranges := List.cons.inj (congrArg Demand.arguments first.1)
  have differing : (2 : Nat) = 1 := congrArg Capture.lower ranges.1
  cases differing

theorem refuses_literal_report :
    replay registry interpretation parentDemand display ordinary sourceSpans protect fallback targets display.id [childDemand] =
      none := by rw [literal_state] <;> rfl

end Yulang.GeneralStoppedDisplayCut335
