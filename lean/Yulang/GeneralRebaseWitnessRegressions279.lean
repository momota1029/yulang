import Yulang.GeneralRebaseWitnessTrace279
import Yulang.GeneralRebaseCompactDisplay279
import Yulang.GeneralRebaseFiniteCodeBoundary277
import Yulang.GeneralRebaseCompiledAcc277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10200000
namespace Yulang.GeneralRebaseWitnessRegressions279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralRebaseWitnessBudget279 (WitnessBasis Fact Holds)
open GeneralRebaseWitnessTrace279 (Covers)
open GeneralRebaseQuietBound277 (Counted)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)

theorem uncount {α : Type} {rel : α → α → Prop} {first last : α}
    (path : Counted rel first n last) : B4Target.Steps rel first last := by
  induction path with
  | nil => exact .refl
  | tail _ step ih => exact .tail ih step

namespace Display
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled after effect)
open GeneralRebaseInstallDisplayDelta279 (new_edge)

def fact : Fact roles := .edge (displayRoot,displayChild)

theorem start_reachable : Reachable registry displayRoot before :=
  ⟨before,GeneralRebaseDisplayStep276.initial_source,.refl⟩

theorem one_edge_covers : Covers registry displayRoot before [fact] := by
  intro n mid path e _enabled _novel actual
  rcases GeneralRebaseCompiledAcc277.exact_reached mid (uncount path) with rfl|rfl
  · have only := (GeneralRebaseCompiledAcc277.adapter_next _).mp actual
    refine ⟨fact,List.mem_singleton_self _,new_edge.2,?_⟩
    exact only.symm ▸ new_edge.1
  · exact False.elim (GeneralRebaseCompiledStable277.halted _ actual)

theorem rank_one : GeneralNominalFiniteProgress.remaining Holds [fact] before = 1 := by
  classical
  have absent : ¬ Holds before fact := new_edge.2
  change (if Holds before fact then 0 else 1) = 1
  rw [ite_eq_right absent]

theorem at_most_one (walk : Counted (Actual registry displayRoot) before n last) :
    last.plans.length ≤ before.plans.length + 1 := by
  have rank := (GeneralRebaseWitnessTrace279.trace_budget one_edge_covers start_reachable walk).2
  rw [rank_one] at rank
  omega

end Display

namespace OldLoop
open GeneralDictionaryVersionLoopSource237 (sourceRegistry initial root)
open GeneralRebaseFiniteCodeBoundary277.Loop (formed)

theorem no_local_witness_basis (facts : List (Fact GeneralDictionaryVersionLoopSource237.roles)) :
    ¬ Covers sourceRegistry root initial facts := by
  intro cover
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc
    (GeneralRebaseWitnessTrace279.accessible_from cover formed)

theorem no_global_witness_basis : ¬ Nonempty (WitnessBasis sourceRegistry root) := by
  rintro ⟨basis⟩
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc
    (GeneralRebaseWitnessBudget279.accessible basis formed)

end OldLoop
end Yulang.GeneralRebaseWitnessRegressions279
