import Yulang.GeneralDeclarativeVersionedRootShape342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15300
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeVersionedRootCompiler342
open GeneralWhereOriginSingleSource318 (declaration sourceRegistry checked)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand original_targets)
open GeneralDeclarativeVersionedRootShape342 (spans)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeVersionedChildWitness342 (coverage)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEndpointBody336 (Body calculate)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Clause)

theorem declared : Declared sourceRegistry actualDemand := by
  intro out here
  rw [original_targets] at here
  cases List.mem_singleton.mp here
  exact ⟨_,rfl⟩

theorem fixed_root (capture : Nat → Capture) :
    collect (one sourceRegistry interpretation declaration actualDemand capture) actualDemand.outputs =
      some [ownerOutput] := by
  rw [original_targets]
  rfl

theorem source_compile (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ s kids, ∃ body : @Body sourceRegistry interpretation actualDemand declaration s kids,
      compileBody sourceRegistry interpretation actualDemand declaration observedRoot spans keep fallback targets =
        some (s,kids) ∧
      body.rootRows = [ownerOutput] ∧ kids.length = 1 := by
  have ordered : spans.map Prod.fst = declaration.inputNames := rfl
  have fit : ∀ a ∈ spans, Bounds observedRoot a.2 := by
    intro a present
    rcases List.mem_cons.mp present with rfl|later
    · exact point_bounded _ _
    · cases List.mem_singleton.mp later
      exact point_bounded _ _
  obtain ⟨s,kids,body,computed,_⟩ := calculate checked coverage List.mem_cons_self (by rfl)
    declared keep fallback targets ordered fit
  have actual := body.rootWritten
  rw [fixed_root] at actual
  refine ⟨s,kids,body,computed,(Option.some.inj actual).symm,?_⟩
  rw [← body.ordered]
  rfl

end Yulang.GeneralDeclarativeVersionedRootCompiler342
