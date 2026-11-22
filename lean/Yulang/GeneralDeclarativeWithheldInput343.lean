import Yulang.GeneralDeclarativeWithheldReceipt343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 8800000
namespace Yulang.GeneralDeclarativeWithheldInput343
open GeneralDeclarativeCurrentWorld343 (now grows)
open GeneralDeclarativeCurrentOrigins343 (done ChildReceipt)
open GeneralDeclarativeFrameShape343 (e0 e1 e2 childRows output_ordinary)
open GeneralDeclarativePlacement343 (symbolic)
open GeneralDeclarativeWithheldReceipt343 (lower_source center_source upper_source bound_isolated)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand original_arguments)
open GeneralDeclarativeVersionedRootShape342 (point)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation root)

/-- The other counterfactual preserves real child receipt authority
and every ordinary equation, but removes the authored root origin. -/
noncomputable def withheld : Supported now done :=
  ⟨fun row origin => ChildReceipt row ∧ origin = .output root.identity,
    fun pos => grows.equations (output_ordinary _ pos.1.printed)⟩

theorem only_receipts (row : Equation) (seen : row ∈ (restriction withheld).equations) :
    row ∈ childRows := by
  obtain ⟨_,a,_⟩ := (backed_iff withheld row).mp seen
  exact a.1.printed

theorem not_variable {a b : Nat} (listed : (⟨a,.variable b⟩ : Equation) ∈ childRows) : False := by
  rcases List.mem_cons.mp listed with one|others
  · cases congrArg Equation.right one
  · rcases List.mem_cons.mp others with one|last
    · cases congrArg Equation.right one
    · cases congrArg Equation.right (List.mem_singleton.mp last)

theorem never_root (row : Equation) (listed : row ∈ childRows) : row.left ≠ 0 := by
  rcases List.mem_cons.mp listed with h|others
  · cases h
    exact lower_source
  · rcases List.mem_cons.mp others with h|last
    · cases h
      exact center_source
    · cases List.mem_singleton.mp last
      exact upper_source

theorem isolated {a b : Nat} (link : Alias (restriction withheld) a b) :
    (a = 0 ↔ b = 0) := by
  induction link with
  | bounds low _ => exact bound_isolated low
  | trans _ _ first later => exact first.trans later
  | forward listed => exact False.elim (not_variable (only_receipts _ listed))
  | backward listed => exact False.elim (not_variable (only_receipts _ listed))

theorem no_anchor (row : Equation) (seen : row ∈ (restriction withheld).equations) :
    ¬ Alias (restriction withheld) 0 row.left := by
  intro got
  exact never_root row (only_receipts row seen) ((isolated got).mp rfl)

theorem not_ready : ¬ GeneralDeclarativeTaggedElection340.Ready withheld actualDemand := by
  intro known
  have input : point ∈ actualDemand.arguments := original_arguments.symm ▸ List.mem_cons_self
  obtain normal | synthetic := known point input
  · obtain ⟨_,row,h,related,_⟩ := normal
    exact no_anchor row h related
  · obtain ⟨_,_,_,⟨_,related,h⟩,_⟩ := synthetic
    exact no_anchor _ h related

theorem no_authored_no_root (key : Nat) (children) :
    ¬ Rule withheld [] sourceRegistry interpretation waiting actualDemand (.selected key children) := by
  intro selected
  cases selected with
  | whole folded => exact not_ready folded.elected.ready

end Yulang.GeneralDeclarativeWithheldInput343
