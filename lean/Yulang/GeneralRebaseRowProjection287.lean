import Yulang.GeneralRebaseRowClosure287

/-! The finite owner/output observer covers the same real install for both
registries, but its state alone cannot decide whether the child dictionary is
available. Settlement/readiness remains outside this two-fact observer. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 15200000
namespace Yulang.GeneralRebaseRowProjection287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after after_exact after_model)
open GeneralRebaseRowParentStep287 (actual_step)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseStep258 (done initial)
open GeneralRebaseSourceStepDriver270 (next)
open GeneralRebaseLiveProjection264 (project)
open GeneralNominalVersionedEvidence231 (Evidence)

def owner : Nat := GeneralNominalIdentities.pair root.identity parentDecl.id
def output : GeneralSourceState.Output := ⟨0,2⟩
abbrev support := GeneralRebaseCompression266.Basis [owner] [output]

def observe (s : State roles) : GeneralRebaseStep258.State support := project [owner] [output] s

theorem before_observe : observe before = initial support :=
  GeneralRebaseWriteAlgebra259.empty _

theorem after_observe (choice : Bool) : observe (after choice) = done support := by
  apply GeneralRebaseStep258.state_ext
  change (observe (after choice)).remaining = []
  cases choice <;> decide +kernel

theorem driver_before : next support (observe before) = some (done support) := by
  rw [before_observe]
  rfl

theorem driver_after (choice : Bool) : next support (observe (after choice)) = none := by
  rw [after_observe]
  rfl

theorem actual_square (choice : Bool) :
    Step (registry choice) root before (after choice) ∧
      next support (observe before) = some (observe (after choice)) :=
  ⟨actual_step choice,(after_observe choice).symm ▸ driver_before⟩

theorem exact_model_same (m) : Models (after true) m ↔ Models (after false) m :=
  (after_exact true m).trans (after_exact false m).symm

theorem output_view_indistinguishable : observe (after true) = observe (after false) :=
  (after_observe true).trans (after_observe false).symm

theorem no_dictionary_status_from_output_view :
    ¬ ∃ f : GeneralRebaseStep258.State support → Bool,
      f (observe (after true)) = true ∧ f (observe (after false)) = false := by
  rintro ⟨f,good,bad⟩
  rw [output_view_indistinguishable] at good
  cases good.symm.trans bad

theorem materially_different_at_same_output_view :
    observe (after true) = observe (after false) ∧
    (∀ m, Models (after true) m ↔ Models (after false) m) ∧
    ∃ m, Models (after true) m ∧ Models (after false) m ∧
      Evidence (registry true) (after true).core m root (.node 0 [.node 1 []]) ∧
      ∀ p, ¬ Evidence (registry false) (after false).core m root p := by
  have actual := after_model true Common.rowEmpty
  exact ⟨output_view_indistinguishable,exact_model_same,_,actual,
    GeneralRebaseRowPayloadExact287.comparison _ actual⟩

end Yulang.GeneralRebaseRowProjection287
