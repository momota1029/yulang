import Yulang.GeneralStoppedDisplayChoice335
import Yulang.GeneralStoppedDisplayCut335
import Yulang.GeneralStoppedLiteralWitness335

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralStoppedDisplayLiteral335
open GeneralNominalExamples (registry interpretation intDisplay registry_checked displayRoot)
open GeneralDeclarationExamples (display)
open GeneralStoppedDisplayProjection335
open GeneralStoppedDisplayGuard335 (waiting covered list_trace int_trace list_print int_print parent_declared)
open GeneralStoppedDisplayChoice335 (parent_choice child_choice)
open GeneralStoppedDisplayCut335 (sourceSpans protect fallback targets literal_state)
open GeneralStoppedLiteralCompiler335 (compile)
open GeneralStoppedLiteralWitness335 (Rule Witness sound)
open GeneralDeclarativeWitnessHead334 (Actuals full)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify)
open GeneralRebaseDisplayExecutor276 (run run_exact raw Phase)

theorem direct_parent :
    compile registry interpretation parentDemand display ordinary sourceSpans protect fallback targets =
      some (ordinary,[childDemand]) := by
  rw [literal_state] <;> rfl

theorem direct_child :
    compile registry interpretation childDemand intDisplay ordinary [] protect fallback targets =
      some (ordinary,[]) := by
  rw [literal_state] <;> rfl

noncomputable def rootReceipt (done : Nat → Prop) :
    Witness (supported done) registry interpretation waiting parentDemand display [childDemand] where
  chosen := parent_choice done
  slice := full (supported done)
  keep := protect
  fallback := fallback
  targets := targets
  named := ordinary
  spans := sourceSpans
  supported := .cons (.named ⟨point_bounded _ _,_,_,list_print,list_trace done .actual,
    .cons ⟨rfl,rfl,point_bounded _ _⟩ .nil⟩) .nil
  linear := by decide +kernel
  computed := ordinary
  emitted := direct_parent
  receipt := literal (reflexive ordinary)

noncomputable def childReceipt (done : Nat → Prop) :
    Witness (supported done) registry interpretation waiting childDemand intDisplay [] where
  chosen := child_choice done
  slice := full (supported done)
  keep := protect
  fallback := fallback
  targets := targets
  named := ordinary
  spans := []
  supported := .cons (.named ⟨point_bounded _ _,_,_,int_print,int_trace done .actual,.nil⟩) .nil
  linear := .nil
  computed := ordinary
  emitted := direct_child
  receipt := literal (reflexive ordinary)

theorem ordered_tree (done : Nat → Prop) :
    Classify (Rule (supported done) registry interpretation waiting) parentDemand
      (.selected (.node 1 [.node 3 []])) :=
  ⟨.selected 1 [.selected 3 []],
    .selected (.selected (rootReceipt done)) (.cons (.selected (.selected (childReceipt done)) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- End-to-end regression for the actual finite C276 raw run. The
proof shares the raw assignment with ordinary replay. Only the
isolated literal compaction is tested; the active C334 body remains
untouched and its exact-name mismatch is separate. -/
theorem actual_success (done : Nat → Prop) (accepted : run key = some (phase,payload)) :
    Classify (Rule (supported done) registry interpretation waiting) parentDemand (.selected payload) ∧
      ∀ m, (Models ordinary m ↔ GeneralNominalVersionedJournal232.Models (raw phase) m) ∧
        (GeneralNominalVersionedJournal232.Models (raw phase) m →
          Evidence registry interpretation m parentDemand payload) := by
  obtain ⟨_,rfl,rfl⟩ := (run_exact key phase payload).mp accepted
  exact ⟨ordered_tree done,fun m => ⟨actual_model m,fun fit =>
    sound registry_checked covered parent_declared (ordered_tree done) m ((actual_model m).mpr fit)⟩⟩

theorem inhabited (done : Nat → Prop) :
    ∃ m, GeneralNominalVersionedJournal232.Models (raw .settled) m ∧
      Evidence registry interpretation m parentDemand (.node 1 [.node 3 []]) := by
  let m := GeneralNominalExamples.model
  have actual : GeneralNominalVersionedJournal232.Models (raw .settled) m :=
    (GeneralRebaseDisplayFrame276.after_models _).mpr (GeneralNominalExamples.state_models true)
  exact ⟨m,actual,
    ((actual_success done GeneralRebaseDisplayExecutor276.canonical).2 m).2 actual⟩

end Yulang.GeneralStoppedDisplayLiteral335
