import Yulang.GeneralDictionaryFiniteJournalJoint
import Yulang.GeneralDictionaryRecordedCoverageLimit

/-! Regression of finite-journal Joint on the actual recursive support trace.
The locality premise is proved from retained sites and the empty alias graph,
not supplied as an assumption. This concrete regression does not establish
unrestricted reachable-state locality or the general V5 bridge. -/
namespace Yulang.GeneralDictionaryFiniteJournalJointExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState GeneralNominalJointCandidates
open GeneralDeclarationExamples (roles)

/-- The actual one-install trace creates no alias edges. -/
theorem alias_eq {first last : Nat} (alias : Alias finish.current first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

/-- In the actual fixture, a Related site at the parent is literally at that
occurrence; the unrecorded scalar child is a different occurrence. -/
theorem root_locality (site : GeneralNominalDemandMerging.Site roles)
    (related : Related finish.current displayRoot site) : site.occurrence = displayRoot := by
  obtain ⟨member,alias⟩ := related
  rw [GeneralDictionarySupportRecursiveClosure.sites_exact] at member
  rcases List.mem_cons.mp member with rfl | tail
  · rfl
  · have same := List.mem_singleton.mp tail
    subst site
    have impossible := alias_eq alias
    contradiction

/-- Apply the finite-history theorem to the real InitialSource and real
ordinary operational trace, in every supplied current journal model. -/
theorem root_joint (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) : Joint registry finish.current displayRoot 1 :=
  GeneralDictionaryFiniteJournalJoint.initial_joint registry displayRoot displayRoot
    (context true) initial_source finish GeneralDictionaryRecordedCoverageLimit.ordinary_trace
    packet (List.mem_singleton_self _) rfl 1 [displayChild] supported_parent_selected
    root_locality assignment valid

/-- Nonvacuity: the regression applies in a reachable, stable, inhabited final
state. It makes no assertion that every reachable state has the locality above. -/
theorem actual_stable_joint :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    Models finish.current model ∧ Joint registry finish.current displayRoot 1 :=
  ⟨actual_reachable,GeneralDictionarySupportRecursiveClosure.stable,current_model,
    root_joint model current_model⟩
end Yulang.GeneralDictionaryFiniteJournalJointExample
