import Yulang.GeneralDictionaryTotalEvidence206
import Yulang.GeneralDictionaryDefaultEvidence204Examples

/-! A named terminal default fragment of legacy-to-total preservation.
This is not the unrestricted migration theorem: centered binder names and raw
source recording are not fields of the historical certificate. -/
namespace Yulang.GeneralDictionaryTotalLegacy206
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202
open GeneralNominalCommonBridge (Assignment)

/-- Every historical certificate for this concrete terminal default source,
in any assignment, yields the total semantic certificate in that assignment.
No selection, commitment, or proposed semantic conclusion is a premise. -/
theorem terminal_default_old_to_new (assignment : Assignment)
    (old : GeneralDictionaryDefaultEvidence204.Certificate registry start.core assignment root 37 [] plan) :
    GeneralDictionaryTotalEvidence206.Certificate registry start.core assignment root 37 [] plan := by
  have valid : GeneralNominalState.Models snapshot assignment :=
    GeneralDictionaryDefaultEvidence204.instance_models ⟨plan,old⟩
  exact GeneralDictionaryTotalEvidence206.certificate_of_semantics
    GeneralDictionaryAllocDefaultLocal202.frame children_empty.symm
    (total_packet assignment ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr valid)) ready (class_effects assignment)

/-- The supported terminal fragment has a semantic leaf in every source model. -/
theorem terminal_default_leaf (assignment : Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralDictionaryTotalEvidence206.Evidence registry start.core assignment root (.node 37 []) :=
  GeneralDictionaryTotalEvidence206.evidence_leaf ⟨plan,
    terminal_default_old_to_new assignment
      (GeneralDictionaryDefaultEvidence204Examples.default_certificate assignment valid)⟩

end Yulang.GeneralDictionaryTotalLegacy206
