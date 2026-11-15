import Yulang.GeneralDictionaryDefaultBoundary204
import Yulang.GeneralDictionaryDefaultEvidence204Examples

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultSelected204
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202
open GeneralDictionaryDefaultBoundary204
open CommonRoleOutermostResolver

theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) :=
  local_iff.mpr v7_selected

theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) := by
  change GeneralDictionaryDefaultEvidence204.Evidence registry start.core assignment root (.node 37 [])
  exact GeneralDictionaryDefaultEvidence204.evidence_leaf_iff.mpr
    ⟨plan,GeneralDictionaryDefaultEvidence204Examples.default_certificate assignment valid.1⟩

/-- The whole selected-only field at the cycle202 snapshot, including all final
models and all generated demands. This is a regression, not global EvidenceNode. -/
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root := by
  intro assignment valid demand key children dictionaries reached stable childStable chosen given
  have same : demand = root := by
    rcases reached with same | generated
    · exact same
    · exact generated_only_root demand generated
  subst demand
  have equal := B4TargetV7.local_functional chosen selected
  cases equal
  cases given
  exact evidence_model assignment valid

theorem regression : (boundary roles).Checked registry ∧
    (boundary roles).Initial registry root start ∧ (boundary roles).Models start model ∧
    (boundary roles).Stable registry start root ∧
    B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) ∧
    B4SkeletonV7.EvidenceAt (boundary roles) registry start root :=
  ⟨⟨rfl,checked⟩,alloc_initial,inhabited,stable,selected,evidenceAt⟩

end Yulang.GeneralDictionaryDefaultSelected204
