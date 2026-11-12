import Yulang.GeneralDictionaryNamedLocality
import Yulang.GeneralDictionaryRecordedCoverageLimit

/-! Nonempty operational witness for the syntactic named-locality discipline. -/
namespace Yulang.GeneralDictionaryNamedLocalityExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)

def names (identity : Nat) : GeneralSourceDictionaries.Occurrence roles :=
  if identity = displayRoot.identity then displayRoot else displayChild

theorem root_named : names displayRoot.identity = displayRoot := by simp [names]

theorem child_named : names displayChild.identity = displayChild := by
  have different : displayChild.identity ≠ displayRoot.identity := by decide +kernel
  simp only [names,ite_eq_right different]

/-- The existing successful installation obeys the naming discipline; this
certificate retains every original operational premise, guard and novelty check. -/
theorem actual_trace : B4Target.Steps
    (GeneralDictionaryNamedLocality.Step names registry displayRoot) start finish := by
  apply B4Target.Steps.tail B4Target.Steps.refl
  refine ⟨displayRoot,.root,.install packet [] enabled ?_ GeneralNominalSupportExamples.display_guard ?_⟩
  · intro committed
    have impossible := committed.2 displayChild (by rw [children_exact]; simp)
    cases impossible
  · intro child member
    rw [children_exact] at member
    have same := List.mem_singleton.mp member
    subst child
    exact child_named

/-- No final-state locality or empty-alias premise is supplied by the caller. -/
theorem every_model_joint (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    GeneralNominalJointCandidates.Joint registry finish.current displayRoot 1 :=
  GeneralDictionaryNamedLocality.initial_joint names registry displayRoot displayRoot
    (context true) initial_source root_named finish actual_trace packet (List.mem_singleton_self _) rfl
    1 [displayChild] supported_parent_selected assignment valid
end Yulang.GeneralDictionaryNamedLocalityExample
