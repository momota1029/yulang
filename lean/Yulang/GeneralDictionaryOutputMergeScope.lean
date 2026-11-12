import Yulang.GeneralDictionaryOutputMergeReachable
import Yulang.GeneralDictionaryRecursiveEvidence

/-! The reachable nonempty-output merge does not produce child dictionaries:
its registry contains a role-0 parent only, while the children request role 1.
This conclusion is independent of assignments and does not assert stability. -/
namespace Yulang.GeneralDictionaryOutputMergeScope
open GeneralDictionaryOutputMergeReachable
open GeneralNominalSaturationState GeneralNominalJointCandidates
open GeneralDeclarationExamples (roles)

theorem child_no_branch (state : State roles) (n key : Nat)
    (model : GeneralNominalCommonBridge.Assignment) :
    ¬ BranchAt registry state (child n) key model := by
  rintro ⟨d,visible,checked,identity,role,rest⟩
  have same := List.mem_singleton.mp visible
  subst d
  cases role

theorem child_no_joint (state : State roles) (n key : Nat) :
    ¬ Joint registry state (child n) key := by
  rintro ⟨_,model,_,branch,_⟩
  exact child_no_branch state n key model branch

theorem child_no_instance (context : GeneralNominalCandidates.Context)
    (model : GeneralNominalCommonBridge.Assignment) (n key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ GeneralDictionaryRecursiveEvidence.Instance registry context model (child n) key children := by
  rintro ⟨d,visible,checked,identity,role,rest⟩
  have same := List.mem_singleton.mp visible
  subst d
  cases role

theorem child_no_evidence (context : GeneralNominalCandidates.Context)
    (model : GeneralNominalCommonBridge.Assignment) (n : Nat)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ GeneralDictionaryRecursiveEvidence.Evidence registry context model (child n) payload := by
  intro given
  have tree := (GeneralDictionaryRecursiveEvidence.evidence_iff_payload registry context model (child n) payload).mp given
  cases tree with
  | node instanceRule _ => exact child_no_instance context model n _ _ instanceRule

/-- The actual source-formed, modeled path and absence of child evidence
coexist. The missing role declaration, not an unmodeled journal, explains it. -/
theorem reachable_without_child_evidence :
    GeneralNominalSupportSteps.SourceFormed registry GeneralNominalExamples.displayRoot finish ∧
    Models finish.current GeneralNominalExamples.model ∧
    ∀ n payload, ¬ GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context
      GeneralNominalExamples.model (child n) payload :=
  ⟨finish_sourceformed,finish_model,child_no_evidence _ _⟩
end Yulang.GeneralDictionaryOutputMergeScope
