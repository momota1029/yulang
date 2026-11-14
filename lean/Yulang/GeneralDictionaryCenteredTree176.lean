import Yulang.GeneralDictionaryCenteredFlexible176
import Yulang.GeneralDictionarySharedRecordedTree

/-! Whole finite journal trees interpreted in the final centered model.
The syntax is the existing RecordedTree, not a new dictionary judgment. Child
Evidence is derived recursively, not assumed. Tree existence is NOT deduced
from Stable or classification, and unrestricted centered refresh is not covered. -/
namespace Yulang.GeneralDictionaryCenteredTree176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence
open GeneralDictionaryCenteredFlexible176 (RecordedCurrent)
open GeneralDictionarySharedRecordedTree (RecordedTree)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root occurrence : Occurrence roles}
variable {state : State roles} {payload : Payload}

/-- No child Evidence hypothesis: induction over the finite recorded syntax
uses each parent's derived current-context Instance in the SAME model. -/
theorem current_evidence (recorded : RecordedCurrent registry state)
    (tree : RecordedTree state.erased.current occurrence payload)
    (model : Assignment) (valid : Models state model) :
    Evidence registry state.erased.current.context model occurrence payload := by
  induction tree using RecordedTree.rec
    (motive_2 := fun sites payloads _ => All₂
      (Evidence registry state.erased.current.context model) sites payloads) with
  | node packet member dictionaries children ih =>
    exact evidence_node _ _ _ _ _ _ _ (recorded packet member model valid) ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

/-- Actual centered restricted-refresh execution derives the parent-instance
invariant from an empty initial journal; only final syntactic tree membership
and the specified final centered model remain as hypotheses. -/
theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (GeneralDictionaryCenteredFlexible176.Step registry root)
      (initial context root) state)
    (tree : RecordedTree state.erased.current occurrence payload)
    (model : Assignment) (valid : Models state model) :
    Evidence registry state.erased.current.context model occurrence payload :=
  current_evidence (GeneralDictionaryCenteredFlexible176.initial_trace_recorded context path) tree model valid

/-- The same syntax also certifies the existing structural discharged judgment. -/
theorem initial_trace_certificate (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (GeneralDictionaryCenteredFlexible176.Step registry root)
      (initial context root) state)
    (tree : RecordedTree state.erased.current occurrence payload) :
    GeneralNominalSupport.Discharged state.erased.current occurrence ∧
    ∀ model, Models state model →
      Evidence registry state.erased.current.context model occurrence payload :=
  ⟨GeneralDictionarySharedRecordedTree.discharged tree,initial_trace_evidence context path tree⟩

end Yulang.GeneralDictionaryCenteredTree176
