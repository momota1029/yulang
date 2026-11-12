import Yulang.GeneralDictionaryEarlyMergeDiagnostics
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Semantic absence for this specific inhabited merged fixture. Its only
visible declaration requires List, while its where children are Int. This does
not assume or assert a general rejected-to-no-Evidence implication. -/
namespace Yulang.GeneralDictionaryEarlyMergeNoEvidence
open GeneralDictionaryEarlyMergeExample
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
open GeneralNominalExamples (displayRoot model)

/-- Inspection itself rules out the only visible declaration, independently of
which valuation or candidate key is proposed. -/
theorem child_no_instance (n : Nat) (valuation : GeneralNominalCommonBridge.Assignment)
    (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)) :
    ¬ Instance registry finish.current.context valuation (child n) key children := by
  rintro ⟨decl,visible,check,identity,role,bounds,located,finished,rest⟩
  have eq := List.mem_singleton.mp visible
  subst decl
  have locatedHere : arguments finish.current.context (child n) = some [((1 : Fin 2),(1 : Fin 2))] := rfl
  have eq := Option.some.inj (located.symm.trans locatedHere)
  subst bounds
  have failed : ¬ Finished (report finish.current.context declaration [((1 : Fin 2),(1 : Fin 2))]) := by
    unfold Finished
    decide +kernel
  exact failed finished

/-- No payload supplies recursive source evidence for either Int where child. -/
theorem child_no_evidence (n : Nat) (valuation : GeneralNominalCommonBridge.Assignment)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry finish.current.context valuation (child n) payload := by
  intro evidence
  cases payload with
  | node key dictionaries =>
    obtain ⟨children,rule,all⟩ := evidence_node_elim registry finish.current.context valuation (child n) key dictionaries evidence
    exact child_no_instance n valuation key children rule

/-- A semantic parent witness must contain every emitted where child, so its
failed first child prevents every parent payload, not only the shown syntax. -/
theorem root_no_evidence (valuation : GeneralNominalCommonBridge.Assignment)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry finish.current.context valuation displayRoot payload := by
  intro evidence
  cases payload with
  | node key dictionaries =>
    obtain ⟨emitted,rule,all⟩ := evidence_node_elim registry finish.current.context valuation displayRoot key dictionaries evidence
    have same := (GeneralDictionarySelectedInstanceCoherence.instance_selected registry finish.current displayRoot
      valuation key 1 emitted children rule GeneralDictionaryEarlyMergeDiagnostics.parent_selected).2
    rw [same,children_exact] at all
    cases all with
    | cons first rest => exact child_no_evidence 10 valuation _ first

/-- The semantic absence is witnessed at an actually reachable nonempty,
inhabited merged journal; it is not an empty-model argument. -/
theorem inhabited_no_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry displayRoot finish ∧
    GeneralNominalSaturationState.Models finish.current model ∧
    finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] ∧
    ∀ payload, ¬ Evidence registry finish.current.context model displayRoot payload :=
  ⟨reachable,finish_model,actual_early_merge.2.2.1,actual_early_merge.2.2.2,root_no_evidence model⟩

end Yulang.GeneralDictionaryEarlyMergeNoEvidence
