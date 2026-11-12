import Yulang.GeneralDictionaryEarlyMergeScalarJoint

/-! Full three-node dictionary semantics in every model of the actual merged
journal. No Stable premise or stability claim is used. -/
namespace Yulang.GeneralDictionaryEarlyMergeScalarEvidence
open GeneralDictionaryEarlyMergeScalarExample GeneralDictionaryEarlyMergeScalarClassification
open GeneralDictionaryEarlyMergeScalarJoint
open GeneralNominalExamples (model displayRoot intDisplay int_display_checked)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence

/-- Retained parent semantics replay in the SAME final model across both the
install and actual merge. This is not a re-selection in a fresh model. -/
theorem parent_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    Instance registry current assignment displayRoot 1 children := by
  have formed := GeneralNominalSupportBoundary.reachable_formed registry finish displayRoot reachable
  have old := (GeneralDictionarySupportJournal.recorded_instances registry displayRoot finish formed packet
    (List.mem_singleton_self _)).1 assignment valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context current
    (packets_grow packet (List.mem_singleton_self _)) assignment valid.1 displayRoot 1 children old

theorem child_instance (n : Nat) (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    Instance registry current assignment (child n) 3 [] :=
  GeneralDictionaryUnrecordedAliasLeafJoint.leaf_instance registry finish (child n) intDisplay (by simp)
    int_display_checked (Or.inr ⟨shape n⟩) 3 [] (supported_child n) assignment valid

theorem child_evidence (n : Nat) (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    Evidence registry current assignment (child n) (.node 3 []) :=
  (evidence_leaf_iff registry current assignment (child n) 3).mpr (child_instance n assignment valid)

abbrev payload : GeneralDictionaryReadback.Payload := .node 1 [.node 3 [],.node 3 []]

theorem full_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) : Evidence registry current assignment displayRoot payload := by
  apply evidence_node registry current assignment displayRoot 1 children _ (parent_instance assignment valid)
  rw [children_exact]
  exact .cons (child_evidence 10 assignment valid) (.cons (child_evidence 11 assignment valid) .nil)

theorem edges_exact : finish.current.edges = [(displayRoot,child 10),(displayRoot,child 11)] := by
  change [] ++ packet.children.map (fun child => (displayRoot,child)) = _
  change [] ++ children.map (fun child => (displayRoot,child)) = _
  rw [children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated finish.current displayRoot focus) :
    focus = displayRoot ∨ focus = child 10 ∨ focus = child 11 := by
  induction generated with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h
    · exact Or.inr (Or.inl (congrArg Prod.snd h))
    · exact Or.inr (Or.inr (congrArg Prod.snd h))
  | alias _ _ member _ _ =>
    rw [sites_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- Actual reached state is inhabited and validates the whole dictionary, not
only the two local alias-class branches. -/
theorem reachable_full_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ Evidence registry current model displayRoot payload :=
  ⟨reachable,finish_model,full_evidence model finish_model⟩
end Yulang.GeneralDictionaryEarlyMergeScalarEvidence
