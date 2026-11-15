import Yulang.GeneralDictionaryDefaultSelectedGeneration211
import Yulang.GeneralDictionaryDefaultComposition208
set_option backward.isDefEq.respectTransparency false


/-! The full dictionary-soundness projection needs selected-tree generation,
not production of every prospective child of an arbitrary selected parent. -/
namespace Yulang.GeneralDictionaryDefaultSoundness211
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralDictionaryDefaultSelectedGeneration211 (classified_generated)
open GeneralDictionaryDefaultExecutor208 (executor)
variable {roles : Roles.RoleDecls}

theorem children_classified {relation : α → β → Prop}
    (given : All₂ relation first last) (member : item ∈ first) :
    ∃ other, relation item other := by
  induction given with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | rest
      · exact ⟨_,head⟩
      · exact ih rest

theorem classify_node {v : B4Target.Vocabulary} {b : B4TargetV7.SourceBoundary v}
    {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat} {dictionaries : List CommonRoleOutermostResolver.Dictionary}
    (derived : B4TargetV7.Classify b r s d (.selected (.node key dictionaries))) :
    ∃ children, B4TargetV7.Local b r s d (.selected key children) ∧
      All₂ (fun child dictionary => B4TargetV7.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases derived with
  | selected selected children => exact ⟨_,selected,children⟩

mutual
  theorem dictionary_evidence
      (node : B4SkeletonV7.EvidenceNode (boundary roles))
      (value : Registry) (checked : (boundary roles).Checked value)
      (state : State roles) (root : Occurrence roles)
      (reachable : B4TargetV7.Reachable (boundary roles) value root state)
      (stable : ∀ demand, (boundary roles).Generated value state root demand →
        (boundary roles).Stable value state demand)
      (model) (valid : (boundary roles).Models state model)
      (dictionary : CommonRoleOutermostResolver.Dictionary) (focus : Occurrence roles)
      (derived : B4TargetV7.Classify (boundary roles) value state focus (.selected dictionary)) :
      (boundary roles).Evidence value state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨_,selected,children⟩ := classify_node derived
      have generated := GeneralDictionaryDefaultSelectedGeneration211.selected_generated reachable selected
      exact node value checked state root reachable model valid focus key _ dictionaries
          (Or.inr generated) (stable focus generated)
          (fun child member => stable child (classified_generated reachable
            (children_classified children member).choose_spec)) selected
          (dictionaries_evidence node value checked state root reachable stable model valid _ _ children)
    termination_by sizeOf dictionary

  theorem dictionaries_evidence
      (node : B4SkeletonV7.EvidenceNode (boundary roles))
      (value : Registry) (checked : (boundary roles).Checked value)
      (state : State roles) (root : Occurrence roles)
      (reachable : B4TargetV7.Reachable (boundary roles) value root state)
      (stable : ∀ demand, (boundary roles).Generated value state root demand →
        (boundary roles).Stable value state demand)
      (model) (valid : (boundary roles).Models state model)
      (dictionaries : List CommonRoleOutermostResolver.Dictionary) (demands : List (Occurrence roles))
      (derived : All₂ (fun d dictionary => B4TargetV7.Classify (boundary roles) value state d
        (.selected dictionary)) demands dictionaries) :
      All₂ (fun d dictionary => (boundary roles).Evidence value state model d dictionary) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence node value checked state root reachable stable model valid _ _ first)
        (dictionaries_evidence node value checked state root reachable stable model valid _ _ rest)
    termination_by sizeOf dictionaries
end

theorem dictionarySound (node : B4SkeletonV7.EvidenceNode (boundary roles)) :
    B4TargetV7.DictionarySound (boundary roles) (executor roles) := by
  intro value checked state root dictionary initial derived model valid
  have reachable := B4TargetV5.reachable_initial (B4TargetV7.prior (boundary roles)) initial
  have final := B4TargetV5.reachable_steps (B4TargetV7.prior (boundary roles)) reachable
    (GeneralDictionaryDefaultExecutor208.execution value checked state root reachable)
  obtain ⟨_,stable⟩ := GeneralDictionaryDefaultBoundary208.closure
    (GeneralDictionaryDefaultExecutor208.halted value checked state root reachable)
  exact dictionary_evidence node value checked _ root final stable model valid dictionary root derived

end Yulang.GeneralDictionaryDefaultSoundness211
