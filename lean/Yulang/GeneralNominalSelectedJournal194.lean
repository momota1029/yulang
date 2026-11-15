import Yulang.GeneralNominalJournalAccessibility194

set_option backward.isDefEq.respectTransparency false
/-! Actual selected payload soundness under syntactic journal coverage. -/
namespace Yulang.GeneralNominalSelectedJournal194
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

theorem survivor_of_instance {registry : Registry} {context : GeneralNominalCandidates.Context}
    {root : Occurrence roles} {selectedKey key : Nat} {selectedChildren children : List (Occurrence roles)}
    (selected : Survivor registry context root selectedKey selectedChildren)
    (model : Assignment)
    (instanceRule : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    Survivor registry context root key children := by
  obtain ⟨known,chosen,visible,check,id,role,bounds,located,prepared,emitted⟩ := selected
  obtain ⟨decl,present,checked,identity,declRole,intervals,found,finished,requests,kids,metadata,branch⟩ := instanceRule
  exact ⟨known,decl,present,checked,identity,declRole,intervals,found,
    ⟨metadata,prepared.2.1,prepared.2.2.1,intervals,found,finished,model,branch.1,branch.2.1⟩,kids⟩

theorem selected_instance {registry : Registry} {state : State roles} {focus : Occurrence roles}
    {key recordedKey : Nat} {children recordedChildren : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment)
    (instanceRule : GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model
      focus recordedKey recordedChildren) :
    recordedKey = key ∧ recordedChildren = children ∧
      GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children := by
  have same : recordedKey = key ∧ recordedChildren = children := by
    cases selected with
    | selected safe unique clear => exact unique.2 _ _ (survivor_of_instance unique.1 model instanceRule)
  exact ⟨same.1,same.2,same.1 ▸ same.2 ▸ instanceRule⟩


open GeneralDictionaryJournalTree (Covered Reach)
variable {registry : Registry} {context : GeneralNominalCandidates.Context}
variable {root : Occurrence roles} {state : State roles}

theorem selected_recorded
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (covered : Covered state.core.erased.current root)
    {focus : Occurrence roles} (reached : Reach state.core.erased.current root focus)
    {key : Nat} {children : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children ∧
      ∀ child ∈ children, Reach state.core.erased.current root child := by
  obtain ⟨packet,present,same⟩ := covered focus reached
  have source := GeneralNominalOrdinaryJournal194.packet_instance path packet present model valid
  rw [same] at source
  obtain ⟨_,kids,source⟩ := selected_instance selected model source
  refine ⟨source,?_⟩
  intro child member
  exact .child reached ⟨packet,present,same,kids ▸ member⟩

theorem classify_node_parts {v : B4Target.Vocabulary} {b : B4TargetV6.SourceBoundary v}
    {r : v.Registry} {s : v.State} {focus : v.Demand} {key : Nat} {payloads : List Payload}
    (derived : B4TargetV6.Classify b r s focus (.selected (.node key payloads))) :
    ∃ children, B4TargetV6.Local b r s focus (.selected key children) ∧
      All₂ (fun child payload => B4TargetV6.Classify b r s child (.selected payload)) children payloads := by
  cases derived with
  | selected safe unique clear children => exact ⟨_,.selected safe unique clear,children⟩

mutual
  theorem dictionary_evidence
      (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
        (initial context root) state)
      (covered : Covered state.core.erased.current root)
      (model : Assignment) (valid : Models state model) (dictionary : Payload)
      (focus : Occurrence roles) (reached : Reach state.core.erased.current root focus)
      (derived : B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) :
      (boundary roles).Evidence registry state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,selected,derivedChildren⟩ := classify_node_parts derived
      obtain ⟨source,childrenReached⟩ := selected_recorded path covered reached selected model valid
      exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children dictionaries source
        (dictionaries_evidence path covered model valid dictionaries children childrenReached derivedChildren)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence
      (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
        (initial context root) state)
      (covered : Covered state.core.erased.current root)
      (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
      (demands : List (Occurrence roles))
      (reached : ∀ focus ∈ demands, Reach state.core.erased.current root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ ((boundary roles).Evidence registry state model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence path covered model valid _ _ (reached _ (by simp)) first)
        (dictionaries_evidence path covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- The actual selected payload, not merely some existential journal dictionary,
is sound at every final model. Coverage and ordinary execution remain explicit. -/
theorem selected_sound
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (covered : Covered state.core.erased.current root) (dictionary : Payload)
    (derived : B4TargetV6.Classify (boundary roles) registry state root (.selected dictionary)) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root dictionary :=
  fun model valid => dictionary_evidence path covered model valid dictionary root .root derived
end Yulang.GeneralNominalSelectedJournal194
