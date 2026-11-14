import Yulang.GeneralNominalSelectedCatalogue195

/-! Current structural completion supports semantic readback without a history
restriction or a caller-supplied finite catalogue. Existence of those current
witnesses is an explicit, strictly nonrecursive production obligation. -/
namespace Yulang.GeneralNominalCurrentCompletion195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalSaturationState (Generated)
open GeneralNominalReuseCatalogue195 (Reusable reusable_instance)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

/-- A source completion contract at each selected generated node. It contains
no recursive Evidence, classification tree, or final dictionary conclusion. -/
def SelectedCompletion (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus → ∀ key children,
    Local registry state focus (.selected key children) →
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ Reusable registry state plan

/-- Local structural completion at the existing state yields both the semantic
node and generated children. No ordinary-only trace is needed. -/
theorem selected_instance (complete : SelectedCompletion registry state root)
    {focus : Occurrence roles} (generated : Generated state.core.erased.current root focus)
    {key : Nat} {children : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children ∧
    ∀ child ∈ children, Generated state.core.erased.current root child := by
  obtain ⟨plan,same,reuse⟩ := complete focus generated key children selected
  have source := reusable_instance reuse model valid
  rw [same] at source
  obtain ⟨_,kids,source⟩ := GeneralNominalSelectedJournal194.selected_instance selected model source
  refine ⟨source,?_⟩
  intro child member
  exact .child generated (same ▸ reuse.2.2.2 child (kids ▸ member))

mutual
  theorem dictionary_evidence (complete : SelectedCompletion registry state root)
      (model : Assignment) (valid : Models state model) (dictionary : Payload)
      (focus : Occurrence roles) (generated : Generated state.core.erased.current root focus)
      (derived : B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) :
      (boundary roles).Evidence registry state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,selected,derivedChildren⟩ := GeneralNominalSelectedJournal194.classify_node_parts derived
      obtain ⟨source,childrenGenerated⟩ := selected_instance complete generated selected model valid
      exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children dictionaries source
        (dictionaries_evidence complete model valid dictionaries children childrenGenerated derivedChildren)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (complete : SelectedCompletion registry state root)
      (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
      (demands : List (Occurrence roles))
      (generated : ∀ focus ∈ demands, Generated state.core.erased.current root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ ((boundary roles).Evidence registry state model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence complete model valid _ _ (generated _ (by simp)) first)
        (dictionaries_evidence complete model valid _ _
          (fun focus member => generated focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- Every actual selected payload is sound from current completion, even after
nonordinary histories; this theorem does NOT supply completion from a history. -/
theorem selected_sound (complete : SelectedCompletion registry state root) (dictionary : Payload)
    (derived : B4TargetV6.Classify (boundary roles) registry state root (.selected dictionary)) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root dictionary :=
  fun model valid => dictionary_evidence complete model valid dictionary root .root derived

/-- Semantic node form for the actual WF/V6 boundary; structural completion,
not ordinary execution or whole-journal coverage, is the remaining premise. -/
theorem evidence_node (complete : SelectedCompletion registry state root)
    {focus : Occurrence roles} (generated : Generated state.core.erased.current root focus)
    {key : Nat} {children : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) (payloads : List Payload)
    (childrenEvidence : All₂ ((boundary roles).Evidence registry state model) children payloads) :
    (boundary roles).Evidence registry state model focus (.node key payloads) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children payloads
    (selected_instance complete generated selected model valid).1 childrenEvidence
end Yulang.GeneralNominalCurrentCompletion195
