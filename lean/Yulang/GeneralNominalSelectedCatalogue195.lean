import Yulang.GeneralNominalReuseCatalogue195

/-! Selected-payload soundness with a finite mixed readback catalogue.
The final model and the classification state are never replaced by the catalogue. -/
namespace Yulang.GeneralNominalSelectedCatalogue195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryJournalTree (Covered Reach)
open GeneralNominalReuseCatalogue195
open GeneralNominalSelectedJournal194 (selected_instance classify_node_parts)
variable {roles : Roles.RoleDecls} {registry : Registry} {context : GeneralNominalCandidates.Context}
variable {root : Occurrence roles} {state : State roles} {plans : List (Plan roles)}

theorem selected_recorded
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (ready : ∀ plan ∈ plans, Reusable registry state plan)
    (covered : Covered (catalogue state plans) root)
    {focus : Occurrence roles} (reached : Reach (catalogue state plans) root focus)
    {key : Nat} {children : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children ∧
      ∀ child ∈ children, Reach (catalogue state plans) root child := by
  obtain ⟨packet,present,same⟩ := covered focus reached
  have source := packet_instance path ready packet present model valid
  rw [same] at source
  obtain ⟨_,kids,source⟩ := selected_instance selected model source
  refine ⟨source,?_⟩
  intro child member
  exact .child reached ⟨packet,present,same,kids ▸ member⟩

mutual
  theorem dictionary_evidence
      (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
        (initial context root) state)
      (ready : ∀ plan ∈ plans, Reusable registry state plan)
      (covered : Covered (catalogue state plans) root)
      (model : Assignment) (valid : Models state model) (dictionary : Payload)
      (focus : Occurrence roles) (reached : Reach (catalogue state plans) root focus)
      (derived : B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) :
      (boundary roles).Evidence registry state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,selected,derivedChildren⟩ := classify_node_parts derived
      obtain ⟨source,childrenReached⟩ := selected_recorded path ready covered reached selected model valid
      exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children dictionaries source
        (dictionaries_evidence path ready covered model valid dictionaries children childrenReached derivedChildren)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence
      (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
        (initial context root) state)
      (ready : ∀ plan ∈ plans, Reusable registry state plan)
      (covered : Covered (catalogue state plans) root)
      (model : Assignment) (valid : Models state model) (dictionaries : List Payload)
      (demands : List (Occurrence roles))
      (reached : ∀ focus ∈ demands, Reach (catalogue state plans) root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ ((boundary roles).Evidence registry state model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence path ready covered model valid _ _ (reached _ (by simp)) first)
        (dictionaries_evidence path ready covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- The actual selected payload, not merely some existential journal dictionary,
is sound at every final model. Coverage and ordinary execution remain explicit. -/
theorem selected_sound
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (ready : ∀ plan ∈ plans, Reusable registry state plan)
      (covered : Covered (catalogue state plans) root) (dictionary : Payload)
    (derived : B4TargetV6.Classify (boundary roles) registry state root (.selected dictionary)) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root dictionary :=
  fun model valid => dictionary_evidence path ready covered model valid dictionary root .root derived
end Yulang.GeneralNominalSelectedCatalogue195
