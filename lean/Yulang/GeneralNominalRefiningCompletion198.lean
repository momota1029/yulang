import Yulang.GeneralNominalRefiningJournal198
import Yulang.GeneralNominalMixedCompletion198
import Yulang.GeneralNominalCurrentCompletion195
import Yulang.GeneralNominalJournalAccessibility194

/-! Actual journal recovery and current unrecorded reuse in one nonrecursive
completion rule. The original final state supplies every model. -/
namespace Yulang.GeneralNominalRefiningCompletion198
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalSaturationState (Generated)
open GeneralNominalReuseCatalogue195 (Reusable reusable_instance)
open GeneralNominalRefiningJournal198 (MixedStep)
open GeneralNominalMixedCompletion198 (Rule NodeAvailable SelectedCompletion TotalCompletion)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {context : GeneralNominalCandidates.Context} {root : Occurrence roles}

theorem node_instance (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (rule : Rule registry state focus key children)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children := by
  rcases rule with recorded | ⟨plan,reuse,rfl,rfl,rfl⟩
  · obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
    exact GeneralNominalRefiningJournal198.packet_instance path packet present model valid
  · exact reusable_instance reuse model valid

theorem packet_edges
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : packet ∈ state.core.erased.current.packets) :
    ∀ child ∈ packet.children, (packet.site.occurrence,child) ∈ state.core.erased.current.edges := by
  induction path with
  | refl => cases recorded
  | @tail before after path action ih =>
    obtain ⟨focus,generated,update⟩ := action.1
    cases update with
    | install plan support enabled novel =>
      rcases List.mem_cons.mp recorded with rfl | member
      · exact fun child within => List.mem_append_right _ (List.mem_map.mpr ⟨child,within,rfl⟩)
      · exact fun child within => List.mem_append_left _ (ih member child within)
    | administrative focus next update =>
      have prior : packet ∈ before.core.erased.current.packets := by cases update <;> exact recorded
      exact fun child within =>
        (GeneralNominalReobservationSteps.at_extends
          (GeneralNominalSupportSteps.administrative_old update)).journal.edges _ (ih prior child within)
    | refresh => exact ih recorded
    | merge => exact ih recorded

theorem children_generated
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (rule : Rule registry state focus key children)
    (generated : Generated state.core.erased.current root focus) :
    ∀ child ∈ children, Generated state.core.erased.current root child := by
  rcases rule with recorded | ⟨plan,reuse,rfl,rfl,rfl⟩
  · obtain ⟨packet,present,rfl,rfl,rfl⟩ := recorded
    intro child member
    exact .child generated (packet_edges path packet present child member)
  · exact fun child member => .child generated (reuse.2.2.2 child member)

theorem selected_instance
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (complete : SelectedCompletion registry state root)
    (generated : Generated state.core.erased.current root focus)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model focus key children ∧
    ∀ child ∈ children, Generated state.core.erased.current root child := by
  obtain ⟨other,kids,rule⟩ := complete focus generated key children selected
  have source := node_instance path rule model valid
  obtain ⟨same,sameChildren,source⟩ := GeneralNominalSelectedJournal194.selected_instance selected model source
  exact ⟨source, sameChildren ▸ children_generated path rule generated⟩

mutual
  theorem dictionary_evidence
      (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
      (complete : SelectedCompletion registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
      (dictionary : Payload) (focus : Occurrence roles)
      (generated : Generated state.core.erased.current root focus)
      (derived : B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) :
      (boundary roles).Evidence registry state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,selected,derivedChildren⟩ := GeneralNominalSelectedJournal194.classify_node_parts derived
      obtain ⟨source,childrenGenerated⟩ := selected_instance path complete generated selected model valid
      exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children dictionaries source
        (dictionaries_evidence path complete model valid dictionaries children childrenGenerated derivedChildren)
  termination_by sizeOf dictionary
  theorem dictionaries_evidence
      (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
      (complete : SelectedCompletion registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
      (dictionaries : List Payload) (demands : List (Occurrence roles))
      (generated : ∀ focus ∈ demands, Generated state.core.erased.current root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ ((boundary roles).Evidence registry state model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence path complete model valid _ _ (generated _ (by simp)) first)
        (dictionaries_evidence path complete model valid _ _
          (fun focus member => generated focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

theorem selected_sound
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (complete : SelectedCompletion registry state root) (dictionary : Payload)
    (derived : B4TargetV6.Classify (boundary roles) registry state root (.selected dictionary)) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root dictionary :=
  fun model valid => dictionary_evidence path complete model valid dictionary root .root derived

theorem evidence_node
    (path : B4Target.Steps (MixedStep registry root) (initial context root) state)
    (complete : SelectedCompletion registry state root)
    (generated : Generated state.core.erased.current root focus)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (payloads : List Payload)
    (childEvidence : All₂ ((boundary roles).Evidence registry state model) children payloads) :
    (boundary roles).Evidence registry state model focus (.node key payloads) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children payloads
    (selected_instance path complete generated selected model valid).1 childEvidence

theorem selected_completion (complete : TotalCompletion registry state root) :
    SelectedCompletion registry state root := fun focus generated _ _ _ => complete focus generated
end Yulang.GeneralNominalRefiningCompletion198
