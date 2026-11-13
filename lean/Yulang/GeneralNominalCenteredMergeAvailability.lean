import Yulang.GeneralNominalCenteredSelectedCompletion

/-! Equal center names always enable the provenance portion of merging.
For distinct names, the exact remaining test is equality in a raw support
slice, rather than equality only in the stronger centered model ledger. -/
namespace Yulang.GeneralNominalCenteredMergeAvailability
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection (Origin)

variable {roles : Roles.RoleDecls}

theorem recovered_inputs (state : GeneralNominalSaturationState.State roles) (site : Site roles) :
    (GeneralNominalFeedbackSites.recover state site.observed).inputs = site.observed.inputs :=
  GeneralDictionaryFeedbackEvidence.recover_inputs state site.observed
    (fun _input member equal => observed_total site (equal ▸ member))

theorem recovery_supported (state : GeneralNominalSupport.Tracked roles) (site : Site roles) (support) :
    GeneralNominalSupportChoices.RecoverySupported state site.observed support := by
  intro index absent
  exact False.elim (observed_total site (List.mem_of_getElem? absent))

theorem merge_guard_iff (state : State roles) (first last : Site roles) (support) :
    GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support ↔
      SameInputs (GeneralNominalSupport.Slice state.erased support) first last := by
  constructor
  · intro guard
    exact ⟨guard.1.1,by simpa only [recovered_inputs] using guard.1.2⟩
  · intro same
    exact ⟨⟨same.1,by simpa only [recovered_inputs] using same.2⟩,
      recovery_supported state.erased first support,recovery_supported state.erased last support⟩

private theorem source_list_reflexive (models : GeneralNominalCommonBridge.Assignment → Prop)
    (inputs : List (Option Origin)) (named : ∀ input ∈ inputs, ∃ source, input = some (.source source)) :
    GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related models) inputs inputs := by
  induction inputs with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨source,rfl⟩ := named first (List.mem_cons_self ..)
    exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same models source⟩
      (ih (fun input member => named input (List.mem_cons_of_mem _ member)))

theorem same_names (models : GeneralNominalCommonBridge.Assignment → Prop) (first last : Site roles)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) : SameInputs models first last := by
  refine ⟨role,?_⟩
  rw [← names]
  apply source_list_reflexive
  intro input member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact ⟨first.center index,rfl⟩

theorem same_names_merge_guard (state : State roles) (first last : Site roles)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) :
    GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed [] :=
  (merge_guard_iff state first last []).mpr (same_names _ first last role names)

theorem same_names_step (state : State roles) (first last : Site roles)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root first.occurrence)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs)
    (novel : ¬ GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity) :
    Step registry root state (merge state first last []) :=
  ⟨first.occurrence,generated,.merge first last [] one two (same_names _ first last role names) novel
    (same_names_merge_guard state first last role names)⟩

theorem stable_same_names_aliased (stable : Stable registry state root)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root first.occurrence)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) :
    GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity := by
  apply Classical.byContradiction
  intro novel
  exact stable first.occurrence generated _
    (.merge first last [] one two (same_names _ first last role names) novel (same_names_merge_guard state first last role names))

end Yulang.GeneralNominalCenteredMergeAvailability
