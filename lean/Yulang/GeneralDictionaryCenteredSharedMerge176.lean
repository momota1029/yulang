import Yulang.GeneralNominalCenteredGroundBoundary

/-! Equal actual input names need no conditional model-equality or support
witness to merge. The theorem concerns registered centered sites, not every
pair of raw recovered sites with semantically equal intervals. -/
namespace Yulang.GeneralDictionaryCenteredSharedMerge176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalRecursiveInspection (Origin)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

private theorem same_sources (models : GeneralNominalCommonBridge.Assignment → Prop)
    {count : Nat} (names : Fin count → Nat) :
    GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related models)
      (List.ofFn fun index => some (Origin.source (names index)))
      (List.ofFn fun index => some (Origin.source (names index))) := by
  induction count with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ count ih =>
    rw [List.ofFn_succ]
    exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same models _⟩ (ih _)

theorem same_named_inputs (models : GeneralNominalCommonBridge.Assignment → Prop)
    (first last : Site roles)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) : SameInputs models first last := by
  refine ⟨role,?_⟩
  rw [← names]
  exact same_sources models first.center

private theorem raw_ext (first last : GeneralNominalDemandMerging.Site roles)
    (occurrence : first.occurrence = last.occurrence) (inputs : first.inputs = last.inputs) : first = last := by
  cases first
  cases last
  cases occurrence
  cases inputs
  rfl

theorem recovered_observed (state : GeneralNominalSaturationState.State roles) (site : Site roles) :
    GeneralNominalFeedbackSites.recover state site.observed = site.observed := by
  apply raw_ext (GeneralNominalFeedbackSites.recover state site.observed) site.observed (by rfl)
  change List.ofFn _ = List.ofFn _
  congr 1
  funext index
  simp only [GeneralNominalFeedbackSites.recoverOrigin,Site.observed,List.getElem_ofFn]
  congr 2

theorem named_merge_guard (state : State roles) (first last : Site roles)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) :
    GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed [] := by
  refine ⟨?_,?_,?_⟩
  · rw [recovered_observed,recovered_observed]
    exact same_named_inputs _ first last role names
  · intro index absent
    simp [Site.observed,List.getElem?_ofFn] at absent
  · intro index absent
    simp [Site.observed,List.getElem?_ofFn] at absent

theorem stable_named_alias (stable : Stable registry state root)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (generated : Generated state.erased.current root first.occurrence)
    (role : first.occurrence.demand.role = last.occurrence.demand.role)
    (names : first.observed.inputs = last.observed.inputs) :
    Alias state.erased.current first.occurrence.identity last.occurrence.identity := by
  classical
  apply Classical.byContradiction
  intro apart
  exact stable first.occurrence generated _ (.merge first last [] one two
    (same_named_inputs _ first last role names) apart (named_merge_guard state first last role names))

end Yulang.GeneralDictionaryCenteredSharedMerge176
