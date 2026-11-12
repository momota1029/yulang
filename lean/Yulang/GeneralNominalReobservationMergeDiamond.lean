import Yulang.GeneralNominalReobservationSteps

/-! An actual transition diamond for demand merging and certified descriptor
replacement. Both second transitions are constructed from the first guards;
no second-edge existence or packet rebasing premise is supplied. -/
namespace Yulang.GeneralNominalReobservationMergeDiamond

open GeneralNominalSaturationState GeneralNominalReobservationSteps
open GeneralNominalDemandMerging (Site)
open GeneralSourceDictionaries (Occurrence)

variable {roles : Roles.RoleDecls} {state : State roles}

theorem recover_equal_models (before after : State roles)
    (same : ∀ model, Models before model ↔ Models after model) (site : Site roles) :
    GeneralNominalFeedbackSites.recover before site = GeneralNominalFeedbackSites.recover after site := by
  have models : Models before = Models after := funext fun model => propext (same model)
  unfold GeneralNominalFeedbackSites.recover
  congr 1
  apply congrArg List.ofFn
  funext index
  unfold GeneralNominalFeedbackSites.recoverOrigin GeneralNominalFeedbackSites.EndpointEqual
  rw [models]

theorem sameInputs_equal_models (before after : State roles)
    (same : ∀ model, Models before model ↔ Models after model) (first last : Site roles) :
    GeneralNominalFeedbackSites.SameInputs before first last ↔
      GeneralNominalFeedbackSites.SameInputs after first last := by
  have models : Models before = Models after := funext fun model => propext (same model)
  unfold GeneralNominalFeedbackSites.SameInputs
  rw [recover_equal_models before after same first,recover_equal_models before after same last,models]

theorem alias_of_same_edges {before after : State roles} (same : before.aliases = after.aliases)
    (given : Alias before first last) : Alias after first last := by
  induction given with
  | refl => exact .refl _
  | edge member => exact .edge (same ▸ member)
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

def merged (change : Revision state) (first last : Site roles) : Revision (merge state first last) where
  entries := change.entries
  catalogue := change.catalogue
  opaqueHeads := change.opaqueHeads
  domain := change.domain

theorem merged_result (change : Revision state) (first last : Site roles) :
    (merged change first last).result = merge change.result first last := rfl

theorem merged_certified (change : Revision state) (certified : Certified change) (first last : Site roles) :
    Certified (merged change first last) where
  raw := by
    intro model valid
    change GeneralNominalState.Models (GeneralNominalState.extend change.snapshot []
      (GeneralNominalDemandMerging.outputAtoms first last)) model at valid
    change GeneralNominalState.Models (GeneralNominalState.extend state.context.state []
      (GeneralNominalDemandMerging.outputAtoms first last)) model
    rw [GeneralNominalState.extend_models] at valid ⊢
    exact ⟨certified.raw model valid.1,valid.2⟩
  exact := by
    intro model
    rw [merged_result,merge_models,merge_models,certified.exact model]

theorem merged_improves (change : Revision state) (improved : Improves change) (first last : Site roles) :
    Improves (merged change first last) := improved

/-- The square uses the full public Step, including its Generated restriction.
The final states are literally equal, so all source observations agree there. -/
theorem merge_reobserve_diamond (registry : GeneralDeclarations.Registry) (root : Occurrence roles)
    (first last : Site roles) (one : first ∈ state.sites) (two : last ∈ state.sites)
    (generated : Generated state root first.occurrence)
    (inputs : GeneralNominalFeedbackSites.SameInputs state first last)
    (novel : ¬ Alias state first.occurrence.identity last.occurrence.identity)
    (change : Revision state) (certified : Certified change) (improved : Improves change) :
    Step registry root state (merge state first last) ∧
    Step registry root state change.result ∧
    Step registry root (merge state first last) (merge change.result first last) ∧
    Step registry root change.result (merge change.result first last) := by
  have refresh : Step registry root state change.result :=
    ⟨root,.root,.reobserve root change certified improved⟩
  refine ⟨⟨first.occurrence,generated,.ordinary _ (.merge first last one two inputs novel)⟩,refresh,?_,?_⟩
  · exact ⟨root,.root,.reobserve root (merged change first last) (merged_certified change certified first last)
      (merged_improves change improved first last)⟩
  · refine ⟨first.occurrence,generated_monotone refresh generated,.ordinary _ (.merge first last one two ?_ ?_)⟩
    · exact (sameInputs_equal_models state change.result (fun model => (certified.exact model).symm) first last).mp inputs
    · exact fun equal => novel (alias_of_same_edges (before := change.result) (after := state) rfl equal)

end Yulang.GeneralNominalReobservationMergeDiamond
