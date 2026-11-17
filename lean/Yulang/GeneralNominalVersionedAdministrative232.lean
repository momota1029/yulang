import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalCenteredHeadMatStepKernel
set_option backward.isDefEq.respectTransparency false

/-! Concrete mixed-journal enqueue/equate/merge transformers. Model restriction
uses the actual raw operation, not legacy semantic equality guards. Exact
merge semantics retains every legacy and versioned live-effect obligation. -/
namespace Yulang.GeneralNominalVersionedAdministrative232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

def change (state : State roles) (after : GeneralNominalSaturationState.State roles) : State roles :=
  ⟨GeneralNominalCenteredHeadMatStepJournal.change state.legacy after,state.plans,state.effects⟩

def enqueue (state : State roles) (focus : Occurrence roles) : State roles :=
  change state (GeneralNominalSaturationState.enqueue state.core.erased.current focus)

def equate (state : State roles) (first last : Nat) : State roles :=
  change state (GeneralNominalFeedbackSteps.equate state.core.erased.current first last)

def merge (state : State roles) (first last : Site roles) : State roles :=
  ⟨GeneralNominalCenteredHeadMatStepJournal.merge state.legacy first last,state.plans,state.effects⟩

theorem enqueue_models (valid : Models (enqueue state focus) model) : Models state model := by
  obtain ⟨legacy,plans,effects⟩ := valid
  refine ⟨?_,plans,?_⟩
  · refine ⟨legacy.1,legacy.2.1,?_,legacy.2.2.2.1,legacy.2.2.2.2.1,?_⟩
    · exact fun site member => legacy.2.2.1 site (List.mem_append_left _ member)
    · intro effect member
      have pair := legacy.2.2.2.2.2 effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := state.core) (after := (enqueue state focus).core)
          (fun _ h => List.mem_append_left _ h) (fun _ h => h)) pair.2⟩
  · intro effect member
    have pair := effects effect member
    exact ⟨pair.1,live_restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (enqueue state focus).core)
        (fun _ h => List.mem_append_left _ h) (fun _ h => h)) pair.2⟩

theorem equate_models (valid : Models (equate state first last) model) : Models state model := by
  obtain ⟨legacy,plans,effects⟩ := valid
  refine ⟨?_,plans,?_⟩
  · refine ⟨((GeneralNominalState.extend_models ..).mp legacy.1).1,
      legacy.2.1,legacy.2.2.1,legacy.2.2.2.1,legacy.2.2.2.2.1,?_⟩
    intro effect member
    have pair := legacy.2.2.2.2.2 effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (equate state first last).core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩
  · intro effect member
    have pair := effects effect member
    exact ⟨pair.1,live_restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (equate state first last).core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩

def LegacyLive (state : State roles) (first last : Site roles) (model : Assignment) : Prop :=
  ∀ effect ∈ state.legacy.effects, effect.Live (merge state first last).core model

def NewLive (state : State roles) (first last : Site roles) (model : Assignment) : Prop :=
  ∀ effect ∈ state.effects, effect.Live (merge state first last).core model

theorem merge_models : Models (merge state first last) model ↔
    Models state model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
      LegacyLive state first last model ∧ NewLive state first last model := by
  constructor
  · rintro ⟨legacy,plans,effects⟩
    obtain ⟨old,atoms,legacyLive⟩ := GeneralNominalCenteredHeadMatStepJournal.merge_models.mp legacy
    refine ⟨⟨old,plans,?_⟩,atoms,legacyLive,fun effect member => (effects effect member).2⟩
    intro effect member
    have pair := effects effect member
    exact ⟨pair.1,live_restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (merge state first last).core)
        (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)) pair.2⟩
  · rintro ⟨⟨legacy,plans,effects⟩,atoms,legacyLive,newLive⟩
    refine ⟨GeneralNominalCenteredHeadMatStepJournal.merge_models.mpr ⟨legacy,atoms,legacyLive⟩,
      plans,fun effect member => ⟨(effects effect member).1,newLive effect member⟩⟩

theorem merge_restrict (valid : Models (merge state first last) model) : Models state model :=
  (merge_models.mp valid).1

theorem change_plans : (change state after).plans = state.plans := rfl
theorem change_effects : (change state after).effects = state.effects := rfl
theorem merge_plans : (merge state first last).plans = state.plans := rfl
theorem merge_effects : (merge state first last).effects = state.effects := rfl

end Yulang.GeneralNominalVersionedAdministrative232
