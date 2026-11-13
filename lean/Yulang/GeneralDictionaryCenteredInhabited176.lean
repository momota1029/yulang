import Yulang.GeneralNominalCenteredGroundBoundary

/-! A model-inhabited fragment of the actual centered relation. Merges in this
fragment identify only already-identical target names for each matching output
name. No claim is made that every execution of the ground boundary belongs to
this fragment. No action or guard of the original relation is changed. -/
namespace Yulang.GeneralDictionaryCenteredInhabited176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def OutputsAligned (first last : Site roles) : Prop :=
  ∀ a ∈ first.occurrence.demand.outputs, ∀ b ∈ last.occurrence.demand.outputs,
    a.name = b.name → a.target = b.target

inductive MergeAligned : {focus : Occurrence roles} → {after : State roles} →
    At registry before focus after → Prop where
  | administrative : MergeAligned (At.administrative focus after action)
  | refresh : MergeAligned (At.refresh focus context certificate source member unknown known)
  | install : MergeAligned (At.install plan support enabled novel packetGuard)
  | merge : OutputsAligned first last →
      MergeAligned (At.merge first last support one two same novel mergeGuard)

theorem aligned_output_atoms (first last : Site roles) (aligned : OutputsAligned first last)
    (model : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) := by
  apply (GeneralNominalDemandMerging.output_atoms_exact first.observed last.observed model).mpr
  intro a one b two same
  rw [aligned a one b two same]
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem aligned_merge_models (state : State roles) (first last : Site roles)
    (aligned : OutputsAligned first last) (support : List (Occurrence roles)) (model : Assignment) :
    Models (merge state first last support) model ↔ Models state model := by
  change (GeneralNominalSaturationState.Models
    (GeneralNominalSaturationState.merge state.erased.current first.observed last.observed) model ∧ _) ↔ _
  rw [GeneralNominalSaturationState.merge_models]
  constructor
  · rintro ⟨⟨old,_⟩,other⟩; exact ⟨old,other⟩
  · rintro ⟨old,other⟩; exact ⟨⟨old,aligned_output_atoms first last aligned model⟩,other⟩

theorem at_inhabited (action : At registry before focus after) (aligned : MergeAligned action)
    (inhabited : ∃ model, Models before model) : ∃ model, Models after model := by
  cases aligned with
  | @administrative focus after action =>
    obtain ⟨model,valid,rest⟩ := inhabited
    exact ⟨model,(GeneralNominalSupportSteps.administrative_models action model).mpr valid,rest⟩
  | @refresh focus context certificate source member unknown known =>
    obtain ⟨model,valid⟩ := inhabited
    exact ⟨model,(refresh_models certificate model).mpr valid⟩
  | @install plan support enabled novel guard =>
    obtain ⟨model,valid,holds⟩ := guard.2.2.2.2.2.2
    exact ⟨model,(install_models enabled.1.2.1 model).mpr ⟨valid,holds⟩⟩
  | merge aligned =>
    obtain ⟨model,valid⟩ := inhabited
    exact ⟨model,(aligned_merge_models _ _ _ aligned _ model).mpr valid⟩

def AlignedStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.erased.current root focus ∧
    ∃ action : At registry before focus after, MergeAligned action

theorem step_actual (step : AlignedStep registry root before after) : Step registry root before after := by
  obtain ⟨focus,generated,action,_⟩ := step
  exact ⟨focus,generated,action⟩

theorem step_inhabited (step : AlignedStep registry root before after)
    (inhabited : ∃ model, Models before model) : ∃ model, Models after model := by
  obtain ⟨focus,generated,action,aligned⟩ := step
  exact at_inhabited action aligned inhabited

theorem trace_actual (path : B4Target.Steps (AlignedStep registry root) before after) :
    B4Target.Steps (Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_actual step)

theorem trace_inhabited (path : B4Target.Steps (AlignedStep registry root) before after)
    (inhabited : ∃ model, Models before model) : ∃ model, Models after model := by
  induction path with
  | refl => exact inhabited
  | tail _ step ih => exact step_inhabited step ih

end Yulang.GeneralDictionaryCenteredInhabited176
