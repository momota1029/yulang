import Yulang.GeneralNominalFeedbackDescent
import Yulang.B4SkeletonV3

/-! Five exact V3 bridge fields for the additive journal-aware boundary.
Evidence stays explicit. General installation descent and unconditional where
accessibility remain source obligations; no executor is supplied. -/
namespace Yulang.GeneralNominalFeedbackBoundary

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver (Frontier Protocol Child)

abbrev vocabulary := GeneralNominalCycleBoundary.vocabulary

abbrev Evidence (roles : Roles.RoleDecls) := Registry → State roles → GeneralNominalCommonBridge.Assignment →
  Occurrence roles → CommonRoleOutermostResolver.Dictionary → Prop

def remaining (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := GeneralNominalFeedbackSteps.Step
  Stable := GeneralNominalFeedbackSteps.Stable
  Generated := fun _ state => Generated state
  Evidence := evidence

def boundary (roles : Roles.RoleDecls) (evidence : Evidence roles) : B4Target.SourceBoundary (vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalFeedbackK2.fields roles) (remaining roles evidence)

theorem local_correspondence (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (state : State roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles evidence) registry state root frontier ↔
      GeneralNominalFeedbackK2.Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles evidence) frontier).symm

noncomputable def frontiers (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then
        Classical.choose (GeneralNominalFeedbackK2.local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles evidence) registry state }

theorem localIdentity (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry state, (frontiers roles evidence registry state).Local =
      B4TargetV3.Local (boundary roles evidence) registry state := fun _ _ => rfl

theorem frontierLocal (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry, (boundary roles evidence).Checked registry → ∀ state root frontier,
      (frontiers roles evidence registry state).frontier root = frontier ↔
        B4TargetV3.Local (boundary roles evidence) registry state root frontier := by
  classical
  intro registry checked state root frontier
  have valid := Classical.choose_spec (GeneralNominalFeedbackK2.local_total registry checked.2 state root)
  change (if checked : Checked registry then
      Classical.choose (GeneralNominalFeedbackK2.local_total registry checked state root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence roles evidence registry state root frontier).mpr valid
  · intro localRule
    exact GeneralNominalFeedbackK2.local_functional valid
      ((local_correspondence roles evidence registry state root frontier).mp localRule)

theorem stepModels (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry, (boundary roles evidence).Checked registry → ∀ root before after,
      (boundary roles evidence).Step registry root before after → ∀ model,
        (boundary roles evidence).Models after model → (boundary roles evidence).Models before model :=
  fun _ _ _ _ _ step model valid => GeneralNominalFeedbackSteps.step_models step model valid

theorem closure (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry, (boundary roles evidence).Checked registry → ∀ state root,
      (∀ after, ¬ (boundary roles evidence).Step registry root state after) →
      (boundary roles evidence).Stable registry state root ∧ ∀ child,
        (boundary roles evidence).Generated registry state root child →
          (boundary roles evidence).Stable registry state child := fun _ _ _ _ halted => GeneralNominalFeedbackSteps.closure halted

theorem dictionaryRefl (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ dictionary, (boundary roles evidence).DictionaryEquivalent dictionary dictionary :=
  GeneralDictionaryPayloadOrder.equivalent_refl

theorem whereAccessible_of_readback (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (checked : (boundary roles evidence).Checked registry) (state : State roles)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.context) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local (boundary roles evidence) registry state)) root := by
  have accessible := GeneralNominalCycleReadback.whereAccessible checked.2 readback root
  induction accessible with
  | intro root below ih =>
    refine Acc.intro root ?_
    rintro child ⟨key,children,localRule,member⟩
    exact ih child ⟨key,children,GeneralNominalFeedbackK2.selected_legacy
      ((local_correspondence roles evidence registry state root _).mp localRule),member⟩

theorem step_preserves_formation (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (step : (boundary roles evidence).Step registry root before after) :
    GeneralNominalFeedbackSteps.SourceFormed registry root after := .update formed step

theorem models_trace (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps ((boundary roles evidence).Step registry root) before after)
    (model : GeneralNominalCommonBridge.Assignment) (valid : (boundary roles evidence).Models after model) :
    (boundary roles evidence).Models before model := GeneralNominalFeedbackSteps.steps_models path model valid

theorem progress_of_installation_descent (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (root : Occurrence roles)
    (descent : GeneralNominalFeedbackDescent.InstallationDescent registry root)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state) :
    Acc (fun next current => (boundary roles evidence).Step registry root current next) state :=
  GeneralNominalFeedbackDescent.accessible_of_installation_descent descent state formed

theorem survivor_unchanged (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    (boundary roles evidence).Survivor registry state root key children ↔
      GeneralNominalRecursiveCandidates.Survivor registry state.context root key children := Iff.rfl

end Yulang.GeneralNominalFeedbackBoundary
