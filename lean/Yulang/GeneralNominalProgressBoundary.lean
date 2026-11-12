import Yulang.GeneralNominalAdministrativeProgress
import Yulang.GeneralNominalSourceReadback
import Yulang.GeneralNominalReadbackCounterexample
import Yulang.B4SkeletonV3

/-! An explicit source boundary with Evidence as its only field parameter.
Five V3 bridge fields are established for these certified source relations.
The source-completeness gaps of the local fields and global Step progress are
not hidden in SourceFormed or in the evidence parameter. -/
namespace Yulang.GeneralNominalProgressBoundary

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver (Frontier Protocol Child)

abbrev vocabulary := GeneralNominalCycleBoundary.vocabulary

abbrev Evidence (roles : Roles.RoleDecls) := Registry → State roles → GeneralNominalCommonBridge.Assignment →
  Occurrence roles → CommonRoleOutermostResolver.Dictionary → Prop

def remaining (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := GeneralNominalCycleSteps.Step
  Stable := GeneralNominalCycleSteps.Stable
  Generated := fun _ state => Generated state
  Evidence := evidence

def boundary (roles : Roles.RoleDecls) (evidence : Evidence roles) : B4Target.SourceBoundary (vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalCycleBoundary.localFields roles) (remaining roles evidence)

theorem local_correspondence (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (state : State roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles evidence) registry state root frontier ↔
      GeneralNominalCycleK2.Local registry state.context root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles evidence) frontier).symm.trans
    (GeneralNominalCycleBoundary.local_projection registry state root frontier)

noncomputable def frontiers (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then
        Classical.choose (GeneralNominalCycleK2.local_total registry checked state.context root) else .pending
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
  have valid := Classical.choose_spec (GeneralNominalCycleK2.local_total registry checked.2 state.context root)
  change (if checked : Checked registry then
      Classical.choose (GeneralNominalCycleK2.local_total registry checked state.context root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence roles evidence registry state root frontier).mpr valid
  · intro localRule
    exact GeneralNominalCycleK2.local_functional valid
      ((local_correspondence roles evidence registry state root frontier).mp localRule)

theorem stepModels (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry, (boundary roles evidence).Checked registry → ∀ root before after,
      (boundary roles evidence).Step registry root before after → ∀ model,
        (boundary roles evidence).Models after model → (boundary roles evidence).Models before model :=
  GeneralNominalCycleBoundary.stepModels roles

theorem closure (roles : Roles.RoleDecls) (evidence : Evidence roles) :
    ∀ registry, (boundary roles evidence).Checked registry → ∀ state root,
      (∀ after, ¬ (boundary roles evidence).Step registry root state after) →
      (boundary roles evidence).Stable registry state root ∧ ∀ child,
        (boundary roles evidence).Generated registry state root child →
          (boundary roles evidence).Stable registry state child := GeneralNominalCycleBoundary.closure roles

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
    exact ih child ⟨key,children,(local_correspondence roles evidence registry state root _).mp localRule,member⟩

theorem step_preserves_formation (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (formed : GeneralNominalSourceFormation.SourceFormed registry root before)
    (step : (boundary roles evidence).Step registry root before after) :
    GeneralNominalSourceFormation.SourceFormed registry root after := .update formed step

theorem models_trace (roles : Roles.RoleDecls) (evidence : Evidence roles)
    (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps ((boundary roles evidence).Step registry root) before after)
    (model : GeneralNominalCommonBridge.Assignment) (valid : (boundary roles evidence).Models after model) :
    (boundary roles evidence).Models before model := GeneralNominalCycleSteps.steps_models path model valid

end Yulang.GeneralNominalProgressBoundary
