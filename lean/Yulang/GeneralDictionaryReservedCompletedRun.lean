import Yulang.GeneralDictionaryReservedRefreshedStability
import Yulang.B4TargetV3Functionality

/-! Endpoint semantics of the actual reserved-output installation, equality
feedback and nominal refresh. No execution function or general progress theorem
is postulated. The finite boundary is the concrete fixture only. -/
namespace Yulang.GeneralDictionaryReservedCompletedRun
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration)
open GeneralDictionaryReservedNominalRefresh
open GeneralDictionaryReservedRefreshedClassification
open GeneralDictionaryReservedRefreshedStability
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState
open CommonRoleOutermostResolver

/-- The exact administrative history is installation, equality feedback, then
carrier-changing nominal refresh. Every edge is an existing actual Value Step. -/
theorem actual_stages :
    GeneralNominalValueSteps.Step registry root start installed ∧
    GeneralNominalValueSteps.Step registry root installed GeneralDictionaryReservedEqualityStep.after ∧
    GeneralNominalValueSteps.Step registry root GeneralDictionaryReservedEqualityStep.after refreshed :=
  ⟨value_install_step,GeneralDictionaryReservedEqualityStep.equality_step,refresh_step⟩

theorem actual_path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) start refreshed :=
  .tail (.tail (.tail .refl value_install_step) GeneralDictionaryReservedEqualityStep.equality_step) refresh_step

theorem initial : (GeneralNominalValueBoundary.boundary roles).Initial registry root start :=
  ⟨context,initial_source,rfl⟩

theorem halted (after : GeneralNominalSupport.Tracked roles) :
    ¬ GeneralNominalValueSteps.Step registry root refreshed after := by
  rintro ⟨focus,generated,action⟩
  exact stable focus generated after action

/-- Every finite continuation of the terminal state is empty up to state equality. -/
theorem continuation_eq (after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) refreshed after) :
    after = refreshed := by
  induction path with
  | refl => rfl
  | tail previous step ih =>
    subst_vars
    exact False.elim (halted _ step)

theorem resolved : Resolves
    (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry refreshed)
    root (.selected declaration.id []) := by
  simpa only [B4TargetV3.render,B4TargetV3.renders] using
    B4TargetV3.render_resolves (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry refreshed (.node declaration.id []) root classified

theorem completed : B4TargetV3.Completed (.selected declaration.id [])
    (.selected (.node declaration.id [])) := .selected .nil

theorem resolves_iff (tree : Tree) :
    Resolves
      (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry refreshed)
      root tree ↔ tree = .selected declaration.id [] := by
  constructor
  · intro derived
    exact B4TargetV3.resolves_functional _ _ _ _ _ _ derived resolved
  · rintro rfl; exact resolved

theorem classify_iff (outcome : Result) :
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry refreshed root outcome ↔ outcome = .selected (.node declaration.id []) := by
  constructor
  · intro derived
    exact B4TargetV3.classify_functional derived classified
  · rintro rfl; exact classified

/-- This is an actual initial-to-terminal sound run for one concrete demand,
not the universal B4 Statement or an assumed solver's exactness certificate. -/
theorem initial_terminal_sound_run :
    (GeneralNominalValueBoundary.boundary roles).Initial registry root start ∧
    B4Target.Steps (GeneralNominalValueSteps.Step registry root) start refreshed ∧
    (∀ after, ¬ GeneralNominalValueSteps.Step registry root refreshed after) ∧
    Resolves
      (B4TargetV3.Local (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry refreshed)
      root (.selected declaration.id []) ∧
    B4TargetV3.Completed (.selected declaration.id []) (.selected (.node declaration.id [])) ∧
    Models refreshed.current positive ∧
    ∀ model, Models refreshed.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context model root
        (.node declaration.id []) :=
  ⟨initial,actual_path,halted,resolved,completed,refreshed_inhabited,
    GeneralDictionaryReservedRefreshedEvidence.current_evidence⟩
end Yulang.GeneralDictionaryReservedCompletedRun
