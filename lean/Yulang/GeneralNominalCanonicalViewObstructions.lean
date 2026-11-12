import Yulang.GeneralNominalRefreshDivergence

/-! Maximality of Known sources does not make the existing observation view
canonical. Both halted refresh outcomes already satisfy that condition, while
literal preservation of nominal descriptors prevents the precision repair. -/
namespace Yulang.GeneralNominalCanonicalViewObstructions

open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalRefreshFork GeneralNominalRefreshDivergence
open GeneralDeclarationExamples (roles)

/-- Every supported source that an old certified refresh could make Known is
already Known. This concerns head availability, not descriptor precision. -/
def KnownMaximal {roleDecls : Roles.RoleDecls} (snapshot : State roleDecls) : Prop :=
  ∀ next : GeneralNominalCandidates.Context,
    GeneralNominalFeedbackSteps.Refresh snapshot next →
    ∀ source ∈ GeneralNominalState.sources snapshot.context.state,
      GeneralNominalState.Known next.state source →
        GeneralNominalState.Known snapshot.context.state source

theorem fork_knownMaximal (wide : Bool) : KnownMaximal (after wide) := by
  classical
  intro next certificate source member known
  by_cases current : GeneralNominalState.Known (state (some wide)) source
  · exact current
  · exact False.elim (no_refresh wide next certificate source member current known)

theorem wide_cannot_refine_to_point :
    ¬ Nonempty (GeneralNominalRefinements.Refines (state (some true)) (state (some false))) := by
  rintro ⟨refinement⟩
  have source (slot : Fin 5) : refinement.base.embed slot = slot :=
    Fin.ext (refinement.base.source slot)
  have descriptorEq := refinement.nominals (0 : Fin 5) (descriptor (2,4)) rfl
  rw [source] at descriptorEq
  have argumentsEq := congrArg GeneralNominalState.Descriptor.arguments (Option.some.inj descriptorEq)
  change ([.type (2,2)] : List (GeneralNominalState.Parameter 5)) =
    [.type (refinement.base.embed 2,refinement.base.embed 4)] at argumentsEq
  rw [source,source] at argumentsEq
  cases argumentsEq

theorem wide_cannot_refresh_to_point :
    ¬ Nonempty (GeneralNominalFeedbackSteps.Refresh (after true) (context (some false))) := by
  rintro ⟨certificate⟩
  exact wide_cannot_refine_to_point ⟨certificate.refines⟩

/-- Adding Known maximality to old stability leaves the actual reachable,
inhabited, model-equivalent fork intact. -/
theorem knownMaximal_stable_fork :
    (GeneralDictionaryReachableBoundary.boundary roles).Checked registry ∧
    (GeneralDictionaryReachableBoundary.boundary roles).Initial registry root before ∧
    (∀ wide, B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles)
      registry root (after wide)) ∧
    (∀ wide, KnownMaximal (after wide) ∧ GeneralNominalFeedbackSteps.Stable registry (after wide) root) ∧
    (∀ wide model, Models (after wide) model ↔ Models before model) ∧
    Models before model ∧
    ¬ (∀ demand frontier,
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false) demand frontier ↔
        B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after true) demand frontier) :=
  ⟨⟨rfl,registry_checked⟩,⟨context none,initial_source,rfl⟩,after_reachable,
    fun wide => ⟨fork_knownMaximal wide,stable wide⟩,same_models,initial_models,different_local⟩

/-- The failure is at the shared initial execution domain, even after requiring
equal models and the proposed additional Known closure on both endpoints. -/
theorem not_knownMaximal_stable_confluence :
    ¬ (∀ first last : State roles,
      B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before first →
      B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before last →
      GeneralNominalFeedbackSteps.Stable registry first root →
      GeneralNominalFeedbackSteps.Stable registry last root →
      KnownMaximal first → KnownMaximal last →
      (∀ assignment, Models first assignment ↔ Models last assignment) →
      ∀ demand frontier,
        B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry first demand frontier ↔
          B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry last demand frontier) := by
  intro agree
  exact different_local (agree (after false) (after true)
    (.tail .refl (refresh_step false)) (.tail .refl (refresh_step true))
    (stable false) (stable true) (fork_knownMaximal false) (fork_knownMaximal true)
    (fun assignment => (same_models false assignment).trans (same_models true assignment).symm))

end Yulang.GeneralNominalCanonicalViewObstructions
