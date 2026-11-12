import Yulang.GeneralNominalReobservationSteps
import Yulang.GeneralNominalCanonicalViewObstructions

/-! Repair of the previous inhabited refresh fork by an actual descriptor
replacement. Both branches reach the same point observation and the same
selected diagnostic. Full maximal-observation inspection is a separate task. -/
namespace Yulang.GeneralNominalReobservationExamples

open GeneralNominalRefreshFork GeneralNominalRefreshDivergence
open GeneralNominalReobservationSteps GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)

noncomputable def revision : Revision (after true) where
  entries := (state (some false)).nominals
  catalogue := (state (some false)).catalogue
  opaqueHeads := (state (some false)).bodies_opaque
  domain := by
    change ∀ slot : Fin 5, (state (some false)).nominals slot = none ↔ (state (some true)).nominals slot = none
    intro slot
    by_cases zero : slot = (0 : Fin 5)
    · subst slot; simp [state]
    · simp [state,zero]

theorem revision_result : revision.result = after false := rfl

theorem revision_certified : Certified revision where
  raw := by
    intro model valid
    have point : Models (after false) model :=
      (GeneralNominalSaturationState.initial_models (context (some false)) root model).mpr valid
    exact ((same_models true model).mpr ((same_models false model).mp point)).1
  exact := fun model => (same_models false model).trans (same_models true model).symm

theorem point_closed : PointClosed (state (some false)) := by
  intro slot d recorded parameter member
  by_cases zero : slot = (0 : Fin 5)
  · subst slot
    have same := Option.some.inj recorded
    subst d
    have same := List.mem_singleton.mp member
    subst parameter; rfl
  · by_cases one : slot = 1
    · subst slot
      have same := Option.some.inj recorded
      subst d
      have same := List.mem_singleton.mp member
      subst parameter; rfl
    · by_cases two : slot = 2
      · subst slot
        have same := Option.some.inj recorded
        subst d
        have same := List.mem_singleton.mp member
        subst parameter; rfl
      · simp [state,zero,one,two] at recorded

theorem revision_improves : Improves revision := by
  constructor
  · rintro slot ⟨prior,recorded,_⟩
    have present : ∃ d, revision.snapshot.nominals slot = some d := by
      cases found : revision.entries slot with
      | none =>
        have missing := (revision.domain slot).mp found
        rw [missing] at recorded
        cases recorded
      | some d => exact ⟨d,found⟩
    obtain ⟨d,found⟩ := present
    exact ⟨d,found,point_closed slot d found⟩
  · refine ⟨(0 : Fin 5),?_,descriptor (2,2),rfl,point_closed 0 _ rfl⟩
    rintro ⟨d,recorded,point⟩
    have same := Option.some.inj recorded
    subst d
    change PointDescriptor (descriptor (2,4)) at point
    have impossible := point (.type (2,4)) (List.mem_singleton_self _)
    exact (by decide +kernel : (2 : Fin 5) ≠ 4) impossible

theorem repair_step : Step registry root (after true) (after false) :=
  ⟨root,.root,.reobserve root revision revision_certified revision_improves⟩

theorem point_stable : Stable registry (after false) root :=
  stable_of_pointClosed (stable false) point_closed

theorem point_halted : ∀ next, ¬ Step registry root (after false) next :=
  stable_halted point_stable

theorem wide_not_stable : ¬ Stable registry (after true) root := by
  intro stopped
  exact stable_halted stopped _ repair_step

theorem fork_extension (wide : Bool) :
    B4Target.Steps (Step registry root) (after wide) (after false) := by
  cases wide with
  | false => exact .refl
  | true => exact .tail .refl repair_step

theorem fork_join (wide : Bool) :
    B4Target.Steps (Step registry root) before (after false) ∧
    B4Target.Steps (Step registry root) (after wide) (after false) ∧
    Stable registry (after false) root ∧
    (∀ model, Models (after wide) model ↔ Models (after false) model) :=
  ⟨.tail .refl (old_step (refresh_step false)),fork_extension wide,point_stable,
    fun model => (same_models wide model).trans (same_models false model).symm⟩

theorem canonical_fork_equal : GeneralCanonicalObservations.canonical (after false) =
    GeneralCanonicalObservations.canonical (after true) := by
  exact GeneralCanonicalObservations.equal_of_same_information
    ⟨fun _ member => member,rfl⟩ ⟨fun _ member => member,rfl⟩
    (fun model => (same_models false model).trans (same_models true model).symm)

/-- The maximal semantic view was already identical at the old divergent
states. An inspection-consumer theorem is essential, not implied by that fact. -/
theorem canonical_equality_does_not_fix_old_local :
    GeneralCanonicalObservations.canonical (after false) = GeneralCanonicalObservations.canonical (after true) ∧
    ¬ (∀ d f,
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false) d f ↔
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after true) d f) :=
  ⟨canonical_fork_equal,different_local⟩

theorem point_observation_in_wide : GeneralCanonicalObservations.canonical (after true)
    (.nominal base 0 (descriptor (2,2))) := by
  rw [← canonical_fork_equal]
  exact GeneralCanonicalObservations.recorded_in_canonical (after false)
    (@GeneralCanonicalObservations.Recorded.nominal (state (some false)) 0 (descriptor (2,2)) rfl)

theorem wide_observation_in_wide : GeneralCanonicalObservations.canonical (after true)
    (.nominal base 0 (descriptor (2,4))) :=
  GeneralCanonicalObservations.recorded_in_canonical (after true)
    (@GeneralCanonicalObservations.Recorded.nominal (state (some true)) 0 (descriptor (2,4)) rfl)

/-- Literal containment of all certified descriptors requires more than one
optional descriptor per slot. This does not exclude a normalized representative
with a separate proof of observational completeness. -/
theorem no_single_descriptor_contains_all : ¬ ∃ entries : Fin 5 → Option (GeneralNominalState.Descriptor 5),
    ∀ descriptor, GeneralCanonicalObservations.canonical (after true) (.nominal base 0 descriptor) →
      entries 0 = some descriptor := by
  rintro ⟨entries,all⟩
  have point := all _ point_observation_in_wide
  have wide := all _ wide_observation_in_wide
  have impossible := congrArg GeneralNominalState.Descriptor.arguments (Option.some.inj (point.symm.trans wide))
  exact (by decide +kernel : (descriptor (2,2)).arguments ≠ (descriptor (2,4)).arguments) impossible

/-- Both repaired traces end at precisely the same source state; this proves
actual Local and diagnostic agreement rather than only model equivalence. -/
theorem repaired_diagnostic :
    (∀ wide, B4Target.Steps (Step registry root) (after wide) (after false)) ∧
    (∀ next, ¬ Step registry root (after false) next) ∧
    B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false) root (.selected 90 []) ∧
    CommonRoleOutermostResolver.Resolves
      (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false)) root (.selected 90 []) ∧
    B4TargetV3.SameDiagnostic (GeneralDictionaryFeedbackEvidence.boundary roles) (.selected 90 []) (.selected 90 []) := by
  refine ⟨fork_extension,point_halted,point_local,point_tree,?_⟩
  exact B4TargetV3.same_diagnostic_refl _ (GeneralNominalFeedbackBoundary.dictionaryRefl roles
    (GeneralDictionaryFeedbackEvidence.evidence roles)) _

end Yulang.GeneralNominalReobservationExamples
