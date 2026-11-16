import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.GeneralDictionaryDefaultTrace208
import Yulang.GeneralDictionaryDefault214ActualJournal

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryAdministrativeSemanticSupport222
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultKernel208
variable {roles : Roles.RoleDecls} {before after : State roles} {model : Assignment}
variable {pool : List Nat}

/-- Equality feedback adds only a consequence of the full total journal. -/
theorem equate_models_iff (equal : Equal before first last) :
    Models (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)) model ↔
      Models before model := by
  constructor
  · intro valid
    refine ⟨((GeneralNominalState.extend_models ..).mp valid.1).1,
      valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    intro effect member
    have pair := valid.2.2.2.2.2 effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := before.core)
        (after := (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)).core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩
  · intro valid
    refine ⟨?_,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    · apply (GeneralNominalState.extend_models ..).mpr
      exact ⟨valid.1,(GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr
        (equal model valid)⟩
    · intro effect member
      have pair := valid.2.2.2.2.2 effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)).core)
          (after := before.core) (fun _ h => h) (fun _ h => h)) pair.2⟩

/-- Enqueue may expose additional named output requests to existing live effects.
The exact residual is retained; no arbitrary administrative model equivalence
is claimed. Linkedness or novelty are not needed for this semantic identity. -/
theorem enqueue_models_iff :
    Models (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)) model ↔
    Models before model ∧ ∀ effect ∈ before.effects,
      effect.Live (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)).core model := by
  constructor
  · intro valid
    refine ⟨⟨valid.1,valid.2.1,?_,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩,?_⟩
    · intro site member
      exact valid.2.2.1 site (List.mem_append_left _ member)
    · intro effect member
      have pair := valid.2.2.2.2.2 effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := before.core)
          (after := (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)).core)
          (fun _ h => List.mem_append_left _ h) (fun _ h => h)) pair.2⟩
    · intro effect member
      exact (valid.2.2.2.2.2 effect member).2
  · rintro ⟨valid,live⟩
    refine ⟨valid.1,valid.2.1,?_,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    · intro site member
      rcases List.mem_append.mp member with old | fresh
      · exact valid.2.2.1 site old
      · cases List.mem_singleton.mp fresh
        exact GeneralNominalSaturationState.point_holds _ _
    · intro effect member
      exact ⟨(valid.2.2.2.2.2 effect member).1,live effect member⟩

/-- Any independently proved semantic pool survives entailed equality feedback.
The pool need not contain the syntactically mentioned equality endpoints. -/
theorem equate_depends
    (equal : Equal before first last)
    (depends : ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) → (Models before a ↔ Models before b)) :
    ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) →
      (Models (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)) a ↔
       Models (change before (GeneralNominalFeedbackSteps.equate before.core.erased.current first last)) b) := by
  intro a b same
  exact (equate_models_iff equal).trans ((depends a b same).trans (equate_models_iff equal).symm)

/-- Enqueue needs only the added live-class dependency, rather than a fresh
whole syntactic journal pool. This does not prove absence of any aggregate. -/
noncomputable def enqueueDelta (before : State roles) (focus : Occurrence roles) : List Nat :=
  before.effects.flatMap fun effect =>
    GeneralDictionaryDefault214ActualBodyFrame.classSources
      (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)).core
      effect.plan.packet.site.occurrence effect.plan

theorem enqueue_depends
    (depends : ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) → (Models before a ↔ Models before b)) :
    ∀ a b : Assignment, (∀ n ∈ pool ++ enqueueDelta before focus, a n = b n) →
      (Models (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)) a ↔
       Models (change before (GeneralNominalSaturationState.enqueue before.core.erased.current focus)) b) := by
  intro a b same
  rw [enqueue_models_iff,enqueue_models_iff]
  apply and_congr (depends a b (fun n member => same n (List.mem_append_left _ member)))
  apply forall_congr'; intro effect
  apply forall_congr'; intro member
  apply GeneralDictionaryDefault214ActualBodyFrame.class_iff
  intro n present
  exact same n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨effect,member,present⟩))

/-- On the actual reachable, generated part of a run, enqueue is impossible:
all generated occurrences are already registered. Thus every administrative
step preserves Models exactly, including total live effects. -/
theorem reachable_administrative_models_iff
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (generated : GeneralNominalSaturationState.Generated before.core.erased.current root focus)
    (action : Administrative before focus after) :
    Models after model ↔ Models before model := by
  cases action with
  | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
        (GeneralDictionaryDefaultTrace208.registered_trace path) generated
      exact False.elim (absent site member same)
  | refresh context certificate source member unknown known =>
      exact GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate
  | reobserve revision certificate improved =>
      exact GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate
  | equate first last one two equal novel => exact equate_models_iff equal

/-- The existing reachable administrative relation cannot enlarge a semantic
pool; reservation lists and cached observations may still change syntactically.
Install and merge remain separate obligations. -/
theorem reachable_administrative_depends
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (generated : GeneralNominalSaturationState.Generated before.core.erased.current root focus)
    (action : Administrative before focus after)
    (depends : ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) → (Models before a ↔ Models before b)) :
    ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) → (Models after a ↔ Models after b) := by
  intro a b same
  exact (reachable_administrative_models_iff path generated action).trans
    ((depends a b same).trans (reachable_administrative_models_iff path generated action).symm)

end Yulang.GeneralDictionaryAdministrativeSemanticSupport222


