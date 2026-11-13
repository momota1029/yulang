import Yulang.GeneralNominalDownstreamExamples
import Yulang.GeneralNominalDownstreamDepth

/-! Actual guarded updates invalidate proposed monotonicity laws for support
certificates. These are obstructions to the proposed measure, not infinite
executions. In particular the R installation deliberately closes its output
cycle, and its producer ceases to have a grounded explanation. -/
namespace Yulang.GeneralNominalBudgetDepthObstruction
open GeneralNominalSupport GeneralNominalSupportChoices GeneralNominalSaturationState
open GeneralNominalDownstreamSupport GeneralNominalDownstreamDepth
open GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralNominalOutputGrowth GeneralNominalOutputGrowthModels GeneralNominalOutputGrowthPackets
open GeneralNominalOutputGrowthRefresh GeneralNominalSupportGrowth
local instance : NeZero observed.current.context.state.base.slots := ⟨by change 3 ≠ 0; omega⟩

private theorem pool : dependencyPool observed = [root 0] := by
  change (installedFacts start (packet 0) ++ []).flatMap Fact.dependencies = _
  rw [empty_alternatives start (packet 0) rfl root_guard]
  rfl

/-- Every explanation of the newly known tail head must use the producing
root, even when arbitrary unused obligations are allowed in the support list. -/
theorem root_necessary (support : List (Occurrence roles))
    (head : HeadSupported added support 1 (.nominal 0 1)) : root 0 ∈ support := by
  classical
  by_cases member : root 0 ∈ support
  · exact member
  have restricted : restrict observed support = [] := by
    simp [restrict,pool,member]
  obtain ⟨snapshot,observation,recorded,entailed⟩ := head
  have empty : HeadSupported observed [] 1 (.nominal 0 1) := by
    rw [← restricted]
    exact ⟨snapshot,observation,recorded,fun model valid =>
      entailed model ((slice_restrict observed support model).mp valid)⟩
  exact False.elim (child_head_unsupported [] (by intro _ impossible; cases impossible) empty)

theorem added_open (producer : Occurrence roles) : ¬ Discharged added.current producer := by
  apply no_leaves_no_discharge
  intro candidate member
  have same : candidate = packet 0 := List.mem_singleton.mp member
  subst candidate
  rw [children_exact]
  simp

theorem tail_available : Available added 1 (.nominal 0 1) := by
  have recorded : Head observed.current.context.state 1 (.nominal 0 1)
      (.nominal refreshedBase 1 lastDescriptor) :=
    Head.nominal (snapshot := observed.current.context.state) 1 lastDescriptor rfl
  exact GeneralNominalDownstreamSteps.available_recorded observed
    (GeneralNominalSupportSteps.formed_exact GeneralNominalSupportGrowth.formed) recorded

theorem root_after_not_grounded : ¬ Grounded registry added (root 0) := by
  intro grounded
  apply trap_excluded registry added (fun producer => producer = root 0) ?_ ?_ (root 0) grounded rfl
  · intro producer same
    subst producer
    exact added_open _
  · intro producer same
    subst producer
    refine ⟨child 0,?_,added_open _,1,.nominal 0 1,?_,?_⟩
    · apply Waiting.child (Waiting.root (added_open _)) _ (added_open _)
      change (root 0,child 0) ∈ [] ++ (packet 0).children.map _
      rw [children_exact]
      simp [GeneralNominalDemandMerging.pointSite]
    · exact Need.input ⟨0,by decide +kernel⟩ _ tail_available
    · intro support known
      exact ⟨root 0,root_necessary support known,rfl⟩

theorem root_before_depth_one : AtDepth registry start 1 (root 0) := by
  refine Or.inr ?_
  intro child _ _ identity test needed
  have known := need_available needed
  have empty : dependencyPool start = [] := rfl
  exact ⟨[],by simpa only [Available,empty] using known,by intro _ impossible; cases impossible⟩

theorem root_after_no_depth (depth : Nat) : ¬ AtDepth registry added depth (root 0) :=
  fun known => root_after_not_grounded (depth_grounded known)

/-- Checked source formation and a real installation are included. The
producer certificate is destroyed before the observation refresh is taken. -/
theorem actual_grounding_loss :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalDownstreamSteps.SourceFormed registry (root 0) start ∧
    GeneralNominalDownstreamSteps.Step registry (root 0) start added ∧
    AtDepth registry start 1 (root 0) ∧
    ¬ Grounded registry added (root 0) ∧
    Models added.current (finiteModel 1) :=
  ⟨checked,.initial _ (initial_source 0),GeneralNominalDownstreamExamples.r_first_step,
    root_before_depth_one,root_after_not_grounded,installed_models 0⟩

theorem not_grounded_step_monotone :
    ¬ (∀ (reg : GeneralDeclarations.Registry) (d : Occurrence roles) (before after : Tracked roles),
      GeneralDeclarations.Checked reg → GeneralNominalDownstreamSteps.SourceFormed reg d before →
      GeneralNominalDownstreamSteps.Step reg d before after → ∀ producer,
      Grounded reg before producer → Grounded reg after producer) := by
  intro preserved
  exact root_after_not_grounded (preserved registry (root 0) start added checked
    (.initial _ (initial_source 0)) GeneralNominalDownstreamExamples.r_first_step (root 0)
    (depth_grounded root_before_depth_one))

/-- This is the precise snapshot-bound predicate from Item 4i. It counts
recorded grounded producers, not the minimal support of each individual head. -/
def PoolBound (reg : GeneralDeclarations.Registry) (state : Tracked roles) (depth : Nat) : Prop :=
  ∀ producer ∈ dependencyPool state, Grounded reg state producer → AtDepth reg state depth producer

theorem p_initial_zero : PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.start 0 := by
  intro _ impossible
  cases impossible

theorem p_after_not_zero : ¬ PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 0 := by
  intro bound
  have recorded : GeneralNominalSupportSiblings.root ∈ dependencyPool GeneralNominalSupportSiblings.afterP := by
    change _ ∈ (installedFacts GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.pk ++ []).flatMap Fact.dependencies
    rw [empty_alternatives GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.pk rfl GeneralNominalSupportSiblings.p_guard]
    simp [Fact.dependencies,GeneralNominalSupportSiblings.pk,GeneralNominalDemandMerging.pointSite]
  have grounded := source_conservative_grounded GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP
    GeneralNominalDownstreamExamples.sibling_source_conservative GeneralNominalSupportSiblings.root
  exact GeneralNominalSupportRankObstruction.siblings_unresolved _ (bound _ recorded grounded)

theorem p_after_one : PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 1 := by
  intro producer _ _
  refine Or.inr ?_
  intro child _ _ identity test needed
  obtain ⟨snapshot,observation,head,entailed⟩ := need_available needed
  refine ⟨[],⟨snapshot,observation,head,?_⟩,by intro _ impossible; cases impossible⟩
  intro model valid
  exact entailed model (all_models_slice _ _ model
    (GeneralNominalDownstreamExamples.sibling_source_conservative model valid.1))

theorem actual_pool_bound_increases :
    GeneralDeclarations.Checked GeneralNominalSupportSiblings.reg ∧
    GeneralNominalDownstreamSteps.SourceFormed GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.start ∧
    GeneralNominalDownstreamSteps.Step GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.afterP ∧
    PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.start 0 ∧
    ¬ PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 0 ∧
    PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 1 :=
  ⟨GeneralNominalSupportSiblings.checked,.initial _ GeneralNominalSupportSiblings.initial_source,
    GeneralNominalDownstreamExamples.p_first_step,p_initial_zero,p_after_not_zero,p_after_one⟩

/-- The one fixed initial snapshot has only two source slots, but its
unconstrained tail permits finite models of arbitrarily large nominal depth. -/
theorem source_arbitrarily_tall (bound : Nat) :
    ∃ model : GeneralNominalCommonBridge.Assignment, Models start.current model ∧
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower (bound+2)) := by
  refine ⟨finiteModel (bound+1),?_,?_⟩
  · apply (snapshot_models 0 _).mpr
    intro index small
    exact finite_prefix_models (bound+1) index (by omega)
  · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

/-- A maximum denotation size over all initial models cannot be a finite
source budget. This leaves symbolic sizes with opaque source leaves open. -/
theorem no_uniform_model_height :
    ¬ ∃ bound : Nat, ∀ model : GeneralNominalCommonBridge.Assignment,
      Models start.current model → ∀ height : Nat,
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower height) → height ≤ bound := by
  rintro ⟨bound,limited⟩
  obtain ⟨model,valid,height⟩ := source_arbitrarily_tall bound
  have impossible := limited model valid (bound+2) height
  omega

theorem checked_off_cycle_unbounded_models :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalDownstreamSteps.SourceFormed registry (root 0) start ∧
    start.current.context.state.base.slots = 2 ∧
    ¬ GeneralNominalFeedbackK2.RootK2 start.current (root 0) ∧
    ¬ ∃ bound : Nat, ∀ model : GeneralNominalCommonBridge.Assignment,
      Models start.current model → ∀ height : Nat,
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower height) → height ≤ bound :=
  ⟨checked,.initial _ (initial_source 0),rfl,not_rootK2 0,no_uniform_model_height⟩

end Yulang.GeneralNominalBudgetDepthObstruction
