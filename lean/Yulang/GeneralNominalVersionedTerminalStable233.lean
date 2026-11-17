import Yulang.GeneralNominalVersionedKernel232
import Yulang.GeneralNominalCenteredHeadAllocMergeStable
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
/-! Explicit sufficient obligations for full stability of a terminal singleton
state. These are decomposition lemmas, not a completed solver termination law. -/
namespace Yulang.GeneralNominalVersionedTerminalStable233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem generated_only
    (sites : state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (edges : state.core.erased.current.edges = [])
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => rw [edges] at member; cases member
  | alias _ _ member _ _ => rw [sites] at member; cases List.mem_singleton.mp member; rfl

def HeadlessUnknown (state : State roles) : Prop :=
  ∃ model, Models state model ∧ ∀ identity,
    identity ∈ GeneralNominalState.sources state.core.erased.current.context.state →
    ¬ GeneralNominalState.Known state.core.erased.current.context.state identity →
    ∀ test : GeneralNominalRecursiveInspection.Test, ¬ test.Holds (model identity).1

theorem no_refresh (headless : HeadlessUnknown state)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state.legacy context)
    (member : identity ∈ GeneralNominalState.sources state.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.core.erased.current.context.state identity) :
    ¬ GeneralNominalState.Known context.state identity := by
  intro known
  obtain ⟨model,valid,headless⟩ := headless
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have next := GeneralNominalCenteredHeadMatStepRefresh.refresh_exact_transport certificate model valid.1
  exact headless identity member unknown test
    (GeneralNominalCenteredHeadAllocMergeStable.head_holds head
      (GeneralCanonicalObservations.recorded_sound context.state model next
        (GeneralNominalSupport.head_recorded head)))

def EqualityClosed (state : State roles) : Prop := ∀ first last,
  first ∈ GeneralNominalState.sources state.core.erased.current.context.state →
  last ∈ GeneralNominalState.sources state.core.erased.current.context.state →
  Equal state first last → GeneralNominalFeedbackSteps.RawEqual state.core.erased.current first last

theorem stable
    (sites : state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (centers : state.core.sites = [site])
    (edges : state.core.erased.current.edges = [])
    (point : GeneralNominalReobservationSteps.PointClosed state.core.erased.current.context.state)
    (headless : HeadlessUnknown state) (equalities : EqualityClosed state)
    (committed : ∀ effect : Effect roles, Installable registry state effect →
      effect.plan.packet.site.occurrence = root → Committed state effect.plan) : Stable registry state root := by
  intro focus generated next action
  have same := generated_only sites edges generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      exact absent _ (sites ▸ List.mem_singleton_self _) same.symm
    | refresh context certificate identity member unknown known =>
      exact no_refresh headless certificate member unknown known
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point revision improved
    | equate first last one two equal novel => exact novel (equalities first last one two equal)
  | refresh focus context certificate identity member unknown known =>
    exact no_refresh headless certificate member unknown known
  | install effect enabled novel => exact novel (committed effect enabled same)
  | merge first last one two same novel =>
    rw [centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact novel (.refl _)

end Yulang.GeneralNominalVersionedTerminalStable233
