import Yulang.GeneralMixedReindexOutputFixture305
import Yulang.GeneralMixedIndexedCommit305
import Yulang.GeneralRebaseDepthHalt285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedReindexOutputHalt305
open GeneralDictionaryOutputDepth252 (registry root roles initial)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseDepthScalar285 (target refreshed new_zero new_one fixed_models actual_followup)
open GeneralMixedReindexOutputFixture305 (wide widened coordinates other_followup different_successors requests_both)
open GeneralRebaseDepthCommit285 (raw_sites center_sites no_edges exact_plan committed)
open GeneralRebaseDepthTerminalFrame285 (known_two equality_closed point_closed high_model putTop)
open GeneralNominalVersionedMixedObservations233 (Refresh cache_sound)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralMixedIndexedFrame305 (IndexedView relocated_same relocated_frame relocate reverse)
open GeneralMixedIndexedCommit305 (committed_forward symm_same)
open GeneralNominalReportContext305 (EquivalentContexts model_iff)

variable (tag : Nat)

noncomputable def view : IndexedView refreshed (widened tag) :=
  GeneralMixedReindexObserver305.indexed (s := refreshed) (coordinates tag)

theorem support_eq : GeneralNominalState.sources (wide tag).state = GeneralNominalState.sources target.state := rfl

theorem raw_close : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed (widened tag) := by
  intro a b am bm semantic
  have old := equality_closed a b ((support_eq tag) ▸ am) ((support_eq tag) ▸ bm)
    (fun m held => semantic m (((view tag).raw.models m).mp held))
  intro m raw
  exact old m ((model_iff (coordinates tag) m).mpr raw)

theorem point_close : GeneralNominalReobservationSteps.PointClosed (wide tag).state :=
  point_closed

theorem no_refresh (ctx : GeneralNominalRecursiveCandidates.Context) (supplied : Refresh (widened tag) ctx)
    (n : Nat) (unknown : ¬ GeneralNominalState.Known (wide tag).state n) :
    ¬ GeneralNominalState.Known ctx.state n := by
  by_cases high : 3 < n
  · intro known
    obtain ⟨test,observation,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
    have fact := cache_sound supplied.cache (GeneralNominalSupport.head_recorded headed)
      (((view tag).raw.models _).mp (high_model n high))
    have shape := GeneralDictionaryGroundCopy218Refresh.head_holds headed fact
    simp only [putTop,ite_true] at shape
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test shape
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases possibilities with rfl|rfl|rfl|rfl
  · exact (unknown ((coordinates tag).forward.known 0 new_zero)).elim
  · exact (unknown ((coordinates tag).forward.known 1 new_one)).elim
  · exact (unknown ((coordinates tag).forward.known 2 known_two)).elim
  · exact GeneralRebaseDepthRefresh285.no_certified_deep_head_of_model (widened tag)
      (((view tag).raw.models _).mp ((fixed_models _).mpr installed_model)) ctx.state supplied.cache rfl

theorem no_install (e : Effect roles) (enabled : Installable registry (widened tag) e)
    (atRoot : e.plan.packet.site.occurrence = root) : Committed (widened tag) e.plan := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at frame
  let back := reverse (view tag)
  have checked := exact_plan (relocated_frame back frame)
  have old : Committed refreshed (relocate back frame) := checked.symm ▸ committed
  exact committed_forward (view tag).raw (symm_same (relocated_same back frame))
    (GeneralNominalInverseCoordinates305.reverse (GeneralMixedIndexedFrame305.coordinates back frame)) old

theorem widened_halted (next : State roles) : ¬ Step registry root (widened tag) next := by
  rintro ⟨focus,generated,operation⟩
  have sites := (view tag).raw.sites ▸ raw_sites
  have same := GeneralNominalVersionedMixedTerminalStable234.generated_only sites ((view tag).raw.edges ▸ no_edges) generated
  cases operation with
  | administrative action =>
    cases action with
    | enqueue _ absent => exact absent _ (sites ▸ List.mem_singleton_self _) same.symm
    | refresh ctx cert identity _ unknown known => exact (no_refresh tag) ctx cert identity unknown known
    | equate first last a b equal novel => exact novel ((raw_close tag) first last a b equal)
    | reobserve revision _ improves =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision (state := (widened tag).core.erased.current)
        (point_close tag) revision improves
  | refresh _ ctx cert identity _ unknown known => exact (no_refresh tag) ctx cert identity unknown known
  | install effect enabled novel => exact novel ((no_install tag) effect enabled same)
  | merge first last a b _ novel =>
    have centers := (view tag).centers ▸ center_sites
    rw [centers] at a b
    cases List.mem_singleton.mp a
    cases List.mem_singleton.mp b
    exact novel (.refl _)

theorem two_distinct_halts :
    refreshed ≠ (widened tag) ∧
    B4Target.Steps (Step registry root) initial refreshed ∧
    B4Target.Steps (Step registry root) initial (widened tag) ∧
    (∀ next, ¬ Step registry root refreshed next) ∧
    (∀ next, ¬ Step registry root (widened tag) next) :=
  ⟨(different_successors tag),actual_followup,(other_followup tag),GeneralRebaseDepthHalt285.halted,(widened_halted tag)⟩

/-- The same request-bearing installed state has countably many distinct
one-step raw halts, all preserving its exact selected payload. -/
theorem many_actual_halts :
    Function.Injective widened ∧
      ∀ n, Step registry root installed (widened n) ∧
        (∀ next, ¬ Step registry root (widened n) next) :=
  ⟨GeneralMixedReindexOutputFixture305.widened_injective,fun n =>
    ⟨GeneralMixedReindexOutputFixture305.other_refresh n,widened_halted n⟩⟩

end Yulang.GeneralMixedReindexOutputHalt305
