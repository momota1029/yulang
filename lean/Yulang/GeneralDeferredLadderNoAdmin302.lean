import Yulang.GeneralDeferredLadderRefresh302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderNoAdmin302
open GeneralDeferredLadderReport302 (context snapshot)
open GeneralDeferredLadderLedger302
open GeneralDeferredLadderRefresh302 (promotedPhase retained_models)
open GeneralObservedLadderRoute301
open GeneralObservedLadderNoAdmin301 (padding free)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedMixedTerminalStable234 (EqualityClosed)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenters (SameInputs)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem same_observed_models (p : Phase n k) (m : Assignment) :
    Models p.state m ↔ Models (GeneralObservedLadderLedger301.start n).state m :=
  (p.models m).trans (GeneralObservedLadderRefreshChain301.before_models n m)

theorem padded (p : Phase n k) (other : Nat → Ty) : Models p.state (padding n other) :=
  (same_observed_models p _).mpr (GeneralObservedLadderNoAdmin301.padded (GeneralObservedLadderLedger301.start n) other)

theorem no_private_head (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (a : Nat) (high : n+1 < a) :
    ¬ GeneralNominalState.Known ctx.state a := by
  intro known
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have valid := padded p (fun _ => .top)
  have next := (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr valid
  have seen := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (GeneralCanonicalObservations.recorded_sound ctx.state _ next.1.1 (GeneralNominalSupport.head_recorded head))
  rw [free _ _ _ high] at seen
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test seen

theorem strict_target (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (a : Nat)
    (_seen : a ∈ GeneralNominalState.sources p.state.core.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known p.state.core.erased.current.context.state a)
    (known : GeneralNominalState.Known ctx.state a) : a = n+1 := by
  by_cases small : a ≤ n+1
  · by_cases inner : a ≤ n
    · have earlier := GeneralObservedLadderRefreshProgram301.earlier_known n a inner
      apply False.elim
      apply unknown
      rw [p.context_eq]
      exact earlier
    · omega
  · exact False.elim (no_private_head p ctx cert a (by omega) known)

theorem only_equal_names (p : Phase n k) (a b : Nat) (same : Equal p.state a b) : a = b :=
  GeneralObservedLadderNoAdmin301.only_equal_names (GeneralObservedLadderLedger301.start n) a b
    (fun m atObserved => same m ((same_observed_models p m).mpr atObserved))

theorem equality_closed (p : Phase n k) : EqualityClosed p.state := by
  intro a b _ _ same
  cases only_equal_names p a b same
  intro _ _
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem point_closed (p : Phase n k) :
    GeneralNominalReobservationSteps.PointClosed p.state.core.erased.current.context.state := by
  rw [p.context_eq]
  intro slot desc found
  change (if h : slot.val ≤ n then some (GeneralNominalOutputGrowthModels.descriptor n slot h) else none) =
    some desc at found
  split at found
  · cases Option.some.inj found
    intro param part
    cases List.mem_singleton.mp part
    rfl
  · cases found

theorem separates (p : Phase n k) {i j : Nat} (left : i ≤ n+1) (right : j ≤ n+1)
    (same : SameInputs (Models p.state) (site n i) (site n j)) : i = j := by
  apply GeneralObservedLadderEnabled301.separates (promotedPhase p) left right
  have eq : Models (promotedPhase p).state = Models p.state :=
    funext fun m => propext (retained_models p m)
  rw [eq]
  exact same

end Yulang.GeneralDeferredLadderNoAdmin302
