import Yulang.GeneralDeferredLadderEarlyReplay303
import Yulang.GeneralDeferredLadderEarlyExact303
import Yulang.GeneralDeferredLadderReinstall304
import Yulang.GeneralDeferredLadderRawCase304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeferredLadderRelay304
open GeneralDeferredLadderAdvance302 (run phase_step)
open GeneralDeferredLadderExact302 (RawStep Promotion)
open GeneralDeferredLadderResnapshot304 (HeadView resnapshot)
open GeneralDeferredLadderOperationalView304 (choices frame_forward generated_iff committed_iff)
open GeneralDeferredLadderRawCase304 (AdministrativeClosed closed_forward only_installs)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRoute301 (focus site sites_exact)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)

abbrev ctx (s : State roles) := s.core.erased.current.context
abbrev refPhase (n k : Nat) (cap : k ≤ n+1) := run n k cap
abbrev refState (n k : Nat) (cap : k ≤ n+1) := (refPhase n k cap).state

/-- A raw state may carry different historical effects, but shares the head
view of a certified hypothetical refresh of the never-promoted ledger. -/
structure Relay (n k : Nat) (cap : k ≤ n+1) (s : State roles) where
  cert : Refresh (refState n k cap) (ctx s)
  known : GeneralNominalState.Known (ctx s).state (n+1)
  view : HeadView (refresh (refState n k cap) (ctx s)) s
  chosen : choices (refState n k cap) = choices s
  reached : B4TargetV8.Reachable (boundary roles) registry displayRoot s
  noLegacy : s.legacy.effects = []

def initial (n k : Nat) (cap : k ≤ n+1) (target : GeneralNominalRecursiveCandidates.Context)
    (cert : Refresh (refState n k cap) target)
    (known : GeneralNominalState.Known target.state (n+1)) :
    Relay n k cap (refresh (refState n k cap) target) :=
  ⟨cert,known,⟨⟨rfl,rfl,rfl,fun _ => Iff.rfl⟩,rfl,rfl⟩,rfl,
    GeneralDeferredLadderEarlyInstall303.promoted_reached (refPhase n k cap) target cert known,
    (refPhase n k cap).legacy_empty⟩

theorem synthetic_closed (n k : Nat) (cap : k ≤ n+1) {s : State roles}
    (rel : Relay n k cap s) :
    AdministrativeClosed (refresh (refState n k cap) (ctx s)) displayRoot := by
  let p := refPhase n k cap
  refine ⟨?_,GeneralDeferredLadderAfterPromotion302.headless p (ctx s) rel.cert rel.known,
    GeneralDeferredLadderAfterPromotion302.equality_closed p (ctx s) rel.cert,
    GeneralDeferredLadderAfterPromotion302.point_closed p (ctx s) rel.cert rel.known,?_⟩
  · intro o generated
    exact GeneralDeferredLadderOnlyInstall302.recorded p
      (GeneralDeferredLadderAfterPromotion302.reverse_generated p (ctx s) generated)
  · intro a first b last same
    change a ∈ p.state.core.sites at first
    change b ∈ p.state.core.sites at last
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (sites_exact ..).mp last
    have models : Models (refresh p.state (ctx s)) = Models p.state :=
      funext fun m => propext (refresh_models rel.cert)
    rw [models] at same
    have indexes := GeneralDeferredLadderNoAdmin302.separates p (by omega) (by omega) same
    cases indexes
    exact .refl _

abbrev syntheticEffect {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :=
  GeneralDeferredLadderEarlyInstall303.effect (refPhase n k cap) hi (ctx s) rel.cert

def realEffect {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :=
  resnapshot rel.view (syntheticEffect rel hi) rfl

abbrev advanceState {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :=
  install s (realEffect rel hi)

theorem enabled {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :
    Installable compiled s (realEffect rel hi) := by
  let p := refPhase n k cap
  have good := GeneralDeferredLadderEarlyInstall303.enabled p hi (ctx s) rel.cert rel.known
  exact GeneralDeferredLadderReinstall304.enabled rel.view rel.chosen (syntheticEffect rel hi) good
    (GeneralNominalVersionedMixedEmbedding234.source_cache rel.reached) rel.noLegacy
    (GeneralDeferredLadderEarlyInstall303.current_requests p (ctx s))
    (GeneralDeferredLadderEarlyInstall303.future_requests p hi (ctx s) rel.cert)
    (GeneralDeferredLadderRetargetFrames302.list_held p (ctx s) rel.cert k hi)

theorem step_exists {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :
    RawStep s (advanceState rel hi) := by
  let p := refPhase n k cap
  change GeneralNominalVersionedMixedKernel234.Step compiled displayRoot s _
  refine ⟨focus n k,?_,.install (realEffect rel hi) (enabled rel hi) ?_⟩
  · exact (generated_iff rel.view.raw).mp
      (GeneralDeferredLadderAfterVariants302.generated p (ctx s) p.focus_generated)
  · intro yes
    exact GeneralDeferredLadderEarlyInstall303.not_committed p hi (ctx s) rel.cert
      ((committed_iff rel.view.raw (syntheticEffect rel hi).plan).mpr yes)

theorem step_unique {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) (after : State roles) :
    RawStep s after ↔ after = advanceState rel hi := by
  constructor
  · intro step
    let p := refPhase n k cap
    have raw : GeneralNominalVersionedMixedKernel234.Step compiled displayRoot s after := step
    obtain ⟨e,valid,novel,generated,rfl⟩ :=
      only_installs (closed_forward rel.view (synthetic_closed n k cap rel)) raw
    obtain ⟨i,low,location⟩ := GeneralDeferredLadderOnlyInstall302.generated p
      (GeneralDeferredLadderAfterPromotion302.reverse_generated p (ctx s)
        ((generated_iff rel.view.raw).mpr generated))
    have f := e.frame
    rw [valid.registry_eq,valid.snapshot_eq,location] at f
    have refFrame := frame_forward rel.view.raw.symm rel.view.context.symm rel.view.centers.symm f
    by_cases earlier : i < k
    · exact False.elim (novel ((committed_iff rel.view.raw e.plan).mp
        (GeneralDeferredLadderEarlyExact303.prior_committed p i (by omega) earlier (ctx s) rel.cert refFrame)))
    have same : i = k := by omega
    subst i
    have plans := GeneralDeferredLadderEarlyExact303.any_list_frame_eq p k hi (Nat.le_refl _)
      (ctx s) rel.cert refFrame
    have effects : e = realEffect rel hi := GeneralDeferredLadderOnlyInstall302.same_effect e _
      valid.registry_eq valid.snapshot_eq plans
    rw [effects]
  · rintro rfl
    exact step_exists rel hi

end Yulang.GeneralDeferredLadderRelay304
