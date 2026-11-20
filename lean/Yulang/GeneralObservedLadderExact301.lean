import Yulang.GeneralObservedLadderOnlyInstall301

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralObservedLadderExact301
open GeneralObservedLadderInitial301 (initial)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderAdvance301 (run advance phase_step)
open GeneralObservedLadderOnlyInstall301 (recorded candidate_exact)
open GeneralObservedLadderNoAdmin301 (headless equality_closed point_closed)
open GeneralObservedLadderEnabled301 (separates)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedTerminalStable234 (no_refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open B4Target (Steps)

theorem only_step (n k : Nat) (cap : k ≤ n+1) (s : State roles)
    (raw : (boundary roles).Step registry displayRoot (run n k cap).state s) :
    ∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state := by
  let p := run n k cap
  change Step compiled displayRoot p.state s at raw
  obtain ⟨focus,generated,action⟩ := raw
  cases action with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨row,seen,loc⟩ := recorded p generated
      exact False.elim (absent row seen loc)
    | refresh ctx certificate id tracked unknown known =>
      exact False.elim (no_refresh (headless p) certificate tracked unknown known)
    | equate a b first last same novel =>
      exact False.elim (novel (equality_closed p a b first last same))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed p) rev improves)
  | refresh _ ctx certificate id tracked unknown known =>
    exact False.elim (no_refresh (headless p) certificate tracked unknown known)
  | install e enabled novel =>
    obtain ⟨hi,equal⟩ := candidate_exact n k cap e enabled generated novel
    cases equal
    exact ⟨hi,rfl⟩
  | merge a b first last same novel =>
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (sites_exact ..).mp last
    have eq : i = j := separates p (by omega) (by omega) same
    cases eq
    exact False.elim (novel (.refl _))

theorem exact_step (n k : Nat) (cap : k ≤ n+1) (s : State roles) :
    (boundary roles).Step registry displayRoot (run n k cap).state s ↔
      ∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state :=
  ⟨only_step n k cap s,by rintro ⟨hi,rfl⟩; exact phase_step n k hi⟩

theorem halted (n : Nat) (s : State roles) :
    ¬ (boundary roles).Step registry displayRoot (run n (n+1) (Nat.le_refl _)).state s := by
  intro raw
  obtain ⟨hi,_⟩ := only_step n (n+1) _ s raw
  omega

theorem reachable_phases (n : Nat) (s : State roles)
    (path : Steps ((boundary roles).Step registry displayRoot) (initial n) s) :
    ∃ k, ∃ cap : k ≤ n+1, s = (run n k cap).state := by
  induction path with
  | refl => exact ⟨0,by omega,rfl⟩
  | tail _ step ih =>
    obtain ⟨k,cap,atPhase⟩ := ih
    cases atPhase
    obtain ⟨hi,exactNext⟩ := only_step n k cap _ step
    exact ⟨k+1,by omega,exactNext⟩

theorem phases_distinct (n a b : Nat) (ha : a ≤ n+1) (hb : b ≤ n+1)
    (same : (run n a ha).state = (run n b hb).state) : a = b := by
  have count (k : Nat) : (edges n k).length = k := by
    induction k with
    | zero => rfl
    | succ k ih => simp [edges,ih]
  have equalLength := congrArg (fun s : State roles => s.core.erased.current.edges.length) same
  change (run n a ha).state.core.erased.current.edges.length =
    (run n b hb).state.core.erased.current.edges.length at equalLength
  rw [(run n a ha).edges_eq,(run n b hb).edges_eq,count,count] at equalLength
  exact equalLength

theorem rank_decreases (n a b : Nat) (ha : a ≤ n+1) (hb : b ≤ n+1)
    (step : (boundary roles).Step registry displayRoot (run n a ha).state (run n b hb).state) :
    n+1-b < n+1-a := by
  obtain ⟨hi,eq⟩ := only_step n a ha _ step
  have next : b = a+1 := phases_distinct n b (a+1) hb (by omega) eq
  omega

theorem accessible_phase (n k : Nat) (cap : k ≤ n+1) :
    Acc (fun last first => (boundary roles).Step registry displayRoot first last) (run n k cap).state := by
  have bounded (fuel : Nat) : ∀ (i : Nat) (hi : i ≤ n+1), n+1-i ≤ fuel →
      Acc (fun last first => (boundary roles).Step registry displayRoot first last) (run n i hi).state := by
    induction fuel with
    | zero =>
      intro i hi zero
      have eq : i = n+1 := by omega
      subst i
      exact Acc.intro _ (fun s no => False.elim (halted n s no))
    | succ fuel ih =>
      intro i hi fits
      constructor
      intro s step
      obtain ⟨below,rfl⟩ := only_step n i hi s step
      exact ih (i+1) (by omega) (by omega)
  exact bounded (n+1-k) k cap (Nat.le_refl _)

theorem accessible_initial (n : Nat) :
    Acc (fun last first => (boundary roles).Step registry displayRoot first last) (initial n) :=
  accessible_phase n 0 (by omega)

end Yulang.GeneralObservedLadderExact301
