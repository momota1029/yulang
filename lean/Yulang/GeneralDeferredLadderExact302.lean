import Yulang.GeneralDeferredLadderOnlyInstall302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralDeferredLadderExact302
open GeneralDeferredLadderLedger302
open GeneralDeferredLadderAdvance302 (run phase_step)
open GeneralDeferredLadderOnlyInstall302 (recorded candidate_exact)
open GeneralDeferredLadderNoAdmin302 (strict_target equality_closed point_closed separates)
open GeneralObservedLadderRoute301 (site sites_exact edges focus)
open GeneralDeferredLadderPlan302 (compiled)
open GeneralDeferredLadderRefresh302 (actual promoted promotedContext unknown tracked_terminal certificate strict)
open GeneralObservedLadderRefresh301 (before)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open B4Target (Steps)

abbrev RawStep := (boundary roles).Step registry displayRoot

/-- A raw scalar observation outcome may fix both contexts' model sets
without fixing the precise stored target context. -/
def Promotion (n : Nat) (old new : State roles) : Prop :=
  ∃ ctx, ∃ _cert : Refresh old ctx, GeneralNominalState.Known ctx.state (n+1) ∧ new = refresh old ctx

theorem only_step (n k : Nat) (cap : k ≤ n+1) (s : State roles)
    (raw : RawStep (run n k cap).state s) :
    (∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state) ∨ Promotion n (run n k cap).state s := by
  let p := run n k cap
  change Step compiled displayRoot p.state s at raw
  obtain ⟨focusHere,generated,action⟩ := raw
  cases action with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨row,seen,loc⟩ := recorded p generated
      exact False.elim (absent row seen loc)
    | refresh ctx cert id tracked beforeSeen afterSeen =>
      have equal := strict_target p ctx cert id tracked beforeSeen afterSeen
      subst id
      exact .inr ⟨ctx,cert,afterSeen,rfl⟩
    | equate a b first last same novel =>
      exact False.elim (novel (equality_closed p a b first last same))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed p) rev improves)
  | refresh _ ctx cert id tracked beforeSeen afterSeen =>
    have equal := strict_target p ctx cert id tracked beforeSeen afterSeen
    subst id
    exact .inr ⟨ctx,cert,afterSeen,rfl⟩
  | install e enabled novel =>
    obtain ⟨hi,equal⟩ := candidate_exact n k cap e enabled generated novel
    cases equal
    exact .inl ⟨hi,rfl⟩
  | merge a b first last same novel =>
    rw [p.centers_eq] at first last
    obtain ⟨i,ai,rfl⟩ := (sites_exact ..).mp first
    obtain ⟨j,bj,rfl⟩ := (sites_exact ..).mp last
    have eq : i = j := separates p (by omega) (by omega) same
    cases eq
    exact False.elim (novel (.refl _))

theorem promotion_legal (p : Phase n k) (s : State roles) (change : Promotion n p.state s) :
    RawStep p.state s := by
  obtain ⟨ctx,cert,found,rfl⟩ := change
  exact ⟨displayRoot,.root,.refresh displayRoot ctx cert (n+1) (tracked_terminal p) (unknown p) found⟩

theorem exact_step (n k : Nat) (cap : k ≤ n+1) (s : State roles) :
    RawStep (run n k cap).state s ↔
      (∃ hi : k ≤ n, s = (run n (k+1) (by omega)).state) ∨ Promotion n (run n k cap).state s := by
  refine ⟨only_step n k cap s,?_⟩
  rintro (⟨hi,rfl⟩|prom)
  · exact phase_step n k hi
  · exact promotion_legal (run n k cap) s prom

theorem promotion_edges (n : Nat) {s t : State roles} (change : Promotion n s t) :
    t.core.erased.current.edges = s.core.erased.current.edges := by
  obtain ⟨_,_,_,rfl⟩ := change
  rfl

theorem edge_count (n k : Nat) : (edges n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [edges,ih]

theorem install_not_promotion (n k : Nat) (hi : k ≤ n) :
    ¬ Promotion n (run n k (by omega)).state (run n (k+1) (by omega)).state := by
  intro prom
  have same := congrArg List.length (promotion_edges n prom)
  change (run n (k+1) (by omega)).state.core.erased.current.edges.length =
    (run n k (by omega)).state.core.erased.current.edges.length at same
  rw [(run n (k+1) (by omega)).edges_eq,(run n k (by omega)).edges_eq,edge_count,edge_count] at same
  omega

theorem leaf_must_promote (n : Nat) (s : State roles) :
    RawStep (run n (n+1) (Nat.le_refl _)).state s ↔
      Promotion n (run n (n+1) (Nat.le_refl _)).state s := by
  rw [exact_step]
  exact ⟨fun h => h.elim (fun ⟨impossible,_⟩ => False.elim (by omega)) id,Or.inr⟩

theorem not_stable (p : Phase n k) (o : GeneralSourceDictionaries.Occurrence roles) :
    ¬ (boundary roles).Stable registry p.state o := by
  intro stable
  exact stable o .root _
    (.refresh o (promotedContext p) (certificate p) (n+1) (tracked_terminal p) (unknown p) (strict p))

end Yulang.GeneralDeferredLadderExact302
