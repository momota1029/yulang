import Yulang.GeneralDeclarativeI65I74BoundedCandidateGeometry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open Producer479 (Site Trail)

-- This is a stricter evidence preflight, not source selection. The
-- first unchecked reachable geometry declines rather than being safe.
def paletteReadyWithinOriginalBudget486 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) :
    Nat → Site s pos → Bool
  | 0,here => (oldObservedSign486 s pos rel palette here.index).isSome
  | fuel+1,here =>
    match oldObservedSign486 s pos rel palette here.index with
    | none => false
    | some true => true
    | some false =>
      (finiteExistingHops486 here).all (fun candidate => paletteReadyWithinOriginalBudget486 rel palette fuel candidate.2)

theorem no_unavailable_guarded_route_is_lost_under_a_successful_original_palette_preflight486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} {first last : Site s pos} {moves points bit}
    (actual : Trail s pos rel first moves points last bit)
    (fuel : Nat) (enough : moves.length ≤ fuel)
    (complete : paletteReadyWithinOriginalBudget486 rel palette fuel first = true) :
    (⟨moves,points,last,bit⟩ : GeometricVisit486 s pos) ∈ enumerateGuardedGeometry486 rel palette fuel first := by
  induction actual generalizing fuel with
  | @stop here sign known correct =>
    have selected : ∃ b, oldObservedSign486 s pos rel palette here.index = some b := by
      cases ran : oldObservedSign486 s pos rel palette here.index with
      | none => cases fuel <;> simp [paletteReadyWithinOriginalBudget486,ran] at complete
      | some b => exact ⟨b,rfl⟩
    obtain ⟨signed,read⟩ := selected
    have actualSign := (old_palette_sign_is_about_its_own_existing_site486 read).2
    have same : signed = sign := by cases signed <;> cases sign <;> simp_all
    subst signed
    cases fuel <;> cases sign <;> simp [enumerateGuardedGeometry486,read]
  | @step here next final move moves indices sign hop root safe tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ k =>
      have signAtRoot : oldObservedSign486 s pos rel palette here.index = some false := by
        cases h : oldObservedSign486 s pos rel palette here.index with
        | none => simp [paletteReadyWithinOriginalBudget486,h] at complete
        | some sign =>
          cases sign with
          | false => rfl
          | true =>
            exact False.elim (safe ((old_palette_sign_is_about_its_own_existing_site486 h).2.mp rfl))
      have child : (move,next) ∈ finiteExistingHops486 here :=
        finite_hops_are_exact_existing_written_visits486.mpr ⟨hop⟩
      have data : (finiteExistingHops486 here).all
          (fun x => paletteReadyWithinOriginalBudget486 rel palette k x.2) = true := by
        simpa [paletteReadyWithinOriginalBudget486,signAtRoot] using complete
      have after := (List.all_eq_true.mp data) (move,next) child
      simp only [enumerateGuardedGeometry486,signAtRoot,List.mem_cons]
      right
      exact List.mem_flatMap.mpr ⟨(move,next),child,
        List.mem_map.mpr ⟨⟨moves,indices,final,sign⟩,ih k (Nat.le_of_succ_le_succ enough) after,rfl⟩⟩

theorem original_required_palette_preflight_gives_complete_exact_old_search486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} {first last : Site s pos} {moves points bit}
    (complete : paletteReadyWithinOriginalBudget486 rel palette (originalNodeBudget486 first.pattern) first = true) :
    (⟨moves,points,last,bit⟩ : GeometricVisit486 s pos) ∈
      enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first ↔
      Trail s pos rel first moves points last bit := by
  constructor
  · exact every_enumerated_geometry_is_the_original_independent_guarded_trail486 _ _ _
  · intro actual
    have small := every_existing_finite_visit_stops_within_the_original_written_budget486 actual
    exact no_unavailable_guarded_route_is_lost_under_a_successful_original_palette_preflight486 actual _
      (by omega) complete

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
