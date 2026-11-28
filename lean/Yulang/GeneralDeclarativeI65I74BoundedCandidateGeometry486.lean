import Yulang.GeneralDeclarativeI65I74ProducerTrail479
import Yulang.GeneralDeclarativeI65I74ExactSuccessorHop486
import Yulang.GeneralDeclarativeI65I74OriginalNodeBudget486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open LiteralVisits473 (Checkpoint GuardedObservationInput readCheck read_checkpoint_guards StepWire)
open QuotientObservation471 (ReturnsUpToEquality)
open ObservationAlternatives473 (Positions graphOf oldPosition)
open Producer479 (Site Trail)

abbrev SignedPalette486 (n : Nat) := Fin n → Option (Checkpoint n)

def oldObservedSign486 {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) (i : Fin n) : Option Bool := do
  let check ← palette i
  if check.which = i then readCheck s pos rel (oldPosition pos i) check else none

theorem old_palette_sign_is_about_its_own_existing_site486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} {i : Fin n} {bit : Bool}
    (h : oldObservedSign486 s pos rel palette i = some bit) :
    GuardedObservationInput s pos rel i ∧
    (bit = true ↔ ReturnsUpToEquality (graphOf s pos) i) := by
  unfold oldObservedSign486 at h
  cases atPoint : palette i with
  | none => simp [atPoint] at h
  | some check =>
    simp only [atPoint,bind,Option.bind] at h
    split at h
    · rename_i same
      have proof := read_checkpoint_guards h
      exact ⟨same ▸ proof.1,same ▸ proof.2.2⟩
    · cases h

def CompletePalette486 {n : Nat} (s : GeneralDeclarativeI65.State)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) : Prop :=
  ∀ i, GuardedObservationInput s pos rel i → ∃ bit, oldObservedSign486 s pos rel palette i = some bit

structure GeometricVisit486 {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n) where
  moves : List StepWire
  points : List (Fin n)
  last : Site s pos
  bit : Bool

/-- Enumerate only geometric visits of the old checked constructor
grammar starting at one given site. The old graph is never changed.
This routine does not authorize source-side use or decide matching. -/
def enumerateGuardedGeometry486 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) :
    Nat → Site s pos → List (GeometricVisit486 s pos)
  | 0,here =>
      match oldObservedSign486 s pos rel palette here.index with
      | none => []
      | some bit => [⟨[],[],here,bit⟩]
  | fuel+1,here =>
      match oldObservedSign486 s pos rel palette here.index with
      | none => []
      | some true => [⟨[],[],here,true⟩]
      | some false =>
          ⟨[],[],here,false⟩ :: (finiteExistingHops486 here).flatMap
            (fun pair => (enumerateGuardedGeometry486 rel palette fuel pair.2).map fun later =>
              ⟨pair.1::later.moves,pair.2.index::later.points,later.last,later.bit⟩)

theorem every_enumerated_geometry_is_the_original_independent_guarded_trail486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} (fuel : Nat) (here : Site s pos) (visit : GeometricVisit486 s pos)
    (found : visit ∈ enumerateGuardedGeometry486 rel palette fuel here) :
    Trail s pos rel here visit.moves visit.points visit.last visit.bit := by
  induction fuel generalizing here visit with
  | zero =>
    cases ran : oldObservedSign486 s pos rel palette here.index with
    | none => simp [enumerateGuardedGeometry486,ran] at found
    | some b =>
      have fixed : visit = ⟨[],[],here,b⟩ := by simpa [enumerateGuardedGeometry486,ran] using found
      subst visit
      have checker := old_palette_sign_is_about_its_own_existing_site486 ran
      exact .stop checker.1 checker.2
  | succ k ih =>
    cases ran : oldObservedSign486 s pos rel palette here.index with
    | none => simp [enumerateGuardedGeometry486,ran] at found
    | some b =>
      have checker := old_palette_sign_is_about_its_own_existing_site486 ran
      cases b with
      | true =>
        have fixed : visit = ⟨[],[],here,true⟩ := by simpa [enumerateGuardedGeometry486,ran] using found
        subst visit
        exact .stop checker.1 checker.2
      | false =>
        simp only [enumerateGuardedGeometry486,ran,List.mem_cons] at found
        rcases found with rfl|continues
        · exact .stop checker.1 checker.2
        · obtain ⟨⟨a,next⟩,member,entered⟩ := List.mem_flatMap.mp continues
          obtain ⟨later,inTail,exact⟩ := List.mem_map.mp entered
          cases exact
          obtain ⟨hop⟩ := (finite_hops_are_exact_existing_written_visits486).mp member
          exact .step hop checker.1 (fun k => Bool.false_ne_true (checker.2.mpr k)) (ih _ _ inTail)

theorem complete_palette_checks_the_exact_independent_sign
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} (complete : CompletePalette486 s pos rel palette)
    {here : Fin n} {bit : Bool} (guard : GuardedObservationInput s pos rel here)
    (sign : bit = true ↔ ReturnsUpToEquality (graphOf s pos) here) :
    oldObservedSign486 s pos rel palette here = some bit := by
  obtain ⟨other,run⟩ := complete here guard
  have meaning := (old_palette_sign_is_about_its_own_existing_site486 run).2
  have same : other = bit := by cases other <;> cases bit <;> simp_all
  exact same ▸ run

theorem every_bounded_independent_visit_occurs_in_the_geometry_enumerator486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} (complete : CompletePalette486 s pos rel palette)
    {first last : Site s pos} {moves points bit}
    (independent : Trail s pos rel first moves points last bit)
    (fuel : Nat) (budget : moves.length ≤ fuel) :
    (⟨moves,points,last,bit⟩ : GeometricVisit486 s pos) ∈
      enumerateGuardedGeometry486 rel palette fuel first := by
  induction independent generalizing fuel with
  | @stop here ownBit guard sign =>
    have ran := complete_palette_checks_the_exact_independent_sign complete guard sign
    cases fuel <;> cases ownBit <;> simp [enumerateGuardedGeometry486,ran]
  | @step here next finish w moves points bit exact guard safe later ih =>
    cases fuel with
    | zero => simp at budget
    | succ k =>
      have root := complete_palette_checks_the_exact_independent_sign complete guard
        (bit := false) (by simp [safe])
      have small : moves.length ≤ k := Nat.le_of_succ_le_succ budget
      simp only [enumerateGuardedGeometry486,root,List.mem_cons]
      right
      apply List.mem_flatMap.mpr
      refine ⟨(w,next),finite_hops_are_exact_existing_written_visits486.mpr ⟨exact⟩,?_⟩
      exact List.mem_map.mpr ⟨⟨moves,points,finish,bit⟩,ih k small,rfl⟩

theorem original_syntax_budget_covers_every_independent_guarded_old_geometry486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} (complete : CompletePalette486 s pos rel palette)
    {first last : Site s pos} {moves points bit}
    (independent : Trail s pos rel first moves points last bit) :
    (⟨moves,points,last,bit⟩ : GeometricVisit486 s pos) ∈
      enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first := by
  apply every_bounded_independent_visit_occurs_in_the_geometry_enumerator486 complete independent
  have budget := every_existing_finite_visit_stops_within_the_original_written_budget486 independent
  omega

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
