import Yulang.GeneralDeclarativeI65I74CoveredCandidateReification485
import Yulang.GeneralDeclarativeI65I74BoundedCandidateGeometry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open Producer479 (Site Trail)

def exactGeometryKey486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) (visit : GeometricVisit486 s pos) : CandidateVisitKey485 n :=
  ⟨argument,visit.moves.map (fun w => (w.action,w.written)),first.index::visit.points⟩

/-- The independent authority predicate must be supplied separately.
This enumerator constructs no access authority and no active output. -/
def finiteAuthorizedVisitPlan486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) (argument : Nat) (first : Site s pos)
    (permit : CandidateVisitKey485 n → Bool) : List (CandidateVisitKey485 n) :=
  (enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first).filterMap fun visit =>
    let key := exactGeometryKey486 argument first visit
    if visit.moves.isEmpty || !permit key then none else some key

def IndependentAuthorizedVisit486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (argument : Nat) (first : Site s pos)
    (Authorized : CandidateVisitKey485 n → Prop) (key : CandidateVisitKey485 n) : Prop :=
  ∃ visit : GeometricVisit486 s pos,
    Trail s pos rel first visit.moves visit.points visit.last visit.bit ∧
    visit.moves ≠ [] ∧ exactGeometryKey486 argument first visit = key ∧ Authorized key

theorem generated_plan_keys_are_exactly_the_authorized_existing_proper_visits486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    (palette : SignedPalette486 n) (complete : CompletePalette486 s pos rel palette)
    (argument : Nat) (first : Site s pos) (permit : CandidateVisitKey485 n → Bool)
    (Authorized : CandidateVisitKey485 n → Prop)
    (lawful : ∀ key, permit key = true ↔ Authorized key) (key : CandidateVisitKey485 n) :
    key ∈ finiteAuthorizedVisitPlan486 rel palette argument first permit ↔
      IndependentAuthorizedVisit486 rel argument first Authorized key := by
  unfold finiteAuthorizedVisitPlan486
  constructor
  · intro member
    obtain ⟨visit,found,offered⟩ := List.mem_filterMap.mp member
    dsimp only at offered
    split at offered
    · cases offered
    · rename_i good
      have same := Option.some.inj offered
      subst key
      have proper : visit.moves ≠ [] := by
        intro empty
        exact good (by simp [empty])
      have accepted : permit (exactGeometryKey486 argument first visit) = true := by
        cases guard : permit (exactGeometryKey486 argument first visit) with
        | false => exact False.elim (good (by simp [guard]))
        | true => rfl
      exact ⟨visit,every_enumerated_geometry_is_the_original_independent_guarded_trail486 _ _ _ found,
        proper,rfl,(lawful _).mp accepted⟩
  · rintro ⟨visit,faithful,proper,equality,authorized⟩
    refine List.mem_filterMap.mpr ⟨visit,?_,?_⟩
    · cases visit with
      | mk moves points terminal bit =>
        exact original_syntax_budget_covers_every_independent_guarded_old_geometry486 complete faithful
    · rw [←equality] at authorized ⊢
      have good := (lawful _).mpr authorized
      have nonempty : visit.moves.isEmpty = false := by
        cases h : visit.moves with
        | nil => exact False.elim (proper h)
        | cons => rfl
      simp [good,nonempty]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
