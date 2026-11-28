import Yulang.GeneralDeclarativeI65I74RosterPalettePreflight486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open Producer479 (Site)
open LiteralVisits473 (Checkpoint)

theorem ready_original_plan_exactly_covers_every_independently_authorized_visit486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    (palette : SignedPalette486 n) (argument : Nat) (first : Site s pos)
    (complete : paletteReadyWithinOriginalBudget486 rel palette (originalNodeBudget486 first.pattern) first = true)
    (permit : CandidateVisitKey485 n → Bool)
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
        exact (original_required_palette_preflight_gives_complete_exact_old_search486 complete).mpr faithful
    · rw [←equality] at authorized ⊢
      have good := (lawful _).mpr authorized
      have nonempty : visit.moves.isEmpty = false := by
        cases h : visit.moves with
        | nil => exact False.elim (proper h)
        | cons => rfl
      simp [good,nonempty]


theorem accepted_ready_roster_preserves_and_reflects_every_prior_authorized_proper_visit_of_each_head486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool} {status}
    (ran : readPaletteCoveredPreElection486 p gd pos rel palette roots permit = some status)
    (i : Fin (visible485 p).length) {argument : Nat} {root : Fin n}
    (here : (roots.map Checkpoint.which)[argument]? = some root)
    (original : OriginalArgumentStart486 p gd pos i argument root)
    (Authorized : CandidateVisitKey485 n → Prop)
    (exactPermit : ∀ key, permit original.ordinal key = true ↔ Authorized key)
    (key : CandidateVisitKey485 n) :
    key ∈ finiteAuthorizedVisitPlan486 rel palette argument original.site (permit original.ordinal) ↔
      IndependentAuthorizedVisit486 rel argument original.site Authorized key := by
  have ready := (accepted_palette_covered_tape_has_every_original_candidate_argument_ready486 ran).2
    i argument root here original
  exact ready_original_plan_exactly_covers_every_independently_authorized_visit486 palette argument
    original.site ready (permit original.ordinal) Authorized exactPermit key

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
