import Yulang.GeneralDeclarativeI65I74G05ContinuationReflection490

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def G05RuleIsSingleValuedOnOriginalRoster490 (p : FullProblem) (meaning : G05LocalMeaning487) : Prop :=
  ∀ (i : Fin (visible485 p).length) ord d a b, OriginalRosterCell485 p i.val (ord,d) →
    meaning i.val ord d a → meaning i.val ord d b → a = b

theorem an_allowed_g05_choice_at_one_original_slot_can_replace_only_that_slot490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {base : G05OrderedLocalChoices490 p}
    (baseAdmissible : G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning base)
    (i : Fin (visible485 p).length) (ord : Nat) (d : GeneralDeclarations.Declaration)
    (original : OriginalRosterCell485 p i.val (ord,d)) (v : G05LocalVerdict487)
    (admissible : meaning i.val ord d v) :
    ∃ alt : G05OrderedLocalChoices490 p,
      G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning alt ∧
      alt i = (ord,v) ∧ ∀ j, j ≠ i → alt j = base j := by
  let alt : G05OrderedLocalChoices490 p := fun j => if j = i then (ord,v) else base j
  refine ⟨alt,?_,by simp [alt],fun j h => by simp [alt,h]⟩
  intro j
  by_cases eq : j = i
  · subst j
    exact ⟨(baseAdmissible i).1,d,by simpa [alt] using original,by simpa [alt] using admissible⟩
  · simpa [alt,eq] using baseAdmissible j

theorem duplicate_allowed_verdicts_at_one_original_g05_slot_have_distinct_exact_replayable_mark_lists490
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning)
    (base : G05OrderedLocalChoices490 p)
    (baseAdmissible : G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning base)
    (i : Fin (visible485 p).length) (ord : Nat) (d : GeneralDeclarations.Declaration)
    (original : OriginalRosterCell485 p i.val (ord,d)) (a b : G05LocalVerdict487)
    (allowsA : meaning i.val ord d a) (allowsB : meaning i.val ord d b) (different : a ≠ b) :
    ∃ ca cb : G05OrderedLocalChoices490 p,
      (∀ j, j ≠ i → ca j = cb j) ∧ ca i = (ord,a) ∧ cb i = (ord,b) ∧
      List.ofFn ca ≠ List.ofFn cb ∧
      (∃ give, routeG05WithDeferredLocal489 p gd pos rel coords permit test give id = .continued (List.ofFn ca)) ∧
      (∃ give, routeG05WithDeferredLocal489 p gd pos rel coords permit test give id = .continued (List.ofFn cb)) := by
  obtain ⟨ca,validA,atA,unchangedA⟩ :=
    an_allowed_g05_choice_at_one_original_slot_can_replace_only_that_slot490 baseAdmissible i ord d original a allowsA
  obtain ⟨cb,validB,atB,unchangedB⟩ :=
    an_allowed_g05_choice_at_one_original_slot_can_replace_only_that_slot490 baseAdmissible i ord d original b allowsB
  have reach := fun marks =>
    (attainable_g05_continuation_values_are_exactly_the_independent_ordered_original_choices490
      p gd pos rel coords permit test id Allowed scope meaning protocol marks).mpr
  refine ⟨ca,cb,fun j off => (unchangedA j off).trans (unchangedB j off).symm,atA,atB,?_,
    reach _ ⟨ca,validA,rfl⟩,reach _ ⟨cb,validB,rfl⟩⟩
  intro eq
  have pointwise := congrArg (fun (marks : List (Nat × G05LocalVerdict487)) => marks[i.val]?) eq
  have atChoice : ca i = cb i := by simpa [i.isLt] using pointwise
  exact different (congrArg Prod.snd (atA.symm.trans (atChoice.trans atB)))

/-- In an all-safe scope already admitting one complete ordered choice,
the identity continuation distinguishes exactly failure of single-valuedness
on an actual candidate. No assumption is made about invisible declarations. -/
theorem g05_attainable_ordered_mark_list_is_unique_iff_local_meaning_is_single_valued_at_original_slots490
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning)
    (base : G05OrderedLocalChoices490 p)
    (baseAdmissible : G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning base) :
    (∀ (a b : List (Nat × G05LocalVerdict487)),
      (∃ give, routeG05WithDeferredLocal489 p gd pos rel coords permit test give id = .continued a) →
      (∃ give, routeG05WithDeferredLocal489 p gd pos rel coords permit test give id = .continued b) → a = b) ↔
    G05RuleIsSingleValuedOnOriginalRoster490 p meaning := by
  constructor
  · intro unique i ord d a b origin allowedA allowedB
    by_cases same : a = b
    · exact same
    · obtain ⟨ca,cb,_,_,_,unequal,replayedA,replayedB⟩ :=
        duplicate_allowed_verdicts_at_one_original_g05_slot_have_distinct_exact_replayable_mark_lists490
          p gd pos rel coords permit test Allowed scope meaning protocol base baseAdmissible
          i ord d origin a b allowedA allowedB same
      exact False.elim (unequal (unique (List.ofFn ca) (List.ofFn cb) replayedA replayedB))
  · intro single a b replaysA replaysB
    let run := fun marks =>
      (attainable_g05_continuation_values_are_exactly_the_independent_ordered_original_choices490
        p gd pos rel coords permit test id Allowed scope meaning protocol marks).mp
    obtain ⟨ca,validA,rfl⟩ := run a replaysA
    obtain ⟨cb,validB,rfl⟩ := run b replaysB
    have eq : ca = cb := by
      funext i
      obtain ⟨d,originA,allowedA⟩ := (validA i).2
      obtain ⟨e,originB,allowedB⟩ := (validB i).2
      have same := Option.some.inj
        (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr originA).symm.trans
          ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr originB))
      obtain ⟨ord,decl⟩ := Prod.mk.inj same
      have matched : meaning i.val (ca i).1 d (cb i).2 := by simpa only [ord,decl] using allowedB
      exact Prod.ext ord (single i (ca i).1 d _ _ originA allowedA matched)
    rw [eq]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
