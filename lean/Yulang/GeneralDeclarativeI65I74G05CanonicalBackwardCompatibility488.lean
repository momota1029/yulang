import Yulang.GeneralDeclarativeI65I74G05CoordinateDispatch488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck)

private theorem mapM_replays_any_already_successful_input_under_success_preserving_reads488
    {α β : Type} {input : List α} {old updated : α → Option β} {result : List β}
    (replay : ∀ a b, old a = some b → updated a = some b)
    (ran : input.mapM (m := Option) old = some result) :
    input.mapM (m := Option) updated = some result := by
  induction input generalizing result with
  | nil => exact ran
  | cons first tail ih =>
    cases r : old first with
    | none => simp [List.mapM_cons,r] at ran
    | some a =>
      cases q : tail.mapM (m := Option) old with
      | none => simp [List.mapM_cons,r,q] at ran
      | some more =>
        have hit : a::more = result := Option.some.inj (by simpa [List.mapM_cons,r,q] using ran)
        subst result
        simp [List.mapM_cons,replay _ _ r,ih q,Option.bind]

theorem old_successful_empty_scope_compilation_is_the_new_empty_roster488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (allow : Nat → CandidateVisitKey485 n → Bool) {rows : List (ComputedOriginalCandidate486 n)}
    (old : compileScopedRoster487 p gd pos rel palette [] allow = some rows) :
    compileNoArgumentRoster488 p = some rows := by
  unfold compileScopedRoster487 at old
  unfold compileNoArgumentRoster488
  apply mapM_replays_any_already_successful_input_under_success_preserving_reads488 _ old
  intro i row available
  unfold compileScopedCandidate487 at available
  cases known : rosterCell485 p i with
  | none => simp [known] at available
  | some ranked =>
    obtain ⟨ord,d⟩ := ranked
    simp only [known,bind,Option.bind] at available
    split at available
    · simpa [originalNoArgumentCandidate488,known,compileScopedArguments487] using available
    · cases available

theorem old_checked_empty_scope_reports_replay_without_changing_the_report_or_witness488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (localCheck : G05LocalChecker487)
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (old : readG05ScopedReport487 p gd pos rel [] permit localCheck w = some r) :
    readNoArgumentG05Report488 p gd pos rel permit localCheck w = some r := by
  unfold readG05ScopedReport487 at old
  split at old
  · rename_i validated
    obtain ⟨coords,root⟩ := Bool.and_eq_true_iff.mp validated
    have empty : w.roots = [] := List.eq_nil_of_length_eq_zero (by
      have size := congrArg List.length (of_decide_eq_true coords : w.roots.map Checkpoint.which = [])
      simpa only [List.length_map,List.length_nil] using size)
    have ok : (w.roots.isEmpty && requestRootCheck p pos rel w.roots) = true :=
      Bool.and_eq_true_iff.mpr ⟨List.isEmpty_iff.mpr empty,root⟩
    rw [readNoArgumentG05Report488,ite_eq_left ok]
    let palette := computedOriginalPalette486 p.old.state.core pos rel
    cases ran : compileScopedRoster487 p gd pos rel palette [] permit with
    | none => simp [palette,ran,Option.bind] at old
    | some rows =>
      have new := old_successful_empty_scope_compilation_is_the_new_empty_roster488 p gd pos rel palette permit ran
      rw [new]
      simpa [palette,ran,Option.bind] using old
  · cases old

private theorem actual_checked_report_always_carries_its_own_priority488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (localCheck : G05LocalChecker487)
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (ran : readG05ScopedReport487 p gd pos rel coords permit localCheck w = some r) :
    r.priority = G05PriorityOfRows487 r.rows := by
  unfold readG05ScopedReport487 at ran
  split at ran
  · let palette := computedOriginalPalette486 p.old.state.core pos rel
    cases compiled : compileScopedRoster487 p gd pos rel palette coords permit with
    | none => simp [palette,compiled,Option.bind] at ran
    | some computed =>
      let reader := readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)
      cases signed : readTape485 p reader w.tape with
      | none => simp [palette,compiled,reader,signed,Option.bind] at ran
      | some signs =>
        cases assembled : readG05OrderedRows487 p localCheck 0 computed signs w.localTokens with
        | none => simp [palette,compiled,reader,signed,assembled,Option.bind] at ran
        | some rows =>
          have eq : (⟨rows,G05PriorityOfRows487 rows⟩ : G05Report487 n) = r := Option.some.inj
            (by simpa [palette,compiled,reader,signed,assembled,Option.bind] using ran)
          subst r
          rfl
  · cases ran

theorem every_previously_accepted_canonical_g05_report_still_accepts_the_same_wire488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (localCheck : G05LocalChecker487)
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (old : checkFlatWithG05Tag487 p gd pos rel coords permit localCheck (.inr r) (.inr w) = true) :
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit localCheck (.inr r) (.inr w) = true := by
  have exact := new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mp old
  have pair : (g05ReportRowsEquivalent488 r.rows r.rows &&
      decide (r.priority = G05PriorityOfRows487 r.rows)) = true := by
    have good : g05ReportRowsEquivalent488 r.rows r.rows = true := by
      apply indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 rfl
      intro i a b first second
      have same := Option.some.inj (first.symm.trans second)
      subst b
      exact ⟨rfl,rfl,fun _ => Iff.rfl⟩
    exact Bool.and_eq_true_iff.mpr ⟨good,
      decide_eq_true (actual_checked_report_always_carries_its_own_priority488 p gd pos rel coords permit localCheck exact)⟩
  cases coords with
  | nil =>
    have upgraded := old_checked_empty_scope_reports_replay_without_changing_the_report_or_witness488
      p gd pos rel permit localCheck exact
    simpa only [checkFlatWithDemandScopedG05Tag488,upgraded] using pair
  | cons _ _ =>
    simpa only [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,exact] using pair

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
