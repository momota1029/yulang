import Yulang.GeneralDeclarativeI65I74G05TokenMap490
import Yulang.GeneralDeclarativeI65I74G05CoordinateDispatch488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck)

private def guardedAssembly490 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (gate : Bool) (compile : Option (List (ComputedOriginalCandidate486 n)))
    (tape : List (Nat × PlannedCandidateWire485 n))
    (codec : G05LocalChecker487) (tokens : List (Option (List Nat))) : Option (G05Report487 n) :=
  if gate then do
    let rows ← compile
    let signed ← readTape485 p (readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit)) tape
    let report ← readG05OrderedRows487 p codec 0 rows signed tokens
    pure ⟨report,G05PriorityOfRows487 report⟩
  else none

private theorem guarded_assembly_preserves_the_computed_token_replacement490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {gate : Bool} {compile : Option (List (ComputedOriginalCandidate486 n))}
    {tape : List (Nat × PlannedCandidateWire485 n)}
    {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {tokens : List (Option (List Nat))} {r : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (ran : guardedAssembly490 p gd pos rel permit gate compile tape left tokens = some r) :
    ∃ fresh, translateG05LocalTokenList490 p left translate 0 tokens = some fresh ∧
      guardedAssembly490 p gd pos rel permit gate compile tape right fresh = some r := by
  cases gate with
  | false => simp [guardedAssembly490] at ran
  | true =>
    cases compile with
    | none => simp [guardedAssembly490] at ran
    | some rows =>
      let read := readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)
      cases taped : readTape485 p read tape with
      | none => simp [guardedAssembly490,read,taped,Option.bind] at ran
      | some signed =>
        cases assembled : readG05OrderedRows487 p left 0 rows signed tokens with
        | none => simp [guardedAssembly490,read,taped,assembled,Option.bind] at ran
        | some report =>
          obtain ⟨fresh,transformed,again⟩ :=
            a_checked_g05_ordered_assembly_is_preserved_by_a_lawful_computable_token_map490 lawful assembled
          refine ⟨fresh,transformed,?_⟩
          simpa [guardedAssembly490,read,taped,again,Option.bind] using
            (show some ⟨report,G05PriorityOfRows487 report⟩ = some r by
              simpa [guardedAssembly490,read,taped,assembled,Option.bind] using ran)

theorem a_scoped_g05_report_reencodes_only_local_tokens_preserving_original_roots_and_tape490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (ran : readG05ScopedReport487 p gd pos rel coords permit left wire = some r) :
    ∃ fresh, translateG05LocalTokenList490 p left translate 0 wire.localTokens = some fresh ∧
      readG05ScopedReport487 p gd pos rel coords permit right {wire with localTokens := fresh} = some r := by
  let gate : Bool := wire.roots.map Checkpoint.which = coords && requestRootCheck p pos rel wire.roots
  let compile := compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
    coords permit
  exact guarded_assembly_preserves_the_computed_token_replacement490
    (p := p) (gd := gd) (pos := pos) (rel := rel) (permit := permit)
    (gate := gate) (compile := compile) (tape := wire.tape) (tokens := wire.localTokens) lawful ran

theorem a_zero_argument_g05_report_reencodes_only_local_tokens_preserving_original_roots_and_tape490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (ran : readNoArgumentG05Report488 p gd pos rel permit left wire = some r) :
    ∃ fresh, translateG05LocalTokenList490 p left translate 0 wire.localTokens = some fresh ∧
      readNoArgumentG05Report488 p gd pos rel permit right {wire with localTokens := fresh} = some r := by
  let gate := wire.roots.isEmpty && requestRootCheck p pos rel wire.roots
  exact guarded_assembly_preserves_the_computed_token_replacement490
    (p := p) (gd := gd) (pos := pos) (rel := rel) (permit := permit)
    (gate := gate) (compile := compileNoArgumentRoster488 p) (tape := wire.tape)
    (tokens := wire.localTokens) lawful ran

theorem a_lawful_computable_g05_token_map_preserves_accepted_reports_for_any_actual_arity490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr r) (.inr wire) = true) :
    ∃ fresh, translateG05LocalTokenList490 p left translate 0 wire.localTokens = some fresh ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit right
        (.inr r) (.inr {wire with localTokens := fresh}) = true := by
  cases coords with
  | nil =>
    cases read : readNoArgumentG05Report488 p gd pos rel permit left wire with
    | none => simp [checkFlatWithDemandScopedG05Tag488,read] at accepted
    | some normalized =>
      obtain ⟨fresh,mapped,replayed⟩ :=
        a_zero_argument_g05_report_reencodes_only_local_tokens_preserving_original_roots_and_tape490 lawful read
      exact ⟨fresh,mapped,by
        simpa only [checkFlatWithDemandScopedG05Tag488,replayed] using
          (show (g05ReportRowsEquivalent488 normalized.rows r.rows &&
            decide (r.priority = G05PriorityOfRows487 r.rows)) = true by
            simpa only [checkFlatWithDemandScopedG05Tag488,read] using accepted)⟩
  | cons first rest =>
    cases read : readG05ScopedReport487 p gd pos rel (first::rest) permit left wire with
    | none => simp [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,read] at accepted
    | some normalized =>
      obtain ⟨fresh,mapped,replayed⟩ :=
        a_scoped_g05_report_reencodes_only_local_tokens_preserving_original_roots_and_tape490 lawful read
      exact ⟨fresh,mapped,by
        simpa only [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,replayed] using
          (show (g05ReportRowsEquivalent488 normalized.rows r.rows &&
            decide (r.priority = G05PriorityOfRows487 r.rows)) = true by
            simpa only [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,read] using accepted)⟩

theorem a_usable_g05_token_map_outputs_an_accepted_wire_with_exactly_the_same_roots_and_candidate_tape490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr r) (.inr wire) = true) :
    ∃ output, translateG05WitnessTokens490 p left translate wire = some output ∧
      output.roots = wire.roots ∧ output.tape = wire.tape ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit right (.inr r) (.inr output) = true := by
  obtain ⟨fresh,converted,again⟩ :=
    a_lawful_computable_g05_token_map_preserves_accepted_reports_for_any_actual_arity490 lawful accepted
  exact ⟨{wire with localTokens := fresh},by simp [translateG05WitnessTokens490,converted],rfl,rfl,again⟩

theorem the_accepted_g05_report_rechecks_after_only_local_tokens_change_for_any_actual_arity490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {left right : G05LocalChecker487} {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (covers : G05LocalCodecCovers490 left right)
    (accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr r) (.inr wire) = true) :
    ∃ fresh, checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit right
      (.inr r) (.inr {wire with localTokens := fresh}) = true := by
  obtain ⟨fresh,_,rechecked⟩ :=
    a_lawful_computable_g05_token_map_preserves_accepted_reports_for_any_actual_arity490
      (chosen_g05_token_map_is_lawful_when_the_target_codec_covers_the_source490 covers) accepted
  exact ⟨fresh,rechecked⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
