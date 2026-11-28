import Yulang.GeneralDeclarativeI65I74G05LocalMarks487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck requestRootCheckSound AllRootSafe)

def readG05ScopedReport487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (check : G05LocalChecker487) (wire : G05FiniteWitness487 n) : Option (G05Report487 n) :=
  if wire.roots.map Checkpoint.which = coords && requestRootCheck p pos rel wire.roots then do
    let computed ← compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
      coords permit
    let signed ← readTape485 p
      (readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)) wire.tape
    let rows ← readG05OrderedRows487 p check 0 computed signed wire.localTokens
    pure ⟨rows,G05PriorityOfRows487 rows⟩
  else none

def g05ReportData487 {n : Nat} (r : G05Report487 n) :
    (List (Nat × List (CandidateVisitKey485 n) × G05CandidateMark487)) × G05Priority487 :=
  (r.rows.map fun row => (row.ordinal,row.observed,row.mark),r.priority)

private theorem encoding_g05_rows_does_not_lose_the_fields487 {n : Nat}
    {lower upper : List (G05CandidateRow487 n)}
    (same : lower.map (fun r => (r.ordinal,r.observed,r.mark)) =
      upper.map (fun r => (r.ordinal,r.observed,r.mark))) : lower = upper := by
  induction lower generalizing upper with
  | nil => cases upper <;> simp_all
  | cons a tail ih =>
    cases upper with
    | nil => simp at same
    | cons b rest =>
      have eq := List.cons.inj same
      have equal : a = b := by
        cases a
        cases b
        cases eq.1
        rfl
      rw [equal,ih eq.2]

theorem g05_report_data_equality_reconstructs_every_report_field487 {n : Nat} {r s : G05Report487 n}
    (same : g05ReportData487 r = g05ReportData487 s) : r = s := by
  cases r with
  | mk lower first =>
    cases s with
    | mk upper second =>
      have priority : first = second := congrArg Prod.snd same
      have rows : lower = upper :=
        encoding_g05_rows_does_not_lose_the_fields487 (congrArg Prod.fst same)
      subst upper
      subst second
      rfl

def checkFlatWithG05Tag487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (check : G05LocalChecker487) :
    Sum Flat481.FlatReport (G05Report487 n) → Sum Flat481.FlatWitness (G05FiniteWitness487 n) → Bool
  | .inl report,.inl w => Flat481.check_full_flat p report w
  | .inr report,.inr w =>
    match readG05ScopedReport487 p gd pos rel coords permit check w with
    | none => false
    | some confirmed => decide (g05ReportData487 confirmed = g05ReportData487 report)
  | _,_ => false

theorem g05_new_tag_preserves_every_old_bool_and_rejects_crossed_tags487
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (check : G05LocalChecker487)
    (old : Flat481.FlatReport) (w : Flat481.FlatWitness)
    (scopedReport : G05Report487 n) (packet : G05FiniteWitness487 n) :
    checkFlatWithG05Tag487 p gd pos rel coords permit check (.inl old) (.inl w) =
      Flat481.check_full_flat p old w ∧
    checkFlatWithG05Tag487 p gd pos rel coords permit check (.inl old) (.inr packet) = false ∧
    checkFlatWithG05Tag487 p gd pos rel coords permit check (.inr scopedReport) (.inl w) = false :=
  ⟨rfl,rfl,rfl⟩

theorem new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {check : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n} :
    checkFlatWithG05Tag487 p gd pos rel coords permit check (.inr r) (.inr w) = true ↔
      readG05ScopedReport487 p gd pos rel coords permit check w = some r := by
  cases read : readG05ScopedReport487 p gd pos rel coords permit check w with
  | none => simp [checkFlatWithG05Tag487,read]
  | some prior =>
    simp only [checkFlatWithG05Tag487,read,decide_eq_true_eq,Option.some.injEq]
    exact ⟨g05_report_data_equality_reconstructs_every_report_field487,congrArg g05ReportData487⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
