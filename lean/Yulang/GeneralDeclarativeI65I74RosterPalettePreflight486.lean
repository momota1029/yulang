import Yulang.GeneralDeclarativeI65I74ComputedWholeRoster486
import Yulang.GeneralDeclarativeI65I74ReachablePalettePreflight486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck)

def allOriginalArgumentPalettesReady486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (visibleOrdinal : Nat) : Nat → List (Fin n) → Bool
  | _,[] => true
  | argument,site::rest =>
    match readOriginalArgumentStart486 p gd pos visibleOrdinal argument site with
    | none => false
    | some started =>
      paletteReadyWithinOriginalBudget486 rel palette (originalNodeBudget486 started.site.pattern) started.site &&
      allOriginalArgumentPalettesReady486 p gd pos rel palette visibleOrdinal (argument+1) rest

def wholeOriginalRosterPaletteReady486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (coordinates : List (Fin n)) : Bool :=
  (List.range (visible485 p).length).all
    (fun idx => allOriginalArgumentPalettesReady486 p gd pos rel palette idx 0 coordinates)

def readPaletteCoveredPreElection486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (roots : List (Checkpoint n))
    (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 :=
  if requestRootCheck p pos rel roots && wholeOriginalRosterPaletteReady486 p gd pos rel palette (roots.map Checkpoint.which)
  then readComputedPreElection486 p gd pos rel palette roots permit
  else none


private theorem rewriting_the_argument_index_keeps_the_same_geometric_start
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {i a b : Nat} {point : Fin n}
    (same : a = b) (started : OriginalArgumentStart486 p gd pos i a point) :
    (same ▸ started : OriginalArgumentStart486 p gd pos i b point).site = started.site := by
  cases same
  rfl

private theorem exact_argument_source_uses_a_ready_palette
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {i : Nat} {coordinates : List (Fin n)} {offset : Nat}
    (good : allOriginalArgumentPalettesReady486 p gd pos rel palette i offset coordinates = true)
    (j : Nat) (point : Fin n) (whereAt : coordinates[j]? = some point)
    (actual : OriginalArgumentStart486 p gd pos i (offset+j) point) :
    paletteReadyWithinOriginalBudget486 rel palette (originalNodeBudget486 actual.site.pattern) actual.site = true := by
  induction coordinates generalizing offset j with
  | nil => simp at whereAt
  | cons root rest ih =>
    cases started : readOriginalArgumentStart486 p gd pos i offset root with
    | none => simp [allOriginalArgumentPalettesReady486,started] at good
    | some selected =>
      have split : paletteReadyWithinOriginalBudget486 rel palette
          (originalNodeBudget486 selected.site.pattern) selected.site = true ∧
          allOriginalArgumentPalettesReady486 p gd pos rel palette i (offset+1) rest = true := by
        simpa [allOriginalArgumentPalettesReady486,started] using good
      cases j with
      | zero =>
        have same : root = point := Option.some.inj whereAt
        subst point
        have ran := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486 actual
        have equal : selected = actual := Option.some.inj (started.symm.trans ran)
        exact equal ▸ split.1
      | succ j =>
        have ordinal : (offset+1)+j = offset+(j+1) := by omega
        have returned := ih split.2 j whereAt (ordinal.symm ▸ actual)
        simpa only [rewriting_the_argument_index_keeps_the_same_geometric_start] using returned

theorem accepted_palette_covered_tape_has_every_original_candidate_argument_ready486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool} {status}
    (ran : readPaletteCoveredPreElection486 p gd pos rel palette roots permit = some status) :
    readComputedPreElection486 p gd pos rel palette roots permit = some status ∧
    ∀ i : Fin (visible485 p).length, ∀ argument root,
      (roots.map Checkpoint.which)[argument]? = some root →
      ∀ actual : OriginalArgumentStart486 p gd pos i.val argument root,
        paletteReadyWithinOriginalBudget486 rel palette (originalNodeBudget486 actual.site.pattern) actual.site = true := by
  unfold readPaletteCoveredPreElection486 at ran
  split at ran
  · rename_i coverage
    refine ⟨ran,fun i argument root atRoot actual => ?_⟩
    have all := (Bool.and_eq_true_iff.mp coverage).2
    have ready := (List.all_eq_true.mp all) i.val (List.mem_range.mpr i.isLt)
    have wanted := exact_argument_source_uses_a_ready_palette ready argument root atRoot
      ((Nat.zero_add _).symm ▸ actual)
    simpa only [rewriting_the_argument_index_keeps_the_same_geometric_start] using wanted
  · cases ran

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
