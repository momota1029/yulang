import Yulang.GeneralDeclarativeI65I74CompileScopedFootprint487
import Yulang.GeneralDeclarativeI65I74AutomaticPaletteEntry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput read_checkpoint_guards)
open TypedRootSafety482 (AllRootSafe requestRootCheck requestRootCheckSound noRootReturnBool)

def compileScopedArguments487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (i : Nat) (permit : CandidateVisitKey485 n → Bool) :
    Nat → List (Fin n) → Option (List (CandidateVisitKey485 n) × List (CandidatePathWire485 n))
  | _, [] => some ([],[])
  | offset, root::rest => do
    let head ← readOriginalArgumentStart486 p gd pos i offset root
    let (keys,wires) ← compileScopedFootprint487 rel palette offset head.site permit
    let (later,packets) ← compileScopedArguments487 p gd pos rel palette i permit (offset+1) rest
    pure (keys ++ later,wires ++ packets)

def compileScopedCandidate487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (roots : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool) (i : Nat) :
    Option (ComputedOriginalCandidate486 n) := do
  let (ordinal,decl) ← rosterCell485 p i
  if decl.head.length = p.old.root.demand.arguments.length &&
      roots.length = p.old.root.demand.arguments.length then
    let (keys,wire) ← compileScopedArguments487 p gd pos rel palette i (permit ordinal) 0 roots
    pure ⟨ordinal,keys,⟨i,wire⟩⟩
  else none

def compileScopedRoster487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (roots : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool) :
    Option (List (ComputedOriginalCandidate486 n)) :=
  (List.range (visible485 p).length).mapM (compileScopedCandidate487 p gd pos rel palette roots permit)

def readScopedPreElection487 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 :=
  if requestRootCheck p pos rel roots then do
    let rows ← compileScopedRoster487 p gd pos rel palette (roots.map Checkpoint.which) permit
    readPlannedPreElection485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit)
      (rows.map fun x => (x.authoredOrdinal,x.packet))
  else none

theorem scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool} {out : PreElection485}
    (ran : readScopedPreElection487 p gd pos rel palette roots permit = some out) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) (roots.map Checkpoint.which) ∧
      ∃ rows, compileScopedRoster487 p gd pos rel palette (roots.map Checkpoint.which) permit = some rows ∧
        readPlannedPreElection485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
          (permitAtOriginalVisibleSlot486 p permit) (rows.map fun x => (x.authoredOrdinal,x.packet)) = some out := by
  unfold readScopedPreElection487 at ran
  split at ran
  · rename_i safe
    refine ⟨requestRootCheckSound _ _ _ _ safe,?_⟩
    cases made : compileScopedRoster487 p gd pos rel palette (roots.map Checkpoint.which) permit with
    | none => simp [made] at ran
    | some rows => exact ⟨rows,rfl,by simpa [made] using ran⟩
  · cases ran

def OriginalRosterPermissionIsPrefixCoherent487 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (permit : Nat → CandidateVisitKey485 n → Bool) : Prop :=
  ∀ (i arg : Nat) (root : Fin n) (head : OriginalArgumentStart486 p gd pos i arg root),
    originalTerminalPermissionRespectsPrefixes487 rel palette arg head.site (permit head.ordinal)

theorem scoped_arguments_reproduce_exact_ordered_packet_list487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i : Nat) (permit : CandidateVisitKey485 n → Bool) (offset : Nat) (roots : List (Fin n))
    (guard : ∀ j ∈ roots, GuardedObservationInput p.old.state.core pos rel j)
    (coherent : ∀ arg root (head : OriginalArgumentStart486 p gd pos i arg root),
      originalTerminalPermissionRespectsPrefixes487 rel palette arg head.site permit) :
    compileScopedArguments487 p gd pos rel palette i permit offset roots =
      computeOrderedArgumentFootprints486 p gd pos rel palette i permit offset roots := by
  induction roots generalizing offset with
  | nil => rfl
  | cons root rest ih =>
    have later := ih (offset+1) (fun j h => guard j (List.mem_cons_of_mem _ h))
    simp only [compileScopedArguments487,computeOrderedArgumentFootprints486]
    cases h : readOriginalArgumentStart486 p gd pos i offset root with
    | none => rfl
    | some head =>
      have first := complete_guarded_old_input_gives_identical_scoped_packet_computation487 complete
        (guard root (List.mem_cons_self ..)) (coherent offset root head)
      change (do
        let (keys,wires) ← compileScopedFootprint487 rel palette offset head.site permit
        let (other,tail) ← compileScopedArguments487 p gd pos rel palette i permit (offset+1) rest
        pure (keys ++ other,wires ++ tail)) = _
      rw [first,later]
      rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
