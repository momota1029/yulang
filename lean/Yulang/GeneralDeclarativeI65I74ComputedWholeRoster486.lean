import Yulang.GeneralDeclarativeI65I74AllOriginalArgumentFootprints486
import Yulang.GeneralDeclarativeI65I74AllDemandedRootsBeforeElection486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe requestRootCheck requestRootCheckSound)

structure ComputedOriginalCandidate486 (n : Nat) where
  authoredOrdinal : Nat
  keys : List (CandidateVisitKey485 n)
  packet : PlannedCandidateWire485 n

def permitAtOriginalVisibleSlot486 {n : Nat} (p : FullProblem)
    (permit : Nat → CandidateVisitKey485 n → Bool) (i : Nat) (key : CandidateVisitKey485 n) : Bool :=
  match rosterCell485 p i with
  | none => false
  | some (ordinal,_) => permit ordinal key

def compileOriginalCandidate486 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (roots : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool) (i : Nat) :
    Option (ComputedOriginalCandidate486 n) := do
  let (ord,decl) ← rosterCell485 p i
  if decl.head.length = p.old.root.demand.arguments.length then
    let (keys,wire) ← computeAllActualArgumentFootprints486 p gd pos rel palette i (permit ord) roots
    pure ⟨ord,keys,⟨i,wire⟩⟩
  else none

def compileWholeOriginalRoster486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (roots : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) :
    Option (List (ComputedOriginalCandidate486 n)) :=
  (List.range (visible485 p).length).mapM (compileOriginalCandidate486 p gd pos rel palette roots permit)

/-- Prepare and independently recheck the generated G05 tape. The
request roots are checked first. Partial or unsupported plans are not
reinterpreted as mismatch; no election policy is installed here. -/
def readComputedPreElection486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (roots : List (Checkpoint n))
    (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 :=
  if requestRootCheck p pos rel roots then do
    let computed ← compileWholeOriginalRoster486 p gd pos rel palette (roots.map Checkpoint.which) permit
    readPlannedPreElection485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit)
      (computed.map fun x => (x.authoredOrdinal,x.packet))
  else none

theorem computed_pre_election_reads_only_the_original_rooted_whole_roster486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {status : PreElection485}
    (ran : readComputedPreElection486 p gd pos rel palette roots permit = some status) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower))
      (roots.map Checkpoint.which) ∧
    ∃ rows, compileWholeOriginalRoster486 p gd pos rel palette (roots.map Checkpoint.which) permit = some rows ∧
      readPlannedPreElection485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit) (rows.map fun x => (x.authoredOrdinal,x.packet)) = some status := by
  unfold readComputedPreElection486 at ran
  split at ran
  · rename_i safe
    refine ⟨requestRootCheckSound _ _ _ _ safe,?_⟩
    cases read : compileWholeOriginalRoster486 p gd pos rel palette (roots.map Checkpoint.which) permit with
    | none => simp [read] at ran
    | some rows => exact ⟨rows,rfl,by simpa [read] using ran⟩
  · cases ran

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
