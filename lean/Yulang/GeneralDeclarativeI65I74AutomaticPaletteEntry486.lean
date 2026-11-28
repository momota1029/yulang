import Yulang.GeneralDeclarativeI65I74ComputedOldPalette486
import Yulang.GeneralDeclarativeI65I74ReadyOriginalRosterCompleteness486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck)
open GeneralDeclarations (Declaration)

/-- No external palette, planned key list, or candidate wire is used.
The old graph and relation are supplied, as are the checked request
root addresses and the independent candidate-local permission. -/
def readAutomaticPalettePreElection486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 :=
  readPaletteCoveredPreElection486 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel) roots permit

theorem scoped_original_roster_finitely_replays_without_any_caller_candidate_packets_or_palette486
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permission : ∀ ord key, permit ord key = true → Authorized ord key)
    (rootsChecked : requestRootCheck p pos rel roots = true)
    (count : roots.length = p.old.root.demand.arguments.length)
    (actualArity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (starts : ∀ i : Fin (visible485 p).length, ∀ argument root,
      (roots.map Checkpoint.which)[argument]? = some root →
      Nonempty (OriginalArgumentStart486 p gd pos i.val argument root)) :
    ∃ bits : List (Nat × Bool), readAutomaticPalettePreElection486 p gd pos rel roots permit =
      some (gate485 bits) :=
  checked_palette_and_original_candidate_data_reify_pre_election_at_exact_demand_roots486
    p gd pos rel (computedOriginalPalette486 _ _ _)
    (real_existing_graph_finitely_computes_its_verified_optional_palette486 _ _ _)
    roots permit Authorized permission rootsChecked count actualArity starts

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
