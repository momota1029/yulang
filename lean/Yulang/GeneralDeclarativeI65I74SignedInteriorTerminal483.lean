import Yulang.GeneralDeclarativeI65I74SignedInteriorPath483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site Trail TrailWire readTrail)
open LiteralVisits473 (StepWire Checkpoint read_checkpoint_guards)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleGraphBisimulation (ObservationallyEqual)

def terminalPair {p : FullProblem} {pos : Positions n}
    (left right : Site p.old.state.core pos)
    (path : List (Site p.old.state.core pos × Site p.old.state.core pos)) :
    Site p.old.state.core pos × Site p.old.state.core pos :=
  match path with
  | [] => (left,right)
  | (l,r)::tail => terminalPair (p := p) l r tail

theorem terminal_pair_is_one_of_the_selected_positions
    {p : FullProblem} {pos : Positions n}
    (left right : Site p.old.state.core pos) (path : List (Site p.old.state.core pos × Site p.old.state.core pos)) :
    terminalPair (p := p) left right path ∈ (left,right)::path := by
  induction path generalizing left right with
  | nil => simp [terminalPair]
  | cons head rest ih =>
    exact List.mem_cons_of_mem _ (ih head.1 head.2)

theorem equal_finite_selection_replays_the_exact_ambient_terminal
    {p : FullProblem} {pos : Positions n} {table : Table} {rel : List (Fin n × Fin n)}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path} {terminal bit}
    (source : InteriorSequence (p := p) table left right card moves path)
    {oldMoves : List StepWire} {oldPoints : List (Fin n)}
    (ambient : Trail p.old.state.core pos rel right oldMoves oldPoints terminal bit)
    (movesMatch : moves.map InteriorMove.step = oldMoves)
    (pointsMatch : moves.map InteriorMove.ambient = oldPoints) :
    (terminalPair (p := p) left right path).2 = terminal := by
  induction source generalizing oldMoves oldPoints with
  | nil =>
    cases ambient with
    | stop => rfl
    | step => simp at movesMatch
  | @cons left right move card tail rest visit _ _ sequence ih =>
    cases ambient with
    | stop => simp at movesMatch
    | @step _ next _ oldMove oldTail oldRest _ hop _ _ rest =>
      simp only [List.map_cons,List.cons.injEq] at movesMatch pointsMatch
      have oldRead := Producer479.exact_hop_has_a_unique_replay479 hop
      rcases movesMatch with ⟨moveEq,movesMatch⟩
      rcases pointsMatch with ⟨pointEq,pointsMatch⟩
      rw [←moveEq,←pointEq] at oldRead
      have matched := Option.some.inj (visit.ambientRead.symm.trans oldRead)
      exact ih (matched.symm ▸ rest) movesMatch pointsMatch

theorem signed_interior_terminal_is_the_same_physical_site_and_same_quotient_sign
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {rel : List (Fin n × Fin n)}
    {w : SignedInteriorWire n}
    (ordered : (List.ofFn (oldPosition pos)).Nodup)
    (same : ObservationallyEqual (graphOf p.old.state.core pos) left.index right.index)
    (out : SignedInteriorPath (p := p) table left right card rel w) :
    let pair := terminalPair (p := p) left right out.sites.path
    pair.2 = out.terminal ∧
    (out.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos) pair.1.index) := by
  have trail := (Producer479.finite_trail_wire_reflects_exact_selected_path479 out.exactAmbient).2
  have renamed : Trail p.old.state.core pos rel right
      ((readPairedIndices w.moves).map InteriorMove.step)
      ((readPairedIndices w.moves).map InteriorMove.ambient) out.terminal out.bit := by
    simpa [readPairedIndices,SignedInteriorWire.ambient,List.map_map,Function.comp_def] using trail
  have endSite := equal_finite_selection_replays_the_exact_ambient_terminal out.sites.actual renamed rfl rfl
  have current := the_paired_quotient_signs_follow_the_independently_checked_path ordered same out.sites.actual
    _ (terminal_pair_is_one_of_the_selected_positions (p := p) left right out.sites.path)
  have bit := (Producer479.declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 trail).2
  exact ⟨endSite,(endSite.symm ▸ bit).trans current.2.symm⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
