import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site Trail)
open LiteralVisits473 (StepWire read_checkpoint_guards)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table)
open PreparedDeclarations463 (CheckedTable)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

/-- Only proper prefixes are required to be safe, including the starting
point when at least one step is taken. Nothing is inferred for siblings. -/
def safeAuthorPrefixes {p : FullProblem} {pos : Positions n}
    (root : Site p.old.state.core pos) :
    List (Site p.old.state.core pos × Site p.old.state.core pos) → Prop
  | [] => True
  | first :: tail => (¬ ReturnsUpToEquality (graphOf p.old.state.core pos) root.index) ∧
      safeAuthorPrefixes (p := p) first.1 tail

theorem finite_paired_source_prefixes_are_safe_at_exact_selected_nodes
    {p : FullProblem} {pos : Positions n} {table : Table} {rel : List (Fin n × Fin n)}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path} {terminal bit}
    (ordered : (List.ofFn (oldPosition pos)).Nodup)
    (same : ObservationallyEqual (graphOf p.old.state.core pos) left.index right.index)
    (source : InteriorSequence (p := p) table left right card moves path)
    {oldMoves : List StepWire} {oldPoints : List (Fin n)}
    (ambient : Trail p.old.state.core pos rel right oldMoves oldPoints terminal bit)
    (movesMatch : moves.map InteriorMove.step = oldMoves)
    (pointsMatch : moves.map InteriorMove.ambient = oldPoints) :
    safeAuthorPrefixes (p := p) left path := by
  induction source generalizing oldMoves oldPoints with
  | nil => exact trivial
  | @cons left right move card tail rest visit l r sequence ih =>
    cases ambient with
    | stop => simp at movesMatch
    | @step _ next _ oldMove oldTail oldRest _ hop _ safe rest =>
      simp only [List.map_cons,List.cons.injEq] at movesMatch pointsMatch
      rcases movesMatch with ⟨moveEq,movesMatch⟩
      rcases pointsMatch with ⟨pointEq,pointsMatch⟩
      have oldRead := Producer479.exact_hop_has_a_unique_replay479 hop
      rw [←moveEq,←pointEq] at oldRead
      have matched := Option.some.inj (visit.ambientRead.symm.trans oldRead)
      obtain ⟨_,⟨one⟩,_⟩ := focused_card_hop_is_actual_and_keeps_a_single_checked_occurrence visit.author
      obtain ⟨_,⟨two⟩⟩ := Producer479.reified_hop_keeps_the_same_old_place479 visit.ambientRead
      have kind := QuotientObservation471.quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation same
      refine ⟨fun loop => safe (kind.mp loop),?_⟩
      exact ih (InteriorCorrespondence483.paired_selected_children_have_equal_regular_observations
        ordered l r same one two rfl) (matched.symm ▸ rest) movesMatch pointsMatch

theorem every_nonterminal_original_author_site_in_the_rooted_suffix_is_safe
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : Producer479.PriorPhase} {w : RootedInteriorWire n}
    (out : RootedInteriorReceipt p gd pos rel basis w) :
    safeAuthorPrefixes (p := p) out.lexical out.suffix.sites.path := by
  have oldCheckpoint := read_checkpoint_guards out.approach.conclusion.checkedSign
  have ambientIndex := (Producer479.reified_hop_keeps_the_same_old_place479 out.approach.lastRead).1
  have same : ObservationallyEqual (graphOf p.old.state.core pos) out.lexical.index out.approach.last.index := by
    rw [out.anchorIndex,←ambientIndex]
    exact fun d => (out.approach.conclusion.agrees d).symm
  have ambient := (Producer479.finite_trail_wire_reflects_exact_selected_path479 out.suffix.exactAmbient).2
  simp only [RootedInteriorWire.continuation,SignedInteriorWire.ambient] at ambient
  exact finite_paired_source_prefixes_are_safe_at_exact_selected_nodes oldCheckpoint.1.2.1
    same out.suffix.sites.actual ambient (by simp [readPairedIndices,RootedInteriorWire.continuation,List.map_map,Function.comp_def])
    (by simp [readPairedIndices,RootedInteriorWire.continuation,List.map_map,Function.comp_def])

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
