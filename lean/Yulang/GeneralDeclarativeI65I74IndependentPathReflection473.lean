import Yulang.GeneralDeclarativeI65I74IndependentPathReplay473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationAlternatives473 (Place Positions oldPosition graphOf readAlternatives)
open QuotientObservation471 (ReturnsUpToEquality)

theorem read_checkpoint_guards
    {s : OwnState} {pos : Positions n} {relation : List (Fin n × Fin n)}
    {atSite : Place} {c : Checkpoint n} {b : Bool}
    (read : readCheck s pos relation atSite c = some b) :
    GuardedObservationInput s pos relation c.which ∧
      oldPosition pos c.which = atSite ∧ (b = true ↔ ReturnsUpToEquality (graphOf s pos) c.which) := by
  have sign := checkpoint_does_not_substitute_a_place_or_change_its_bit read
  refine ⟨?_, sign⟩
  unfold readCheck at read
  split at read
  · exact accepted_observation_yields_all_input_guards read
  · cases read

theorem actual_read_reflects_the_independent_path_and_all_prefix_guards
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {p : Pattern} {query raw : Expr} {site : Place} {wire : PathWire n}
    {report : TypedPathResult s positions site p query raw wire}
    (ran : readLiteralPath s positions rel site p query raw wire = some report) :
    oldPosition positions wire.here.which = site ∧
      IndependentPath s positions rel wire.here.which p query raw (wire.rest.map Prod.fst)
        report.suffix report.final report.bit := by
  rcases wire with ⟨here,rest⟩
  induction rest generalizing here site p query raw with
  | nil =>
    rw [readLiteralPath] at ran
    split at ran
    · cases ran
    · rename_i b check
      cases Option.some.inj ran
      obtain ⟨guard,whereAt,sign⟩ := read_checkpoint_guards check
      exact ⟨whereAt,.terminal guard sign⟩
  | cons step remaining ih =>
    rcases step with ⟨move,follow⟩
    rw [readLiteralPath] at ran
    split at ran
    · rename_i check
      obtain ⟨guard,whereAt,sign⟩ := read_checkpoint_guards check
      cases readStep : readLiteralVisitStep s p query raw move with
      | none => simp [readStep,bind,Option.bind] at ran
      | some actual =>
        simp only [readStep,bind,Option.bind] at ran
        split at ran
        · cases ran
        · rename_i next nextAddress
          cases later : readLiteralPath s positions rel next actual.writtenChild actual.childQuery
              actual.actualRawChild ⟨follow,remaining⟩ with
          | none => simp [later] at ran
          | some tail =>
            simp only [later] at ran
            cases ran
            obtain ⟨atNext,independent⟩ := ih follow later
            exact ⟨whereAt,.branch move actual guard
              (fun recurs => Bool.false_ne_true (sign.mpr recurs))
              (by simpa [whereAt,atNext] using nextAddress) independent⟩
    · cases ran

theorem independent_path_iff_exact_finite_replay
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {here p query raw steps suffix final bit} :
    IndependentPath s positions rel here p query raw steps suffix final bit ↔
    ∃ (wire : PathWire n) (reported : TypedPathResult s positions (oldPosition positions here) p query raw wire),
      wire.here.which = here ∧ wire.rest.map Prod.fst = steps ∧
      readLiteralPath s positions rel (oldPosition positions here) p query raw wire = some reported ∧
      reported.suffix = suffix ∧ reported.final = final ∧ reported.bit = bit := by
  constructor
  · exact independent_path_has_finite_replay_at_its_exact_terminal
  · rintro ⟨wire,reported,hops,stepsEq,replayed,written,endAt,output⟩
    have reflects := (actual_read_reflects_the_independent_path_and_all_prefix_guards replayed).2
    simpa [hops,stepsEq,written,endAt,output] using reflects

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
