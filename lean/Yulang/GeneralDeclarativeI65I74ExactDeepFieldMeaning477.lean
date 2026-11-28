import Yulang.GeneralDeclarativeI65I74NamedPathMeaning477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions graphOf interpretedAt readAlternatives)
open QuotientObservation471 (ReturnsUpToEquality ExactCone cone_replay_sound cone embedded classOf)
open CommonRoleRegularGraph (successors)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment)
open LiteralVisits473 (readCheck Checkpoint)
open FiniteWorklist (Path)

theorem original_argument_has_a_nonempty_real_walk_to_the_exact_deep_field477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)} (x : NamedFieldTrail477 fixed q table rel outer inner wires) :
    inner.which ∈ successors (graphOf p.old.state.core table) outer.which ∧
    Path (successors (graphOf p.old.state.core table)) inner.which x.last.checkpoint.which ∧
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer.which ∧
    ∀ pt ∈ x.follows.prefixPoints, ¬ ReturnsUpToEquality (graphOf p.old.state.core table) pt := by
  obtain ⟨safe,walk,all,_,_⟩ := deep_field_uses_one_original_source_typing_and_actual_safe_prefixes477 x
  exact ⟨exact_named_field_is_an_original_outer_graph_edge476 x.first,walk,safe,all⟩

theorem a_positive_deep_field_cycle_returns_to_the_actual_last_operand477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)} (x : NamedFieldTrail477 fixed q table rel outer inner wires)
    (yes : x.last.bit = true) :
    ∃ first last : Fin x.last.checkpoint.m,
      first ∈ successors (cone x.last.checkpoint.scope) x.last.checkpoint.scope.site ∧
      Path (successors (cone x.last.checkpoint.scope)) first last ∧
      classOf x.last.checkpoint.partition last = classOf x.last.checkpoint.partition x.last.checkpoint.scope.site ∧
      ∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core table m.assignment (embedded x.last.checkpoint.scope last))
          (value (environment m.assignment) .actual (x.follows.lastOperand x.first.selected.field.actualPayload)) := by
  obtain ⟨first,last,edge,trail,returns,meaning⟩ := deep_positive_field_reaches_its_own_type_in_every_same_fit477 x yes
  refine ⟨first,last,edge,trail,returns,?_⟩
  intro m fit
  have source : readAlternatives p.old.state.core table rel x.last.checkpoint.which
      x.last.checkpoint.scope x.last.checkpoint.partition = some true := by
    simpa [readCheck,x.last.actual.1,yes] using x.last.returned
  have scope : ExactCone (graphOf p.old.state.core table) x.last.checkpoint.which x.last.checkpoint.scope := by
    unfold readAlternatives at source
    split at source
    · exact (cone_replay_sound source).1
    · cases source
  simpa only [scope.1,last_checkpoint_has_its_actual_field_operand_value477 x m] using meaning m fit

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
