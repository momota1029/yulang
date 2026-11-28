import Yulang.GeneralDeclarativeI65I74NamedFieldQuotient476
import Yulang.GeneralDeclarativeI65I74FiniteCheckedObservation473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions graphOf interpretedAt readAlternatives
  actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit
  actual_safe_quotient_never_returns_to_its_own_observation_class)
open LiteralVisits473 (Checkpoint GuardedObservationInput readCheck checked_alternatives_exact_for_fixed_input_and_both_signs)
open QuotientObservation471 (ReturnsUpToEquality ConeWire Wire classOf embedded cone)
open ObservationSyntax471 (CheckedFieldBit)
open GeneralDeclarativeTermWalk322 (Walk)
open CommonRoleRegularGraph (successors)
open CommonNominalFullCarrier (Equivalent)
open FiniteWorklist (Path)

theorem named_sign_retains_actual_source_typing_in_every_fit476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) :
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt r.head.orig.code answer.selected.trace.uses :=
  located_capture_uses_one_actual_typing_walk_in_every_fit476 r answer.selected.returned

theorem positive_named_field_returns_to_its_checked_type_in_every_fit476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (known : answer.bit = true) :
    ∃ first last : Fin inner.m,
      first ∈ successors (cone inner.scope) inner.scope.site ∧
      Path (successors (cone inner.scope)) first last ∧
      classOf inner.partition last = classOf inner.partition inner.scope.site ∧
      (∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core table m.assignment (embedded inner.scope last))
          (interpretedAt p.old.state.core table m.assignment (embedded inner.scope inner.scope.site))) := by
  have seen := answer.innerCheck
  rw [known] at seen
  have actual : readAlternatives p.old.state.core table rel inner.which
      inner.scope inner.partition = some true := by
    simpa [readCheck,answer.actualInner.1] using seen
  exact actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit (p := p) actual

theorem negative_named_field_has_no_return_inside_its_checked_class476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (known : answer.bit = false) :
    ∀ first ∈ successors (cone inner.scope) inner.scope.site, ∀ last,
      Path (successors (cone inner.scope)) first last →
      classOf inner.partition last ≠ classOf inner.partition inner.scope.site := by
  have seen := answer.innerCheck
  rw [known] at seen
  have actual : readAlternatives p.old.state.core table rel inner.which
      inner.scope inner.partition = some false := by
    simpa [readCheck,answer.actualInner.1] using seen
  exact actual_safe_quotient_never_returns_to_its_own_observation_class (p := p) actual

theorem checked_named_field_has_a_finite_exact_report_when_both_cones_are_given476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Fin n}
    (selected : NamedSelection476 r q)
    (literal : q.field = fixed.label ∧ q.writtenPath = fixed.path ∧ HEq selected.field fixed.original)
    (op : atNamedCell476 table outer r.head.orig.capture.lower r.picked.raw)
    (ip : atNamedCell476 table inner selected.mark.exposure.name selected.mark.exposure.picked.raw)
    (outerInputs : GuardedObservationInput p.old.state.core table rel outer)
    (innerInputs : GuardedObservationInput p.old.state.core table rel inner)
    (safe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer) (b : Bool)
    (sign : b = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) inner) :
    ∃ (first last : Checkpoint n), first.which = outer ∧ last.which = inner ∧
      ∃ answer : NamedFieldQuotient476 fixed q table rel first last,
        readNamedFieldQuotient476 fixed q table rel first last = some answer ∧
        answer.report = ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,
          fixed.path,fixed.label,b⟩ := by
  have outerSign : false = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) outer :=
    ⟨fun nope => False.elim (Bool.false_ne_true nope),fun bad => (safe bad).elim⟩
  obtain ⟨m,k,aScope,aPartition,gotOuter⟩ :=
    (checked_alternatives_exact_for_fixed_input_and_both_signs outerInputs false).mpr outerSign
  obtain ⟨u,v,bScope,bPartition,gotInner⟩ :=
    (checked_alternatives_exact_for_fixed_input_and_both_signs innerInputs b).mpr sign
  let first : Checkpoint n := ⟨outer,m,k,aScope,aPartition⟩
  let last : Checkpoint n := ⟨inner,u,v,bScope,bPartition⟩
  have outerRead : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) first = some false := by
    simp [readCheck,first,op.1,gotOuter]
  have namedRead : readCheck p.old.state.core table rel (.logical selected.mark.exposure.name) last = some b := by
    simp [readCheck,last,ip.1,gotInner]
  let answer : NamedFieldQuotient476 fixed q table rel first last :=
    ⟨selected,literal,op,ip,outerRead,b,namedRead⟩
  exact ⟨first,last,rfl,rfl,answer,exact_named_quotient_receipt_replays476 answer,
    (exact_named_quotient_pin_and_both_bits476 answer).2.2⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
