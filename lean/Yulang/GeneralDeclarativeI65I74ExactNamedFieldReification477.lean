import Yulang.GeneralDeclarativeI65I74ScopedNamedRoute477
import Yulang.GeneralDeclarativeI65I74NamedFieldTrail477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (literal_occurrence)
open ObservationAlternatives473 (Positions graphOf)
open ObservationSyntax471 (CheckedFieldBit)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (Checkpoint StepWire GuardedObservationInput independent_checkpoint_reifies_the_exact_site_and_sign)

def namedSelectionSite477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {q : NamedSelectionWire476} (original : NamedSelection476 r q)
    (table : Positions n) (place : Fin n)
    (here : atNamedCell476 table place original.mark.exposure.name original.mark.exposure.picked.raw) :
    ScopedNamedSite477 r original.trace table :=
  ⟨original.field.sourcePattern,original.field.selectedQuery,q.writtenPath,
   literal_occurrence (checked_field_and_mark_retain_distinct_exact_source_positions476 original).1,
   original.mark,q.markOrdinal,original.chosen,place,here⟩

def terminalStepField477 (initial : Nat) : List StepWire → Option Nat
  | [] => some initial
  | [last] => match last.action with
    | .field label => some label
    | _ => none
  | _ :: next :: rest => terminalStepField477 initial (next :: rest)

theorem choosing_checkpoint_wires_never_changes_the_terminal_field_label477
    {n : Nat} (initial : Nat) (wires : List (NamedPathStepWire477 n)) :
    terminalFieldLabel477 initial wires = terminalStepField477 initial (wires.map (·.literal)) := by
  induction wires with
  | nil => rfl
  | cons h ws ih =>
    cases ws with
    | nil => rfl
    | cons w ws => exact ih

theorem scoped_original_field_with_independent_path_has_finite_report_for_either_sign477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (original : NamedSelection476 r q)
    (same : q.field = fixed.label ∧ q.writtenPath = fixed.path ∧ HEq original.field fixed.original)
    {root start : Fin n} (rootCell : atNamedCell476 table root r.head.orig.capture.lower r.picked.raw)
    (startCell : atNamedCell476 table start original.mark.exposure.name original.mark.exposure.picked.raw)
    (rootScope : GuardedObservationInput p.old.state.core table rel root)
    (startScope : GuardedObservationInput p.old.state.core table rel start)
    (safe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) root)
    (b0 : Bool) (class0 : b0 = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) start)
    {steps : List StepWire} {final : ScopedNamedSite477 r original.trace table}
    (route : ScopedNamedRoute477 rel (namedSelectionSite477 original table start startCell) steps final)
    {label : Nat} (field : terminalStepField477 fixed.label steps = some label)
    (b : Bool) (classified : b = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) final.site) :
    ∃ (outer inner : Checkpoint n) (wires : List (NamedPathStepWire477 n)),
      outer.which = root ∧ inner.which = start ∧ wires.map (·.literal) = steps ∧
      ∃ response : NamedFieldTrail477 fixed q table rel outer inner wires,
        readNamedFieldTrail477 fixed q table rel outer inner wires = some response ∧
        response.report = ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,final.pose,label,b⟩ := by
  have dead : false = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) root :=
    ⟨fun impossible => False.elim (Bool.false_ne_true impossible),fun cyc => False.elim (safe cyc)⟩
  obtain ⟨outer,o,checkedOuter⟩ := independent_checkpoint_reifies_the_exact_site_and_sign rootScope false dead
  obtain ⟨inner,i,checkedInner⟩ := independent_checkpoint_reifies_the_exact_site_and_sign startScope b0 class0
  rw [rootCell.1] at checkedOuter
  rw [startCell.1] at checkedInner
  let beginning : NamedFieldQuotient476 fixed q table rel outer inner :=
    ⟨original,same,o.symm ▸ rootCell,i.symm ▸ startCell,checkedOuter,b0,checkedInner⟩
  have agree : (firstNamedCheckpoint477 beginning).siteData =
      namedSelectionSite477 original table start startCell := by
    rcases inner with ⟨which,m,k,scope,part⟩
    change which = start at i
    subst which
    rfl
  obtain ⟨wires,finish,stepsMatch,last,path,_⟩ :=
    all_independent_named_moves_reify_one_finite_path_on_the_same_state477 route
      (firstNamedCheckpoint477 beginning) agree
  have labelOk : terminalFieldLabel477 fixed.label wires = some label := by
    rw [choosing_checkpoint_wires_never_changes_the_terminal_field_label477,stepsMatch]
    exact field
  let result : NamedFieldTrail477 fixed q table rel outer inner wires :=
    ⟨beginning,finish,path,label,labelOk⟩
  refine ⟨outer,inner,wires,o,i,stepsMatch,result,
    named_field_trail_replays_without_replacing_initial_source_or_final_site477 result,?_⟩
  have pose : finish.pose = final.pose := congrArg ScopedNamedSite477.pose last
  have pos : finish.checkpoint.which = final.site := congrArg ScopedNamedSite477.site last
  have returned := (named_checkpoint_carries_exact_written_raw_and_author_occurrences477 finish).2.2.2
  rw [pos] at returned
  have sameBit : finish.bit = b := by
    cases h1 : finish.bit <;> cases h2 : b
    · rfl
    · exact False.elim (Bool.false_ne_true (h1.symm.trans (returned.mpr (classified.mp h2))))
    · exact False.elim (Bool.false_ne_true (h2.symm.trans (classified.mpr (returned.mp h1))))
    · rfl
  simp [NamedFieldTrail477.report,result,pose,sameBit]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
