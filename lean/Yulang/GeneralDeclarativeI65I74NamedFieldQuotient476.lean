import Yulang.GeneralDeclarativeI65I74FixedNamedSourceChoice476
import Yulang.GeneralDeclarativeI65I74TypedConeQuotientSound474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions Place oldPosition graphOf readAlternatives interpretedAt)
open LiteralVisits473 (Checkpoint readCheck checkpoint_does_not_substitute_a_place_or_change_its_bit)
open QuotientObservation471 (ReturnsUpToEquality)
open ObservationSyntax471 (CheckedFieldBit)

def atNamedCell476 (p : Positions n) (site : Fin n) (name ordinal : Nat) : Prop :=
  oldPosition p site = .logical name ∧ (p.cells.get site).oldOrdinal = ordinal

def atNamedCellTest476 (p : Positions n) (site : Fin n) (name ordinal : Nat) : Bool :=
  decide (oldPosition p site = .logical name ∧ (p.cells.get site).oldOrdinal = ordinal)

theorem exact_named_cell_test476 (p : Positions n) (site : Fin n) (name ordinal : Nat) :
    atNamedCellTest476 p site name ordinal = true ↔ atNamedCell476 p site name ordinal := by
  simp [atNamedCellTest476,atNamedCell476]

/-- A single actual immediate field whose source typing opened an
existing named row. An independent quotient cone is still required
for both the actual outer point and the selected field. -/
structure NamedFieldQuotient476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n) where
  selected : NamedSelection476 r q
  literalChoice : q.field = fixed.label ∧ q.writtenPath = fixed.path ∧ HEq selected.field fixed.original
  actualOuter : atNamedCell476 table outer.which r.head.orig.capture.lower r.picked.raw
  actualInner : atNamedCell476 table inner.which selected.mark.exposure.name selected.mark.exposure.picked.raw
  prefixSafe : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer = some false
  bit : Bool
  innerCheck : readCheck p.old.state.core table rel (.logical selected.mark.exposure.name) inner = some bit

def readNamedFieldQuotient476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n) :
    Option (NamedFieldQuotient476 fixed q table rel outer inner) :=
  match readSource : readNamedAtFixedChoice476 fixed q with
  | none => none
  | some selected =>
    if outerCell : atNamedCellTest476 table outer.which r.head.orig.capture.lower r.picked.raw = true then
      if innerCell : atNamedCellTest476 table inner.which selected.mark.exposure.name selected.mark.exposure.picked.raw = true then
        if outerSafe : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer = some false then
          match check : readCheck p.old.state.core table rel (.logical selected.mark.exposure.name) inner with
          | none => none
          | some b =>
            some ⟨selected,(fixed_named_join_is_exact_same_literal_field_receipt476 fixed q selected).mp readSource,
              (exact_named_cell_test476 ..).mp outerCell,(exact_named_cell_test476 ..).mp innerCell,outerSafe,b,check⟩
        else none
      else none
    else none

def NamedFieldQuotient476.report {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) : CheckedFieldBit :=
  ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,q.writtenPath,q.field,answer.bit⟩

theorem exact_named_quotient_receipt_replays476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) :
    readNamedFieldQuotient476 fixed q table rel outer inner = some answer := by
  rcases answer with ⟨selected,literal,oc,ic,safe,bit,hit⟩
  have select := (fixed_named_join_is_exact_same_literal_field_receipt476 fixed q selected).mpr literal
  have outerCell := (exact_named_cell_test476 ..).mpr oc
  have innerCell := (exact_named_cell_test476 ..).mpr ic
  unfold readNamedFieldQuotient476
  split
  · rename_i gone
    rw [select] at gone
    contradiction
  · rename_i seen read
    have same := Option.some.inj (read.symm.trans select)
    subst seen
    simp only [outerCell,innerCell,safe,dite_true]
    split
    · rename_i gone
      rw [hit] at gone
      contradiction
    · rename_i b actual
      have same := Option.some.inj (actual.symm.trans hit)
      subst b
      rfl

theorem exact_named_quotient_pin_and_both_bits476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) :
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer.which ∧
    (answer.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) inner.which) ∧
    answer.report = ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,
      fixed.path,fixed.label,answer.bit⟩ := by
  refine ⟨?_,(checkpoint_does_not_substitute_a_place_or_change_its_bit answer.innerCheck).2,?_⟩
  · exact fun bad => Bool.false_ne_true
      ((checkpoint_does_not_substitute_a_place_or_change_its_bit answer.prefixSafe).2.mpr bad)
  · simp [NamedFieldQuotient476.report,answer.literalChoice.1,answer.literalChoice.2.1]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
