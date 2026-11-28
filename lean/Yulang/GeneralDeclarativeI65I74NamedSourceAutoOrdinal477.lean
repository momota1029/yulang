import Yulang.GeneralDeclarativeI65I74LocatedUniqueOrdinal477
import Yulang.GeneralDeclarativeI65I74NamedFieldWitness476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

def readNamedSourceWithoutOrdinal477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) :
    Option ((i : Nat) × NamedSelection476 r ⟨fixed.label,fixed.path,i⟩) := do
  let trace ← readLocatedAtHead476 r
  let index ← exactMarkOrdinal477 [.field fixed.label] trace
  let selected ← readNamedAtFixedChoice476 fixed ⟨fixed.label,fixed.path,index⟩
  pure ⟨index,selected⟩

theorem exact_source_selection_needs_no_supplied_ordinal477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (i : Nat) (selected : NamedSelection476 r ⟨fixed.label,fixed.path,i⟩)
    (accepted : readNamedAtFixedChoice476 fixed ⟨fixed.label,fixed.path,i⟩ = some selected) :
    readNamedSourceWithoutOrdinal477 fixed = some ⟨i,selected⟩ := by
  have unique := actual_head_capture_has_unique_compiled_paths477 r selected.returned
  have idx := literal_ordinal_lookup_replays_every_existing_mark477 unique selected.chosen selected.selectedPath
  simp [readNamedSourceWithoutOrdinal477,selected.returned,idx,accepted]

def readImmediateNamedQuotientWithoutOrdinal477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n) :
    Option ((i : Nat) × NamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer inner) := do
  let source ← readNamedSourceWithoutOrdinal477 fixed
  let result ← readNamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,source.1⟩ table rel outer inner
  pure ⟨source.1,result⟩

theorem exact_named_quotient_needs_no_supplied_ordinal477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {i : Nat} (result : NamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer inner)
    (accepted : readNamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer inner =
      some result) :
    readImmediateNamedQuotientWithoutOrdinal477 fixed table rel outer inner = some ⟨i,result⟩ := by
  have source := (fixed_named_join_is_exact_same_literal_field_receipt476 fixed _ result.selected).mpr result.literalChoice
  have lookup := exact_source_selection_needs_no_supplied_ordinal477 fixed i result.selected source
  simp [readImmediateNamedQuotientWithoutOrdinal477,lookup,accepted]

theorem absent_source_path_still_yields_no_quotient477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    {trace : LocatedCapture476 w.offered}
    (ok : readLocatedAtHead476 r = some trace)
    (absent : ∀ m ∈ trace.marks, m.path ≠ [.field fixed.label])
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n) :
    readImmediateNamedQuotientWithoutOrdinal477 fixed table rel outer inner = none := by
  have miss := no_captured_ordinal_exactly_when_path_not_opened477.mpr absent
  simp [readImmediateNamedQuotientWithoutOrdinal477,readNamedSourceWithoutOrdinal477,ok,miss]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

