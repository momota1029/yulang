import Yulang.GeneralDeclarativeI65I74IndexedBeforeCapture478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

theorem a_real_singleton_head_has_literal_visible_ordinal_zero478
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (read : BeforeCapture a gd w) : w.source.visibleOrdinal = 0 := by
  have actual := read.head.orig.actualVisible
  rw [read.address] at actual
  obtain ⟨bounded,_⟩ := List.getElem?_eq_some_iff.mp actual
  rw [read.visibleOnce] at bounded
  omega

def readSingletonInputBeforeCapture478 {p : FullProblem} {t : Table} (a : Attached (rawAt p) t)
    (gd : CheckedTable p.old.state.core.current) (argument : Nat) (rows : List SourceIndexPair478) :
    Option (Σ original : BeforeCaptureWire, BeforeCapture a gd original) :=
  readIndexedBeforeCapture478 a gd ⟨⟨0,argument⟩,rows⟩

theorem exact_accepted_input_needs_neither_frame_nor_visible_ordinal_as_data478
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (read : BeforeCapture a gd w) :
    readSingletonInputBeforeCapture478 a gd w.source.headArgument
        (w.offered.map StampedRead.indexPair478) = some ⟨w,read⟩ := by
  have zero := a_real_singleton_head_has_literal_visible_ordinal_zero478 read
  have source : (⟨0,w.source.headArgument⟩ : PreparedDeclarations463.HeadAddress) = w.source := by
    cases h : w.source with
    | mk visible argument =>
      simp only [h] at zero
      exact congrArg (fun k => (⟨k,argument⟩ : PreparedDeclarations463.HeadAddress)) zero.symm
  unfold readSingletonInputBeforeCapture478
  rw [source]
  exact recovering_from_exact_input_indices_keeps_frame_and_actual_capture478 read

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
