import Yulang.GeneralDeclarativeI65I74LocatedUniqueOrdinal477
import Yulang.GeneralDeclarativeI65I74NamedPathHop477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint StepWire)

def chooseNamedHopOrdinal477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (step : StepWire) (check : Checkpoint n) :
    Option (NamedPathStepWire477 n) := do
  let i ← exactMarkOrdinal477 (c.mark.path ++ [oneCompiledStep477 step.action]) trace
  pure ⟨step,i,check⟩

def readNamedHopWithoutOrdinal477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (step : StepWire) (check : Checkpoint n) :
    Option ((wire : NamedPathStepWire477 n) × NamedPathHop477 c wire) := do
  let w ← chooseNamedHopOrdinal477 c step check
  let out ← readNamedPathHop477 c w
  pure ⟨w,out⟩

theorem ordinal_lookup_preserves_exact_checked_hop477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    (executed : readLocatedAtHead476 r = some trace)
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) :
    readNamedHopWithoutOrdinal477 c wire.literal wire.arriveCheck = some ⟨wire,hop⟩ := by
  have paths := actual_head_capture_has_unique_compiled_paths477 r executed
  have h := literal_ordinal_lookup_replays_every_existing_mark477 paths hop.chosen hop.path
  obtain ⟨step,ordinal,check⟩ := wire
  change exactMarkOrdinal477 (c.mark.path++[oneCompiledStep477 step.action]) trace = some ordinal at h
  simp only [readNamedHopWithoutOrdinal477,chooseNamedHopOrdinal477,h,bind,Option.bind,pure,
    named_path_hop_has_exact_replay477 hop]

theorem absent_exact_deep_mark_still_prevents_hop477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (step : StepWire) (check : Checkpoint n)
    (absent : ∀ m ∈ trace.marks, m.path ≠ c.mark.path ++ [oneCompiledStep477 step.action]) :
    readNamedHopWithoutOrdinal477 c step check = none := by
  have miss := no_captured_ordinal_exactly_when_path_not_opened477.mpr absent
  simp [readNamedHopWithoutOrdinal477,chooseNamedHopOrdinal477,miss]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

