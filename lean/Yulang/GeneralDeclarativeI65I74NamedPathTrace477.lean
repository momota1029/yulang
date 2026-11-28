import Yulang.GeneralDeclarativeI65I74NamedPathHop477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource)
open LiteralVisits473 (Checkpoint)
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open FiniteWorklist (Path)

inductive NamedPathTrace477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} :
    NamedCheckpoint477 r trace table rel → List (NamedPathStepWire477 n) →
    NamedCheckpoint477 r trace table rel → Type where
  | stop (point : NamedCheckpoint477 r trace table rel) : NamedPathTrace477 point [] point
  | step {c d : NamedCheckpoint477 r trace table rel} {w : NamedPathStepWire477 n}
      {ws : List (NamedPathStepWire477 n)} (hop : NamedPathHop477 c w)
      (rest : NamedPathTrace477 hop.endPoint ws d) : NamedPathTrace477 c (w :: ws) d

def readNamedPathTrace477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} (c : NamedCheckpoint477 r trace table rel) :
    (ws : List (NamedPathStepWire477 n)) →
    Option (Σ d : NamedCheckpoint477 r trace table rel, NamedPathTrace477 c ws d)
  | [] => some ⟨c,.stop c⟩
  | wire :: rest => do
      let hop ← readNamedPathHop477 c wire
      let tail ← readNamedPathTrace477 hop.endPoint rest
      pure ⟨tail.1,.step hop tail.2⟩

theorem finite_named_path_receipt_replays_exactly477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) :
    readNamedPathTrace477 c ws = some ⟨d,xs⟩ := by
  induction xs with
  | stop => rfl
  | step hop xs ih =>
    simp [readNamedPathTrace477,named_path_hop_has_exact_replay477 hop,ih]

theorem finite_named_path_reader_is_exact477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} (c : NamedCheckpoint477 r trace table rel)
    (ws : List (NamedPathStepWire477 n)) :
    (readNamedPathTrace477 c ws).isSome = true ↔
      Nonempty (Σ d : NamedCheckpoint477 r trace table rel, NamedPathTrace477 c ws d) := by
  constructor
  · cases h : readNamedPathTrace477 c ws with
    | none => simp
    | some got => exact fun _ => ⟨got⟩
  · rintro ⟨⟨d,proof⟩⟩
    simp [finite_named_path_receipt_replays_exactly477 proof]

def NamedPathTrace477.prefixPoints {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) : List (Fin n) :=
  match xs with
  | .stop _ => []
  | .step _ tail => c.checkpoint.which :: tail.prefixPoints

theorem finite_named_path_points_are_all_safe_before_terminal477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) :
    Path (successors (graphOf p.old.state.core table)) c.checkpoint.which d.checkpoint.which ∧
    (∀ pt ∈ xs.prefixPoints, ¬ ReturnsUpToEquality (graphOf p.old.state.core table) pt) ∧
    (d.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) d.checkpoint.which) := by
  induction xs with
  | stop point =>
    exact ⟨.nil _,by simp [NamedPathTrace477.prefixPoints],
      (named_checkpoint_carries_exact_written_raw_and_author_occurrences477 point).2.2.2⟩
  | step hop tail ih =>
    obtain ⟨edge,safe⟩ := named_path_hop_has_real_edge_and_safe_source477 hop
    refine ⟨.cons edge ih.1,?_,ih.2.2⟩
    intro pt present
    simp only [NamedPathTrace477.prefixPoints,List.mem_cons] at present
    rcases present with same | later
    · exact same ▸ safe
    · exact ih.2.1 pt later

theorem finite_named_path_retains_original_written_and_compiled_addresses477 {n : Nat}
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) :
    d.pose = c.pose ++ (ws.flatMap fun wire => wire.literal.written) ∧
    d.mark.path = c.mark.path ++ (ws.map fun wire => oneCompiledStep477 wire.literal.action) ∧
    atSource r.head.orig.original d.pose = some d.source := by
  induction xs with
  | stop point => simp [point.written]
  | step hop tail ih =>
    refine ⟨?_,?_,ih.2.2⟩
    · simp [ih.1,NamedPathHop477.endPoint,List.append_assoc]
    · simp only [ih.2.1,NamedPathHop477.endPoint,hop.path,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
