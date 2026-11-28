import Yulang.GeneralDeclarativeI65I74MixedLiteralHop477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationAlternatives473 (Positions graphOf)
open LiteralVisits473 (Checkpoint StepWire checkpoint_does_not_substitute_a_place_or_change_its_bit)
open QuotientObservation471 (ReturnsUpToEquality)
open FiniteWorklist (Path)
open CommonRoleRegularGraph (successors)

inductive MixedTrail477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    (trace : LocatedCapture476 w.offered) :
    MixedPoint477 r table rel → List (StepWire × Checkpoint n) → MixedPoint477 r table rel → Prop
  | stop : MixedTrail477 trace c [] c
  | step (first : MixedArrival477 trace c wire next)
      (rest : MixedTrail477 trace first.finish tail final) :
      MixedTrail477 trace c ((wire,next)::tail) final

def readMixedTrail477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    (trace : LocatedCapture476 w.offered) (start : MixedPoint477 r table rel)
    (wires : List (StepWire × Checkpoint n)) :
    Option {last : MixedPoint477 r table rel // MixedTrail477 trace start wires last} :=
  match wires with
  | [] => some ⟨start,.stop⟩
  | (wire,next)::rest => do
    let hop ← readMixedArrival477 trace start wire next
    let last ← readMixedTrail477 trace hop.finish rest
    pure ⟨last.1,.step hop last.2⟩
termination_by wires.length

theorem verified_mixed_trail_replays_to_same_exact_finish477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {start last : MixedPoint477 r table rel} {wires}
    (ran : readLocatedAtHead476 r = some trace)
    (proof : MixedTrail477 trace start wires last) :
    readMixedTrail477 trace start wires = some ⟨last,proof⟩ := by
  induction proof with
  | stop => rw [readMixedTrail477]
  | @step c wire next tail final first rest ih =>
    obtain ⟨hop,seen,_,_,_,equal⟩ := mixed_arrival_replays_its_checked_bit477 ran first
    rw [readMixedTrail477]
    simp only [seen,bind,Option.bind]
    -- Map the induction hypothesis on the endpoint indices, not on
    -- a new interpretation of either origin evidence.
    have replayNamedFinish :
        (readMixedTrail477 trace hop.finish tail).map Subtype.val = some final := by
      rw [equal,ih]
      rfl
    cases ranTail : readMixedTrail477 trace hop.finish tail with
    | none => simp [ranTail] at replayNamedFinish
    | some out =>
      have index : out.1 = final := by simpa [ranTail] using replayNamedFinish
      rcases out with ⟨done,ok⟩
      dsimp only at index
      subst done
      rfl

theorem mixed_trail_keeps_both_paths_and_terminal_is_exact477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {start last : MixedPoint477 r table rel} {wires}
    (proof : MixedTrail477 trace start wires last) :
    last.pose = start.pose ++ wires.flatMap (fun x => x.1.written) ∧
    last.compiled = start.compiled ++ wires.map (fun x => oneCompiledStep477 x.1.action) ∧
    (last.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) last.checkpoint.which) := by
  induction proof with
  | @stop c =>
    exact ⟨by simp,by simp,(checkpoint_does_not_substitute_a_place_or_change_its_bit c.checked).2⟩
  | step hop rest ih =>
    have one := checked_mixed_hop_keeps_compiled_and_original_paths477 hop
    refine ⟨?_,?_,ih.2.2⟩
    · rw [ih.1,one.1]
      simp [List.append_assoc]
    · rw [ih.2.1,one.2.1]
      simp [List.append_assoc]

inductive SafeEdgeTrail477 {ι : Type} (adjacent : ι → List ι) (cycle : ι → Prop) :
    ι → List ι → ι → Prop
  | stop : SafeEdgeTrail477 adjacent cycle i [] i
  | step : j ∈ adjacent i → ¬cycle i → SafeEdgeTrail477 adjacent cycle j rest k →
      SafeEdgeTrail477 adjacent cycle i (j::rest) k

theorem mixed_trail_contains_actual_edges_and_only_safe_proper_prefixes477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {start last : MixedPoint477 r table rel} {wires}
    (proof : MixedTrail477 trace start wires last) :
    SafeEdgeTrail477 (successors (graphOf p.old.state.core table))
      (ReturnsUpToEquality (graphOf p.old.state.core table))
      start.checkpoint.which (wires.map fun x => x.2.which) last.checkpoint.which := by
  induction proof with
  | stop => exact .stop
  | step hop tail ih =>
    obtain ⟨edge,safe⟩ := mixed_arrival_is_exact_edge_and_source_is_safe477 hop
    exact .step edge safe ih

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

