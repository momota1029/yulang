import Yulang.GeneralDeclarativeI65I74NamedPathHop477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions graphOf readAlternatives)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (Checkpoint StepWire ReadStep GuardedObservationInput independent_checkpoint_reifies_the_exact_site_and_sign
  accepted_observation_yields_all_input_guards readCheck checkpoint_does_not_substitute_a_place_or_change_its_bit)

structure LocalNamedStep477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (literal : StepWire) (i : Nat) (point : Fin n) (bit : Bool) where
  sourceSafe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) c.checkpoint.which
  next : ReadStep p.old.state.core literal c.source c.code c.mark.exposure.picked.row.right
  stamp : LocatedMark476 w.offered
  chosen : trace.marks[i]? = some stamp
  path : stamp.path = c.mark.path ++ [oneCompiledStep477 literal.action]
  actualRaw : next.actualRawChild = .variable stamp.exposure.name
  actualCell : atNamedCell476 table point stamp.exposure.name stamp.exposure.picked.raw
  coverage : GuardedObservationInput p.old.state.core table rel point
  quotientSign : bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) point

theorem local_named_step_has_a_finite_witness_at_the_very_same_site477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c : NamedCheckpoint477 r trace table rel}
    {literal : StepWire} {i : Nat} {point : Fin n} {bit : Bool}
    (rule : LocalNamedStep477 c literal i point bit) :
    ∃ checkpoint : Checkpoint n, checkpoint.which = point ∧
      ∃ hop : NamedPathHop477 c ⟨literal,i,checkpoint⟩,
        readNamedPathHop477 c ⟨literal,i,checkpoint⟩ = some hop ∧
        hop.bit = bit ∧ hop.next = rule.next ∧ hop.stamp = rule.stamp := by
  obtain ⟨checkpoint,site,returned⟩ :=
    independent_checkpoint_reifies_the_exact_site_and_sign rule.coverage bit rule.quotientSign
  have no : c.bit = false := by
    cases b : c.bit
    · rfl
    · exact False.elim (rule.sourceSafe ((checkpoint_does_not_substitute_a_place_or_change_its_bit c.returned).2.mp b))
  have h : readCheck p.old.state.core table rel (.logical rule.stamp.exposure.name) checkpoint = some bit := by
    rw [rule.actualCell.1] at returned
    exact returned
  let witness : NamedPathHop477 c ⟨literal,i,checkpoint⟩ :=
    ⟨no,rule.next,rule.stamp,rule.chosen,rule.path,rule.actualRaw,site.symm ▸ rule.actualCell,bit,h⟩
  exact ⟨checkpoint,site,witness,named_path_hop_has_exact_replay477 witness,rfl,rfl,rfl⟩

def existing_exact_hop_recovers_independent_coverage_and_site_sign477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c : NamedCheckpoint477 r trace table rel}
    {wire : NamedPathStepWire477 n} (hop : NamedPathHop477 c wire) :
    LocalNamedStep477 c wire.literal wire.arriveOrdinal wire.arriveCheck.which hop.bit := by
  have got : readAlternatives p.old.state.core table rel wire.arriveCheck.which
       wire.arriveCheck.scope wire.arriveCheck.partition = some hop.bit := by
    simpa [readCheck,hop.actual.1] using hop.hit
  exact ⟨(named_path_hop_has_real_edge_and_safe_source477 hop).2,
    hop.next,hop.stamp,hop.chosen,hop.path,hop.rawChild,hop.actual,
    accepted_observation_yields_all_input_guards got,
    (checkpoint_does_not_substitute_a_place_or_change_its_bit hop.hit).2⟩

theorem exactly_the_local_independent_rule_has_a_finite_hop477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c : NamedCheckpoint477 r trace table rel}
    (literal : StepWire) (ordinal : Nat) (point : Fin n) (bit : Bool) :
    (∃ checkpoint : Checkpoint n, checkpoint.which = point ∧
      ∃ hop : NamedPathHop477 c ⟨literal,ordinal,checkpoint⟩,
        readNamedPathHop477 c ⟨literal,ordinal,checkpoint⟩ = some hop ∧ hop.bit = bit) ↔
    Nonempty (LocalNamedStep477 c literal ordinal point bit) := by
  constructor
  · rintro ⟨checkpoint,site,hop,_,sign⟩
    rw [←site,←sign]
    exact ⟨existing_exact_hop_recovers_independent_coverage_and_site_sign477 hop⟩
  · rintro ⟨cut⟩
    obtain ⟨checkpoint,site,hop,read,sign,_,_⟩ := local_named_step_has_a_finite_witness_at_the_very_same_site477 cut
    exact ⟨checkpoint,site,hop,read,sign⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
