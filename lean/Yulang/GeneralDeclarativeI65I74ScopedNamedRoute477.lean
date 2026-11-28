import Yulang.GeneralDeclarativeI65I74NamedPathTrace477
import Yulang.GeneralDeclarativeI65I74LocalNamedReification477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (Checkpoint StepWire ReadStep GuardedObservationInput independent_checkpoint_reifies_the_exact_site_and_sign
  checkpoint_does_not_substitute_a_place_or_change_its_bit written_pose_append_is_exact readCheck)

structure ScopedNamedSite477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (trace : LocatedCapture476 w.offered) (table : Positions n) where
  source : Pattern
  code : Expr
  pose : List Pose
  written : atSource r.head.orig.original pose = some source
  stamp : LocatedMark476 w.offered
  ordinal : Nat
  chosen : trace.marks[ordinal]? = some stamp
  site : Fin n
  actual : atNamedCell476 table site stamp.exposure.name stamp.exposure.picked.raw

def NamedCheckpoint477.siteData {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} (c : NamedCheckpoint477 r trace table rel) :
    ScopedNamedSite477 r trace table :=
  ⟨c.source,c.code,c.pose,c.written,c.mark,c.ordinal,c.stamped,c.checkpoint.which,c.actual⟩

structure ScopedNamedMove477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} (rel : List (Fin n × Fin n)) (current : ScopedNamedSite477 r trace table)
    (step : StepWire) where
  sourceSafe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) current.site
  read : ReadStep p.old.state.core step current.source current.code current.stamp.exposure.picked.row.right
  childStamp : LocatedMark476 w.offered
  childOrdinal : Nat
  chosen : trace.marks[childOrdinal]? = some childStamp
  path : childStamp.path = current.stamp.path ++ [oneCompiledStep477 step.action]
  rawChild : read.actualRawChild = .variable childStamp.exposure.name
  target : Fin n
  exactCell : atNamedCell476 table target childStamp.exposure.name childStamp.exposure.picked.raw
  covered : GuardedObservationInput p.old.state.core table rel target
  bit : Bool
  sign : bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) target

def ScopedNamedMove477.destination {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {current : ScopedNamedSite477 r trace table}
    {step : StepWire} (mv : ScopedNamedMove477 rel current step) : ScopedNamedSite477 r trace table :=
  ⟨mv.read.writtenChild,mv.read.childQuery,current.pose ++ step.written,
    by rw [written_pose_append_is_exact,current.written]; exact literal_occurrence mv.read.writtenFrom,
    mv.childStamp,mv.childOrdinal,mv.chosen,mv.target,mv.exactCell⟩

theorem scoped_move_produces_real_hop_and_same_literal_destination477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c : NamedCheckpoint477 r trace table rel}
    {step : StepWire} (mv : ScopedNamedMove477 rel c.siteData step) :
    ∃ wire : NamedPathStepWire477 n, wire.literal = step ∧ wire.arriveOrdinal = mv.childOrdinal ∧
      ∃ hop : NamedPathHop477 c wire, hop.endPoint.siteData = mv.destination ∧ hop.bit = mv.bit := by
  let cut : LocalNamedStep477 c step mv.childOrdinal mv.target mv.bit :=
    ⟨mv.sourceSafe,mv.read,mv.childStamp,mv.chosen,mv.path,mv.rawChild,mv.exactCell,mv.covered,mv.sign⟩
  obtain ⟨cert,site,hop,_,bit,read,stamp⟩ := local_named_step_has_a_finite_witness_at_the_very_same_site477 cut
  refine ⟨_,rfl,rfl,hop,?_,bit⟩
  change hop.next = mv.read at read
  change hop.stamp = mv.childStamp at stamp
  cases hop
  simp only [NamedCheckpoint477.siteData,NamedPathHop477.endPoint,ScopedNamedMove477.destination,
    NamedCheckpoint477.siteData] at *
  subst_vars
  rcases cert with ⟨which,m,k,scope,partition⟩
  change which = mv.target at site
  subst which
  rfl


inductive ScopedNamedRoute477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} (rel : List (Fin n × Fin n)) :
    ScopedNamedSite477 r trace table → List StepWire → ScopedNamedSite477 r trace table → Type where
  | stop (site : ScopedNamedSite477 r trace table) : ScopedNamedRoute477 rel site [] site
  | step {originSite terminalSite : ScopedNamedSite477 r trace table} {first : StepWire} {tail : List StepWire}
      (mv : ScopedNamedMove477 rel originSite first) (rest : ScopedNamedRoute477 rel mv.destination tail terminalSite) :
      ScopedNamedRoute477 rel originSite (first :: tail) terminalSite

theorem all_independent_named_moves_reify_one_finite_path_on_the_same_state477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {originSite terminalSite : ScopedNamedSite477 r trace table} {steps : List StepWire}
    (route : ScopedNamedRoute477 rel originSite steps terminalSite)
    (seed : NamedCheckpoint477 r trace table rel) (built : seed.siteData = originSite) :
    ∃ (wires : List (NamedPathStepWire477 n)) (finish : NamedCheckpoint477 r trace table rel),
      wires.map NamedPathStepWire477.literal = steps ∧ finish.siteData = terminalSite ∧
      ∃ evidence : NamedPathTrace477 seed wires finish, readNamedPathTrace477 seed wires = some ⟨finish,evidence⟩ := by
  induction route generalizing seed with
  | stop _ => exact ⟨[],seed,rfl,built,.stop seed,rfl⟩
  | step mv rest ih =>
    cases built
    obtain ⟨wire,literal,_,hop,atDest,_⟩ := scoped_move_produces_real_hop_and_same_literal_destination477 mv
    obtain ⟨ws,fin,tailActs,endpoint,tail,gathered⟩ := ih hop.endPoint atDest
    let all := NamedPathTrace477.step hop tail
    exact ⟨wire :: ws,fin,by simp [literal,tailActs],endpoint,all,finite_named_path_receipt_replays_exactly477 all⟩


def checkedHopAsScopedMove477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) : ScopedNamedMove477 rel c.siteData wire.literal :=
  let independent := existing_exact_hop_recovers_independent_coverage_and_site_sign477 hop
  ⟨independent.sourceSafe,hop.next,hop.stamp,wire.arriveOrdinal,hop.chosen,hop.path,hop.rawChild,
    wire.arriveCheck.which,hop.actual,independent.coverage,hop.bit,independent.quotientSign⟩

theorem checked_hop_has_exact_same_destination_as_independent_move477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) :
    (checkedHopAsScopedMove477 hop).destination = hop.endPoint.siteData := rfl

theorem accepted_path_reflects_the_independent_scoped_route477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {seed finish : NamedCheckpoint477 r trace table rel} {wires : List (NamedPathStepWire477 n)}
    (path : NamedPathTrace477 seed wires finish) :
    Nonempty (ScopedNamedRoute477 rel seed.siteData (wires.map NamedPathStepWire477.literal) finish.siteData) := by
  induction path with
  | stop pt => exact ⟨.stop pt.siteData⟩
  | step hop rest ih =>
    obtain ⟨tail⟩ := ih
    exact ⟨.step (checkedHopAsScopedMove477 hop) tail⟩

theorem scoped_named_route_iff_exact_finite_checkpoint_replay477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (seed : NamedCheckpoint477 r trace table rel) (endSite : ScopedNamedSite477 r trace table)
    (steps : List StepWire) :
    Nonempty (ScopedNamedRoute477 rel seed.siteData steps endSite) ↔
      ∃ (wires : List (NamedPathStepWire477 n)) (finish : NamedCheckpoint477 r trace table rel),
        wires.map NamedPathStepWire477.literal = steps ∧ finish.siteData = endSite ∧
        ∃ evidence : NamedPathTrace477 seed wires finish,
          readNamedPathTrace477 seed wires = some ⟨finish,evidence⟩ := by
  constructor
  · rintro ⟨planned⟩
    exact all_independent_named_moves_reify_one_finite_path_on_the_same_state477 planned seed rfl
  · rintro ⟨wires,finish,actions,last,replayed,_⟩
    rw [←actions,←last]
    exact accepted_path_reflects_the_independent_scoped_route477 replayed

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
