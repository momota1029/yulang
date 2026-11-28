import Yulang.GeneralDeclarativeI65I74ProducerReport479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarativeWitnessOrigins350 (Table attach Attached)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open NativeProducer465 (CheckedPhase checkPhaseOrigin)
open InputCoordinates475 (rawAt SamePhaseInputObservation478 OriginalEventFootprint478
  SourceIndexPair478 recoverOldStamps478 replayEventFootprint478 readSingletonInputBeforeCapture478
  readLocatedAtHead476)

structure AuthoredIssueData where
  manifest : Table
  references : OriginalEventFootprint478
  rootAuthorOrdinal : Nat

structure ReleasedIssueData where
  write : Write
  originOrdinal : Nat

/-- Data-only already-issued source-side reference. A matched pair in
the attached table is not by itself a compiler ownership claim. -/
def checkAuthoredRoot {n : Nat} (p : FullProblem) (pos : Positions n)
    (route : RouteWire n) (data : AuthoredIssueData) : Bool :=
  let selected := (pos.cells.get route.trail.cursor.which).oldOrdinal
  match (rawAt p).equations[selected]?,data.manifest.authored[data.rootAuthorOrdinal]? with
  | some old,some authored => decide (old = authored)
  | _,_ => false

/-- The released-output branch consults the precise existing native
address, ordinary snapshot, route, current version and grant. It does
not convert the output into an authored ordinary row. -/
def checkReleasedRoot {n : Nat} (p : FullProblem) (pos : Positions n)
    (phase : CheckedPhase p.old.state.core) (route : RouteWire n)
    (data : ReleasedIssueData) : Bool :=
  let selected := (pos.cells.get route.trail.cursor.which).oldOrdinal
  match (rawAt p).equations[selected]? with
  | some row => checkPhaseOrigin phase data.write row.left data.originOrdinal
  | none => false

def readSourceIssueAtRoute {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (route : RouteWire n) (data : AuthoredIssueData) :
    Option SamePhaseInputObservation478 := do
  if checkAuthoredRoot p pos route data then
    let _attached ← attach (rawAt p) data.manifest
    let _ ← recoverOldStamps478 ((rawAt p).equations) data.manifest.authored data.references.reads
    let answer ← readRoute p gd pos rel route
    if answer.rootArgument = data.references.argument ∧ answer.outcome.1 = data.references.originalPose
    then some answer else none
  else none

def readReleasedIssueAtRoute {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (phase : CheckedPhase p.old.state.core)
    (route : RouteWire n) (data : ReleasedIssueData) : Option SamePhaseInputObservation478 :=
  if checkReleasedRoot p pos phase route data then readRoute p gd pos rel route else none

def readOldLocatedSourceIssue {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (route : RouteWire n)
    (data : AuthoredIssueData) : Option SamePhaseInputObservation478 := do
  let attached ← attach (rawAt p) data.manifest
  match route.trail.tail with
  | [] => none
  | first :: tail =>
      replayEventFootprint478 attached gd pos rel route.trail.cursor first.2 (tail.map Prod.snd)
        data.references

end Yulang.GeneralDeclarativeI65.I72.Producer479
