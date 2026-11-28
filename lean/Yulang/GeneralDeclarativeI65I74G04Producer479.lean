import Yulang.GeneralDeclarativeI65I74ProducerIssue479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (StepWire)
open InputCoordinates475 (SamePhaseInputObservation478 rawAt StampedRead SourceIndexPair478
  FirstIs recoverOldStamps478)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

/-- The old ordinary support owner is a number, not a native stamp.
A completion-side association has to retain all of these fields.
Neither equal targets nor an independently released write recover it. -/
structure CompletedAssociation where
  supportOwner : Nat
  rawOrdinal : Nat
  row : Equation
  write : Write
  originOrdinal : Nat
  deriving DecidableEq

/-- Prior, separately authenticated phase evidence. This module does
not populate this ledger or reinterpret a released output as source.
The existing exact order of authored rows is retained. -/
structure PriorPhase where
  authors : Table
  completed : List CompletedAssociation
  /-- An optional pre-erasure ordering recorded by the actual input
  stage. Different equal equations do not identify these positions. -/
  recordedReads : Option (List SourceIndexPair478)

def PriorPhase.ExactFor {n p gd} {pos : Positions n} {rel}
    (basis : PriorPhase) (e : TypedInput p gd pos rel) : Prop :=
  match e.backing with
  | .source _ =>
    Nonempty (Attached (rawAt p) basis.authors) ∧
    (∀ row, row ∈ basis.authors.authored ↔ e.support.derivesFrom row .source) ∧
    Read ⟨(rawAt p).normal,basis.authors.authored⟩ .actual
      (.variable e.head.orig.capture.lower) e.head.orig.code e.uses ∧
    (∀ chosen, basis.recordedReads = some chosen →
      ∃ rows : List StampedRead,
        recoverOldStamps478 (rawAt p).equations basis.authors.authored chosen = some rows ∧
        (∃ start, FirstIs e.head.orig.capture.lower rows start ∧ start.raw = e.rawOrdinal) ∧
        Read ⟨(rawAt p).normal,rows.map StampedRead.row⟩ .actual
          (.variable e.head.orig.capture.lower) e.head.orig.code e.uses)
  | .released owner _ write original _ _ _ =>
    ⟨owner,e.rawOrdinal,e.rootRow,write,original⟩ ∈ basis.completed

inductive IssuePayload where
  | authored (input : AuthoredIssueData)
  | released (input : ReleasedIssueData)

structure InputInspectionWire (n : Nat) where
  route : RouteWire n
  payload : IssuePayload

def ExactSelectedRoute {n p gd} {pos : Positions n} {rel}
    (e : TypedInput p gd pos rel) (w : RouteWire n) : Prop :=
  w.argument = e.head.orig.location.headArgument ∧
  w.declarationOrdinal = e.declarationOrdinal ∧
  w.trail.cursor.which = e.root.index ∧
  w.trail.tail.map Prod.fst = ⟨.field e.firstLabel,e.firstPose⟩ :: e.tail ∧
  w.trail.tail.map (fun h => h.2.which) = e.first.index :: e.tailPoints

/-- The emitted ordered indices must actually drive the independent
typing event, rather than checking an unused list of valid pairs. A
recorded pre-erasure selection is kept exactly when available. -/
def AuthoredRunRetained {n p gd} {pos : Positions n} {rel}
    (basis : PriorPhase) (e : TypedInput p gd pos rel)
    (data : AuthoredIssueData) : Prop :=
  (∀ selected, basis.recordedReads = some selected → data.references.reads = selected) ∧
  ∃ rows : List StampedRead,
    recoverOldStamps478 (rawAt p).equations basis.authors.authored data.references.reads = some rows ∧
    (∃ start, FirstIs e.head.orig.capture.lower rows start ∧
      start.raw = e.rawOrdinal ∧ start.author = data.rootAuthorOrdinal) ∧
    Read ⟨(rawAt p).normal,rows.map StampedRead.row⟩ .actual
      (.variable e.head.orig.capture.lower) e.head.orig.code e.uses

def IssueIsFaithful {n p gd} {pos : Positions n} {rel}
    (basis : PriorPhase) (e : TypedInput p gd pos rel) (w : InputInspectionWire n) : Prop :=
  ExactSelectedRoute e w.route ∧
  match e.backing,w.payload with
  | .source _,.authored data =>
      data.manifest = basis.authors ∧
      data.references.argument = e.report.rootArgument ∧
      data.references.originalPose = e.report.outcome.1 ∧
      basis.authors.authored[data.rootAuthorOrdinal]? = some e.rootRow ∧
      AuthoredRunRetained basis e data ∧
      readSourceIssueAtRoute p gd pos rel w.route data = some e.report
  | .released owner phase write original _ _ _,.released data =>
      data.write = write ∧ data.originOrdinal = original ∧
      ⟨owner,e.rawOrdinal,e.rootRow,data.write,data.originOrdinal⟩ ∈ basis.completed ∧
      readReleasedIssueAtRoute p gd pos rel phase w.route data = some e.report
  | _,_ => False

/-- A future input-stage producer must retain data at the original typed
event, before comparing or dropping source paths and old row positions.
The current compiler is not asserted to implement this operation. -/
abbrev InputPhaseEmission :=
  ∀ (n : Nat) (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (relations : List (Fin n × Fin n)),
    PriorPhase → TypedInput p gd positions relations → Option (InputInspectionWire n)

/-- The open G04 producer obligation. The domain is the independent
typed input event, not the existence of a successful report or a
previously attached candidate wire. The already selected source
observation and all old physical positions are preserved verbatim.
The authored branch has original source-only input support. The
release branch is relative to a separately linked completion;
it cannot supply its own grant, version or completed association. -/
def G04Producer : Prop :=
  ∃ emit : InputPhaseEmission,
    ∀ (n : Nat) (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
      (positions : Positions n) (relations : List (Fin n × Fin n))
      (basis : PriorPhase) (event : TypedInput p gd positions relations),
      basis.ExactFor event →
      ∃ wire, emit n p gd positions relations basis event = some wire ∧
        IssueIsFaithful basis event wire

theorem named_producer_premise_supplies_an_issued_exact_report479
    (producer : G04Producer)
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {relations}
    (basis : PriorPhase) (event : TypedInput p gd pos relations)
    (valid : basis.ExactFor event) :
    ∃ (emit : InputPhaseEmission) (wire : InputInspectionWire n),
      emit n p gd pos relations basis event = some wire ∧
      IssueIsFaithful basis event wire := by
  obtain ⟨emit,emitOkay⟩ := producer
  obtain ⟨wire,run,faithful⟩ := emitOkay n p gd pos relations basis event valid
  exact ⟨emit,wire,run,faithful⟩

end Yulang.GeneralDeclarativeI65.I72.Producer479
