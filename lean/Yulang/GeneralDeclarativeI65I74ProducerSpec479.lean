import Yulang.GeneralDeclarativeI65I74EventFootprintSound478
import Yulang.GeneralDeclarativeI65I74LiteralVisitCoordinates473
import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open NativeProducer465 (CheckedPhase PhaseOriginAt)
open ObservationAlternatives473 (Positions oldPosition graphOf readTermAt anchorFor)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open WrittenPattern460.PhysicalOrigin (Pose)
open LiteralVisits473 (ReadStep StepWire childSlot GuardedObservationInput)
open InputCoordinates475 (rawAt registryAt SafeEdgeTrail477 oneCompiledStep477 SamePhaseInputObservation478)

/-- A semantic path point reads existing ordinary data. The typed query and
its original pattern are separate from the raw term at the observation. -/
structure Site {n : Nat} (s : GeneralDeclarativeI65.State) (positions : Positions n) where
  index : Fin n
  pattern : Pattern
  query : Expr
  term : Expr
  exactTerm : readTermAt s positions index = some term

/-- An original written action at a selected coordinate, without a supplied
checkpoint, capture packet, or answer from the executable report reader. -/
structure Hop {n : Nat} {s : GeneralDeclarativeI65.State} {positions : Positions n}
    (left right : Site s positions) (step : StepWire) where
  typed : ReadStep s step left.pattern left.query left.term
  written : typed.writtenChild = right.pattern
  query : typed.childQuery = right.query
  position : anchorFor (positions.cells.get left.index) (childSlot step.action)
    typed.actualRawChild = oldPosition positions right.index
  edge : right.index ∈ successors (graphOf s positions) left.index

/-- All proper prefixes are safe in the same quotient. A terminal bit is
about its own equivalence class, not reachability of some other class. -/
inductive Trail {n : Nat} (s : GeneralDeclarativeI65.State) (positions : Positions n)
    (rel : List (Fin n × Fin n)) :
    Site s positions → List StepWire → List (Fin n) → Site s positions → Bool → Prop where
  | stop {here bit} :
      GuardedObservationInput s positions rel here.index →
      (bit = true ↔ ReturnsUpToEquality (graphOf s positions) here.index) →
      Trail s positions rel here [] [] here bit
  | step {here next finish move moves indices bit} :
      Hop here next move →
      GuardedObservationInput s positions rel here.index →
      (¬ ReturnsUpToEquality (graphOf s positions) here.index) →
      Trail s positions rel next moves indices finish bit →
      Trail s positions rel here (move :: moves) (next.index :: indices) finish bit

theorem declarative_trail_reads_existing_edges_and_returns_at_the_terminal479
    {s : GeneralDeclarativeI65.State} {positions : Positions n} {rel} {first moves indices final bit}
    (path : Trail s positions rel first moves indices final bit) :
    SafeEdgeTrail477 (successors (graphOf s positions)) (ReturnsUpToEquality (graphOf s positions))
      first.index indices final.index ∧
    (bit = true ↔ ReturnsUpToEquality (graphOf s positions) final.index) := by
  induction path with
  | stop _ sign => exact ⟨.stop,sign⟩
  | step hop _ safe _ ih => exact ⟨.step hop.edge safe ih.1,ih.2⟩

/-- The two sources of authority are kept distinct. In particular, an
output support is not an authored row and its release is checked at an
existing native address with the exact same ordinary snapshot. -/
inductive Backing (p : FullProblem) {settled : Nat → Prop}
    (support : Supported (rawAt p) settled) (row : Equation) : Type where
  | source : support.derivesFrom row .source → Backing p support row
  | released (owner : Nat) (phase : CheckedPhase p.old.state.core)
      (write : Write) (originOrdinal : Nat) :
      support.derivesFrom row (.output owner) →
      settled owner →
      PhaseOriginAt phase write row.left originOrdinal →
      Backing p support row

/-- Independent source typing, exact old row and actual head occurrence.
The ordered ordinary exposure is not a minted author table or a packet.
The two input origins retain their own evidence until issuance. -/
structure TypedInput {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (rel : List (Fin n × Fin n)) where
  head : PrecheckedHead (p := p.old) gd
  single : visible p.old.state.core p.old.root = [head.orig.declaration]
  declarationOrdinal : Nat
  registered : (registryAt p)[declarationOrdinal]? = some head.orig.declaration
  root : Site p.old.state.core positions
  atHead : root.pattern = head.orig.original ∧ root.query = head.orig.code
  atPoint : oldPosition positions root.index = .logical head.orig.capture.lower
  rawOrdinal : Nat
  physicalRow : (positions.cells.get root.index).oldOrdinal = rawOrdinal
  rootRow : Equation
  existingRoot : (rawAt p).equations[rawOrdinal]? = some rootRow
  rootOwns : rootRow.left = head.orig.capture.lower ∧ rootRow.right = root.term
  settled : Nat → Prop
  support : Supported (rawAt p) settled
  backing : Backing p support rootRow
  uses : List Occurrence
  typed : Read (restriction support) .actual (.variable head.orig.capture.lower) head.orig.code uses
  firstLabel : Nat
  firstPose : List Pose
  first : Site p.old.state.core positions
  enters : Hop root first ⟨.field firstLabel,firstPose⟩
  rootGuard : GuardedObservationInput p.old.state.core positions rel root.index
  rootSafe : ¬ ReturnsUpToEquality (graphOf p.old.state.core positions) root.index
  tail : List StepWire
  tailPoints : List (Fin n)
  final : Site p.old.state.core positions
  bit : Bool
  visits : Trail p.old.state.core positions rel first tail tailPoints final bit
  endsInField : LiteralVisits473.pathEndsWithField tail

def TypedInput.report {n p gd} {positions : Positions n} {rel}
    (input : TypedInput p gd positions rel) : SamePhaseInputObservation478 :=
  ⟨⟨p.old.root.occurrence,input.head.orig.declaration.id,input.declarationOrdinal⟩,
    input.head.orig.location.headArgument,
    input.firstPose ++ input.tail.flatMap StepWire.written,
    .field input.firstLabel :: input.tail.map (oneCompiledStep477 ∘ StepWire.action),
    oldPosition positions input.final.index,input.bit⟩

end Yulang.GeneralDeclarativeI65.I72.Producer479
