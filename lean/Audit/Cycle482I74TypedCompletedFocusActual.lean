import Yulang.GeneralDeclarativeI65I74ExactScopedReport482
import Yulang.GeneralDeclarativeI65I74TypedCompletedDecline482
import Yulang.GeneralDeclarativeI65I74G04ProducerMeaning479
import Yulang.GeneralDeclarativeI65I74ReplayEventFootprint478
import Yulang.GeneralDeclarativeI65I74NamedQuotientSemantics476
import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475
import Yulang.GeneralDeclarativeI65I74BeforeCaptureField475
import Yulang.GeneralDeclarativeI65I74BeforeCaptureRun475
import Yulang.GeneralDeclarativeI65I74PinnedInputAuthorization474
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65I74RecordTraversal455
import Yulang.GeneralDeclarativeI65I74RecordEntry412
import Yulang.GeneralDeclarativeWitnessLiteral349
import Yulang.GeneralDeclarativeI65I74FullState444
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.ActualCompletedFocus482
open Yulang.GeneralDeclarativeI65
open WrittenPattern460 (CoreState)
open RetainedFull445
open ObservationSyntax471
open RecordTraversal455.MixedQA
open AuthenticatedHop458 (Wire)
open InlineStructuralPolicy458 (Ticket emptyPolicy)
open RoutedNominalPoint456
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Ty Equivalent record)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)
open List410 (ExactEscapeWire)
open RecordK2412 (FieldCycleWire)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open PreparedDeclarations463
open PhysicalVisit463.IssuedProjection464

open NativeProducer465 (CheckedPhase)
open GeneralDeclarativeWitnessNativeValue360 (Write Address)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)
open GeneralDeclarativeWitnessNativeOrder362 (node)

/-- A literal pre-existing completion ledger for this fixture. This
does not construct or exercise a compiler emitting the release. -/
def completedStamp482 : Stamp := ⟨[33,1],19,410,3⟩
def completedAddress482 : GeneralDeclarativeWitnessNativeValue360.Address := ⟨completedStamp482,0,0,0,4,0⟩
def completedWrite482 : Write := ⟨completedAddress482,.leaf 4⟩

def bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
def empty : Expr := .primitive .emptyRecord []
def buildProblem (decl : Declaration) (physicalState : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    (let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
      ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
     ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[decl]⟩)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,physicalState,[]⟩,List.replicate 20 [] ++ [[cov]],
    [originalOfWrite completedWrite482],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)


open InputCoordinates475
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open ObservationAlternatives473 (Positions Place)
open ObservationRawAlias471 (ClassWire)
open LiteralVisits473 (Checkpoint)
open ObservationSyntax471 (CheckedFieldBit)
open Yulang.GeneralDeclarativeI65.I72.Producer479
open LiteralVisits473 (readCheck read_checkpoint_guards pathEndsWithField)
open ObservationAlternatives473 (graphOf oldPosition readTermAt)
open QuotientObservation471 (ReturnsUpToEquality)
open GeneralDeclarativeWitnessOrigins350 (support)
open LiteralFold471 (inputSourceOnly)

def stablePattern479 : Pattern :=
  .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])

def stableDecl479 : Declaration := ⟨218,19,[stablePattern479],[],[],[]⟩
def raw479 : Equation := ⟨4,.record 30 (.record 40 empty empty) empty⟩
def snap479 : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[raw479]⟩
def input479 : FullProblem := (buildProblem stableDecl479 snap479).get (by decide +kernel)

def cert479 : CertificateProtocol input479.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = stableDecl479)
  sound := by
    intro d _ yes
    obtain rfl : d = stableDecl479 := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits input479.old.state.core.current.environment stableDecl479 = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def gd479 := (prepareTable cert479 [(stableDecl479,())]).get (by decide +kernel)
def table479 : Table := ⟨[raw479],[],[]⟩
def attached479 := (attach (rawAt input479) table479).get (by decide +kernel)
def exactKey479 : BeforeCaptureWire := ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,raw479⟩]⟩

def splitFresh479 : ExactEscapeWire :=
  ⟨(List.range 5).map (fun k => if k = 4 then 1 else 0),[1]⟩

def cl479 : ClassWire := ⟨[(4,.same)],splitFresh479⟩
def pos479 : Positions 4 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.rowPos 0 [.field 30],0⟩,
      ⟨.rowPos 0 [.field 30,.field 40],0⟩,⟨.rowPos 0 [],0⟩],
    [.record [30],.record [40],.record []],
    #v[cl479,cl479,cl479,cl479]⟩
def rel479 : List (Fin 4 × Fin 4) := [(0,0),(0,3),(3,0),(3,3),(1,1),(2,2)]
def outer479 : Checkpoint 4 :=
  ⟨0,3,3,⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 []],0⟩,
    ⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 []]⟩⟩
def inner479 : Checkpoint 4 :=
  ⟨1,2,2,⟨#v[1,2],#v[.structural 1 [1],.structural 2 []],0⟩,
    ⟨#v[0,1],#v[.structural 1 [1],.structural 2 []]⟩⟩
def route479 : RouteWire 4 :=
  ⟨0,0,⟨outer479,[(⟨.field 30,[.payload]⟩,inner479)]⟩⟩

open Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank

def ordinaryOwner482 : Nat := 77
def phase482 : CheckedPhase input479.old.state.core :=
  ⟨⟨rawAt input479,⟨[completedStamp482],[completedWrite482]⟩⟩,rfl,⟨[completedAddress482]⟩⟩
def oldAssociation482 : CompletedAssociation :=
  ⟨ordinaryOwner482,0,raw479,completedWrite482,0⟩
def priorCompleted482 : PriorPhase :=
  ⟨⟨[],[(raw479,ordinaryOwner482)],[ordinaryOwner482]⟩,[oldAssociation482],none⟩
def pendingCompleted482 : PriorPhase :=
  {priorCompleted482 with authors := {priorCompleted482.authors with released := []}}

def nestedCard482 : ReadCard :=
  .record [] [40] [(40,.variable 3)] empty (.cons .capture .nil) (.primitive .nil)
def focusCard482 : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩] [30] [(30,.record 40 (.variable 3) empty)] empty
    (.cons nestedCard482 .nil) (.primitive .nil)

def finalWire482 : CompletedFocusWire 4 :=
  ⟨⟨route479,focusCard482,0,[outer479]⟩,ordinaryOwner482,0,⟨completedWrite482,0⟩⟩

def checkCompleted482 (prior : PriorPhase := priorCompleted482)
    (phase : CheckedPhase input479.old.state.core := phase482)
    (wire : CompletedFocusWire 4 := finalWire482) :=
  readCompletedFocus input479 gd479 pos479 rel479 prior phase wire

def caseValue482 :=
  (checkCompleted482).map (fun r => r.output.outcome)

def staleWrite482 : Write :=
  {completedWrite482 with address := {completedAddress482 with owner := {completedStamp482 with version := 2}}}
def staleWire482 : CompletedFocusWire 4 :=
  {finalWire482 with release := ⟨staleWrite482,0⟩}
def staleGrant482 : CheckedPhase input479.old.state.core :=
  {phase482 with gate := ⟨[completedAddress482,staleWrite482.address]⟩}
def staleBasis482 : PriorPhase :=
  {priorCompleted482 with completed := [{oldAssociation482 with write := staleWrite482}]}

/-- info: [true, true, false, false, false, false, false, false] -/
#guard_msgs in
#eval [checkCompleted482.isSome,
  caseValue482 == some ([.payload],[.field 30],.rowPos 0 [.field 30],false),
  (checkCompleted482 pendingCompleted482).isSome,
  (checkCompleted482 {priorCompleted482 with completed := []}).isSome,
  (checkCompleted482 priorCompleted482 {phase482 with gate := ⟨[]⟩}).isSome,
  (checkCompleted482 staleBasis482 staleGrant482 staleWire482).isSome,
  (checkCompleted482 priorCompleted482 phase482 {finalWire482 with producedOrdinal := 1}).isSome,
  (runRootPinnedAuthoredCard input479 gd479 pos479 rel479 priorCompleted482 route479 focusCard482 0).isSome]

def nativeModel482 : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 (record 40 .emptyRecord .emptyRecord) .emptyRecord
      else .emptyRecord),Common.rowEmpty),fun _ => none,
    fun n => if n = 4 then some (node completedWrite482.code) else none⟩

theorem fixed_completed_fixture_has_original_same_state_model482 :
    FitsFull input479.state nativeModel482 := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ none; cases none
  · intro _ none; cases none
  · intro row member
    change row ∈ [raw479] at member
    obtain rfl := List.mem_singleton.mp member
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ none; cases none
  · intro src known
    change src ∈ [originalOfWrite completedWrite482] at known
    obtain rfl := List.mem_singleton.mp known
    rfl
  · intro _ none; cases none

#print axioms fixed_completed_fixture_has_original_same_state_model482

def askedCompletion482 : SamePhaseInputObservation478 :=
  ⟨⟨[71,2],218,0⟩,0,[.payload],[.field 30],.rowPos 0 [.field 30],false⟩

def confirmCompletion482 (candidate : SamePhaseInputObservation478) : Bool :=
  checkScopedCompleted482 input479 gd479 pos479 rel479 priorCompleted482 phase482 finalWire482 candidate

/-- info: [true, false, false, false, false, false] -/
#guard_msgs in
#eval [
  confirmCompletion482 askedCompletion482,
  confirmCompletion482 {askedCompletion482 with frame := ⟨[71,3],218,0⟩},
  confirmCompletion482 {askedCompletion482 with rootArgument := 3},
  confirmCompletion482 {askedCompletion482 with outcome := ([.tail],[.field 30],.rowPos 0 [.field 30],false)},
  confirmCompletion482 {askedCompletion482 with outcome := ([.payload],[.field 31],.rowPos 0 [.field 30],false)},
  confirmCompletion482 {askedCompletion482 with outcome := ([.payload],[.field 30],.rowPos 0 [.field 30],true)}]
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.ActualCompletedFocus482
