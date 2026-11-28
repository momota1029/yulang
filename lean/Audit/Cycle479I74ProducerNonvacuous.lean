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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SmallProducerEvent479
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
    [],[]⟩
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
def finiteIssue479 : AuthoredIssueData := ⟨table479,⟨0,[⟨0,0⟩],[.payload]⟩,0⟩

def smallBranchChecks479 :=
  [readCheck input479.old.state.core pos479 rel479 (.logical 4) outer479 == some false,
   readCheck input479.old.state.core pos479 rel479 (.rowPos 0 [.field 30]) inner479 == some false,
   (readSourceIssueAtRoute input479 gd479 pos479 rel479 route479 finiteIssue479).map
      (fun res => res.outcome) == some ([.payload],[.field 30],.rowPos 0 [.field 30],false),
   (runAtBeforeCapture ((readBeforeCapture attached479 gd479 exactKey479).get
      (by decide +kernel))).isSome]

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval smallBranchChecks479


def oldSmallInvocation479 : BeforeCapture attached479 gd479 exactKey479 :=
  (readBeforeCapture attached479 gd479 exactKey479).get (by decide +kernel)

def actualSmallRun479 : PinnedCapture oldSmallInvocation479 :=
  (runAtBeforeCapture oldSmallInvocation479).get (by decide +kernel)

def noOutputHead479 : PrecheckedHead (p := input479.old) gd479 :=
  oldSmallInvocation479.head

def noOutputRoot479 : Site input479.old.state.core pos479 :=
  ⟨0,noOutputHead479.orig.original,noOutputHead479.orig.code,raw479.right,rfl⟩

def noOutputFirst479 : Site input479.old.state.core pos479 :=
  (readHop noOutputRoot479 ⟨.field 30,[.payload]⟩ 1).get (by decide +kernel)

theorem exact_first_hop479 : Nonempty (Hop noOutputRoot479 noOutputFirst479 ⟨.field 30,[.payload]⟩) := by
  have seen : readHop noOutputRoot479 ⟨.field 30,[.payload]⟩ 1 = some noOutputFirst479 :=
    (Option.some_get _).symm
  exact (reified_hop_keeps_the_same_old_place479 seen).2

def sourceGate479 := gateFromAttachedAuthor472 (p := input479) attached479

theorem outer_false479 :
    readCheck input479.old.state.core pos479 rel479 (.logical 4) outer479 = some false := by
  decide +kernel

theorem inner_false479 :
    readCheck input479.old.state.core pos479 rel479 (.rowPos 0 [.field 30]) inner479 = some false := by
  decide +kernel

noncomputable def independentlyTypedSource479 : TypedInput input479 gd479 pos479 rel479 := by
  have h := read_checkpoint_guards outer_false479
  have g := read_checkpoint_guards inner_false479
  have next : noOutputFirst479.index = inner479.which := by decide +kernel
  refine { head := noOutputHead479
           single := by decide +kernel
           declarationOrdinal := 0
           registered := by decide +kernel
           root := noOutputRoot479
           atHead := ⟨rfl,rfl⟩
           atPoint := by decide +kernel
           rawOrdinal := 0
           physicalRow := rfl
           rootRow := raw479
           existingRoot := rfl
           rootOwns := ⟨by decide +kernel,rfl⟩
           settled := _
           support := inputSourceOnly sourceGate479
           backing := .source (by simp [sourceGate479,inputSourceOnly,gateFromAttachedAuthor472,
             support,GeneralDeclarativeWitnessOrigins350.origin,table479])
           uses := actualSmallRun479.uses
           typed := exact_pinned_capture_uses_authored_not_output_only_support actualSmallRun479
           firstLabel := 30
           firstPose := [.payload]
           first := noOutputFirst479
           enters := Classical.choice exact_first_hop479
           rootGuard := h.1
           rootSafe := fun cy => Bool.false_ne_true (h.2.2.mpr cy)
           tail := []
           tailPoints := []
           final := noOutputFirst479
           bit := false
           visits := .stop (next ▸ g.1) (next ▸ g.2.2)
           endsInField := trivial }

def flatFit479 : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 (record 40 .emptyRecord .emptyRecord) .emptyRecord
      else .emptyRecord),Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem no_output_input_fits479 : FitsFull input479.state flatFit479 := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [raw479] at h
    obtain rfl := List.mem_singleton.mp h
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

def actualSourceBasis479 : PriorPhase := ⟨table479,[],some [⟨0,0⟩]⟩

theorem independently_typed_trace_has_an_exact_prior_source_without_any_output479 :
    actualSourceBasis479.ExactFor independentlyTypedSource479 ∧
    input479.old.root.demand.outputs = [] ∧ FitsFull input479.state flatFit479 := by
  refine ⟨?_,rfl,no_output_input_fits479⟩
  change Nonempty _ ∧ (∀ _row, _) ∧ GeneralDeclarativeInlineTrace331.Read _ _ _ _ _ ∧ _
  refine ⟨⟨attached479⟩,?_,actualSmallRun479.actualRead,?_⟩
  · intro row
    rfl
  · intro indices exact
    have picked : indices = [⟨0,0⟩] := (Option.some.inj exact).symm
    subst indices
    refine ⟨[⟨0,0,raw479⟩],?_,⟨⟨0,0,raw479⟩,⟨by decide +kernel,[],[],rfl,by simp⟩,rfl⟩,actualSmallRun479.actualRead⟩
    apply ordered_old_stamp_recovery_has_independent_exact_replay478.mpr
    exact .cons rfl rfl rfl .nil

#print axioms independently_typed_trace_has_an_exact_prior_source_without_any_output479
#print axioms no_output_input_fits479

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SmallProducerEvent479
