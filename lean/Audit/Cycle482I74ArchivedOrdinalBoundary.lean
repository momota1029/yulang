import Yulang.GeneralDeclarativeI65I74ArchivedNamedRoute482
import Yulang.GeneralDeclarativeI65I74NamedTerminalRoute482
import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482
import Yulang.GeneralDeclarativeI65I74TypedFocusHop482
import Yulang.GeneralDeclarativeI65I74G04ProducerExistence480
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
import Yulang.GeneralDeclarativeInlineFootprint331

/-! ### An exact prior typing archive is not the selected raw graph path

The three physical raw rows are the ordinary source root 4 and two equal
copies of a recursive record at logical name 6. The genuine pre-erasure
typing packet kept the first occurrence of the repeated row. The
independently checked selected field arrives at the other physical ordinal.
Both existing alternatives are included in the quotient check, with no
added names, generated ordinary rows, or released outputs. The positional
mismatch is not a type mismatch and carries no new rejection meaning. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PositiveArchiveDuplicate482
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

def stablePattern482 : Pattern :=
  .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])

def stableDecl482 : Declaration := ⟨218,19,[stablePattern482],[],[],[]⟩
def raw482 : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def rep482 : Equation := ⟨6,.record 40 (.variable 6) empty⟩
def snap482 : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[raw482,rep482,rep482]⟩
def input482 : FullProblem := (buildProblem stableDecl482 snap482).get (by decide +kernel)

def cert482 : CertificateProtocol input482.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = stableDecl482)
  sound := by
    intro d _ yes
    obtain rfl : d = stableDecl482 := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits input482.old.state.core.current.environment stableDecl482 = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def gd482 := (prepareTable cert482 [(stableDecl482,())]).get (by decide +kernel)
def table482 : Table := ⟨[raw482,rep482,rep482],[],[]⟩
def attached482 := (attach (rawAt input482) table482).get (by decide +kernel)
def exactKey482 : BeforeCaptureWire := ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,raw482⟩,⟨1,1,rep482⟩]⟩

def splitFresh482 (n : Nat) : ExactEscapeWire :=
  ⟨(List.range 7).map (fun k => if k = n then 1 else 0),[1]⟩
def cl482 (n : Nat) : ClassWire := ⟨[(n,.same)],splitFresh482 n⟩
def pos482 : Positions 5 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,2⟩,⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩],
    [.record [30],.record [40]],
    #v[cl482 4,cl482 6,cl482 4,cl482 6,cl482 6]⟩
def rel482 : List (Fin 5 × Fin 5) :=
  [(0,0),(0,2),(2,0),(2,2),
   (1,1),(1,3),(1,4),(3,1),(3,3),(3,4),(4,1),(4,3),(4,4)]
def outer482 : Checkpoint 5 :=
  ⟨0,2,2,⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]],0⟩,
    ⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]]⟩⟩
def inner482 : Checkpoint 5 :=
  ⟨1,1,1,⟨#v[1],#v[.structural 1 [0]],0⟩,⟨#v[0],#v[.structural 1 [0]]⟩⟩
def route482 : RouteWire 5 :=
  ⟨0,0,⟨outer482,[(⟨.field 30,[.payload]⟩,inner482)]⟩⟩
def finiteIssue482 : AuthoredIssueData := ⟨table482,⟨0,[⟨0,0⟩,⟨1,1⟩],[.payload]⟩,0⟩

def smallBranchChecks482 :=
  [readCheck input482.old.state.core pos482 rel482 (.logical 4) outer482 == some false,
   readCheck input482.old.state.core pos482 rel482 (.logical 6) inner482 == some true,
   (readSourceIssueAtRoute input482 gd482 pos482 rel482 route482 finiteIssue482).map
      (fun res => res.outcome) == some ([.payload],[.field 30],.logical 6,true),
   (runAtBeforeCapture ((readBeforeCapture attached482 gd482 exactKey482).get
      (by decide +kernel))).isSome]

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval smallBranchChecks482


def oldSmallInvocation482 : BeforeCapture attached482 gd482 exactKey482 :=
  (readBeforeCapture attached482 gd482 exactKey482).get (by decide +kernel)

def actualSmallRun482 : PinnedCapture oldSmallInvocation482 :=
  (runAtBeforeCapture oldSmallInvocation482).get (by decide +kernel)

def noOutputHead482 : PrecheckedHead (p := input482.old) gd482 :=
  oldSmallInvocation482.head

def noOutputRoot482 : Site input482.old.state.core pos482 :=
  ⟨0,noOutputHead482.orig.original,noOutputHead482.orig.code,raw482.right,rfl⟩

def noOutputFirst482 : Site input482.old.state.core pos482 :=
  (readHop noOutputRoot482 ⟨.field 30,[.payload]⟩ 1).get (by decide +kernel)

theorem exact_first_hop482 : Nonempty (Hop noOutputRoot482 noOutputFirst482 ⟨.field 30,[.payload]⟩) := by
  have seen : readHop noOutputRoot482 ⟨.field 30,[.payload]⟩ 1 = some noOutputFirst482 :=
    (Option.some_get _).symm
  exact (reified_hop_keeps_the_same_old_place479 seen).2

def sourceGate482 := gateFromAttachedAuthor472 (p := input482) attached482

theorem outer_false482 :
    readCheck input482.old.state.core pos482 rel482 (.logical 4) outer482 = some false := by
  decide +kernel

theorem inner_true482 :
    readCheck input482.old.state.core pos482 rel482 (.logical 6) inner482 = some true := by
  decide +kernel

noncomputable def independentlyTypedSource482 : TypedInput input482 gd482 pos482 rel482 := by
  have h := read_checkpoint_guards outer_false482
  have g := read_checkpoint_guards inner_true482
  have next : noOutputFirst482.index = inner482.which := by decide +kernel
  refine { head := noOutputHead482
           single := by decide +kernel
           declarationOrdinal := 0
           registered := by decide +kernel
           root := noOutputRoot482
           atHead := ⟨rfl,rfl⟩
           atPoint := by decide +kernel
           rawOrdinal := 0
           physicalRow := rfl
           rootRow := raw482
           existingRoot := rfl
           rootOwns := ⟨by decide +kernel,rfl⟩
           settled := _
           support := inputSourceOnly sourceGate482
           backing := .source (by simp [sourceGate482,inputSourceOnly,gateFromAttachedAuthor472,
             support,GeneralDeclarativeWitnessOrigins350.origin,table482])
           uses := actualSmallRun482.uses
           typed := exact_pinned_capture_uses_authored_not_output_only_support actualSmallRun482
           firstLabel := 30
           firstPose := [.payload]
           first := noOutputFirst482
           enters := Classical.choice exact_first_hop482
           rootGuard := h.1
           rootSafe := fun cy => Bool.false_ne_true (h.2.2.mpr cy)
           tail := []
           tailPoints := []
           final := noOutputFirst482
           bit := true
           visits := .stop (next ▸ g.1) (next ▸ g.2.2)
           endsInField := trivial }

def cyclicTy : Ty := .record 40 (.block [.record 40 (.inl 0) .emptyRecord] 0) .emptyRecord

theorem cyclicTy_step : Equivalent cyclicTy (record 40 cyclicTy .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k cyclicTy =
      CommonNominalFullCarrier.observeTy k (record 40 cyclicTy .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def flatFit482 : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 cyclicTy .emptyRecord
      else if n = 6 then cyclicTy else .emptyRecord),Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem no_output_input_fits482 : FitsFull input482.state flatFit482 := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [raw482,rep482,rep482] at h
    have hh : row = raw482 ∨ row = rep482 := by simpa using h
    rcases hh with rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact cyclicTy_step
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

def actualSourceBasis482 : PriorPhase := ⟨table482,[],some [⟨0,0⟩,⟨1,1⟩]⟩

theorem independently_typed_trace_has_an_exact_prior_source_without_any_output482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧
    input482.old.root.demand.outputs = [] ∧ FitsFull input482.state flatFit482 := by
  refine ⟨?_,rfl,no_output_input_fits482⟩
  change Nonempty _ ∧ (∀ _row, _) ∧ GeneralDeclarativeInlineTrace331.Read _ _ _ _ _ ∧ _
  refine ⟨⟨attached482⟩,?_,?_,?_⟩
  · intro row
    rfl
  · obtain ⟨rows,subset,holds⟩ := GeneralDeclarativeInlineFootprint331.trace actualSmallRun482.actualRead
    refine holds ⟨(rawAt input482).normal, actualSourceBasis482.authors.authored⟩ rfl ?_
    intro row inside
    have hh := subset inside
    change row ∈ [raw482,rep482] at hh
    change row ∈ [raw482,rep482,rep482]
    simpa using hh
  · intro indices exact
    have picked : indices = [⟨0,0⟩,⟨1,1⟩] := (Option.some.inj exact).symm
    subst indices
    refine ⟨[⟨0,0,raw482⟩,⟨1,1,rep482⟩],?_,⟨⟨0,0,raw482⟩,⟨by decide +kernel,[],[⟨1,1,rep482⟩],rfl,by simp⟩,rfl⟩,actualSmallRun482.actualRead⟩
    apply ordered_old_stamp_recovery_has_independent_exact_replay478.mpr
    exact .cons rfl rfl rfl (.cons rfl rfl rfl .nil)

theorem same_event_terminal_raw_index_is_absent_from_archived_reads482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧
    FitsFull input482.state flatFit482 ∧
    input482.old.root.demand.outputs = [] ∧
    oldPosition pos482 independentlyTypedSource482.final.index = .logical 6 ∧
    (pos482.cells.get independentlyTypedSource482.final.index).oldOrdinal = 2 ∧
    independentlyTypedSource482.report.outcome.2.2.2 = true ∧
    (∀ author : Nat, (⟨2,author⟩ : SourceIndexPair478) ∉
      actualSourceBasis482.recordedReads.getD []) := by
  obtain ⟨qualified,outNone,fit⟩ :=
    independently_typed_trace_has_an_exact_prior_source_without_any_output482
  have phys : noOutputFirst482.index = 1 := by decide +kernel
  refine ⟨qualified,fit,outNone,?_,?_,rfl,?_⟩
  · change oldPosition pos482 noOutputFirst482.index = .logical 6
    rw [phys]
    rfl
  · change (pos482.cells.get noOutputFirst482.index).oldOrdinal = 2
    rw [phys]
    rfl
  · intro a
    simp [actualSourceBasis482]

/-- Matching the archive entry-by-entry at every physical visited
position is strictly stronger than the old exact phase's qualification.
The existing producer still supplies a faithful finite report. -/
theorem old_exact_positive_report_has_a_faithful_wire_without_terminal_archive_stamp482 :
    (∃ w, IssueIsFaithful actualSourceBasis482 independentlyTypedSource482 w) ∧
    ¬ ∃ author, (⟨(pos482.cells.get independentlyTypedSource482.final.index).oldOrdinal,author⟩
      : SourceIndexPair478) ∈ actualSourceBasis482.recordedReads.getD [] := by
  obtain ⟨valid,_,_,_,physical,_,absent⟩ :=
    same_event_terminal_raw_index_is_absent_from_archived_reads482
  obtain ⟨_,w,_,faithful⟩ := named_producer_premise_supplies_an_issued_exact_report479
    g04_producer_proved_scoped480 actualSourceBasis482 independentlyTypedSource482 valid
  refine ⟨⟨w,faithful⟩,?_⟩
  rintro ⟨author,recorded⟩
  rw [physical] at recorded
  exact absent author recorded

#print axioms same_event_terminal_raw_index_is_absent_from_archived_reads482
#print axioms old_exact_positive_report_has_a_faithful_wire_without_terminal_archive_stamp482

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PositiveArchiveDuplicate482

/-! ### Locally lawful geometry can visit prior pending-only raw data

An exact old typed authored event and fitting state do not certify which
old raw row supports a later original path. Here the declared typing
reads the authorized self-recursive row at raw ordinal 1. The existing
quotient step uses another raw row at ordinal 2 with the same type
observations. That row is indexed only under a pending producer in the
independent prior. Neither its geometry nor a fitting model authorizes
it as source or release. Rejecting this proof card says nothing about
the disposition of the old language request. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PendingGeometry482
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

open PositiveArchiveDuplicate482 (buildProblem empty stableDecl482 raw482 rep482 cyclicTy cyclicTy_step)

def pending482 : Equation := ⟨6,.record 40 (.variable 7) empty⟩
def other482 : Equation := ⟨7,.record 40 (.variable 7) empty⟩
def snap482 : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[raw482,rep482,pending482,other482]⟩
def input482 : FullProblem := (buildProblem stableDecl482 snap482).get (by decide +kernel)

def cert482 : CertificateProtocol input482.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = stableDecl482)
  sound := by
    intro d _ yes
    obtain rfl : d = stableDecl482 := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits input482.old.state.core.current.environment stableDecl482 = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def gd482 := (prepareTable cert482 [(stableDecl482,())]).get (by decide +kernel)
def table482 : Table := ⟨[raw482,rep482],[(pending482,99),(other482,99)],[]⟩
def attached482 := (attach (rawAt input482) table482).get (by decide +kernel)
def exactKey482 : BeforeCaptureWire := ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,raw482⟩,⟨1,1,rep482⟩]⟩

def splitFresh482 (n : Nat) : ExactEscapeWire :=
  ⟨(List.range 8).map (fun k => if k = n then 1 else 0),[1]⟩
def cl482 (n : Nat) : ClassWire := ⟨[(n,.same)],splitFresh482 n⟩
def pos482 : Positions 7 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,2⟩,⟨.logical 7,3⟩,⟨.rowPos 0 [],0⟩,
      ⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩,⟨.rowPos 3 [],3⟩],
    [.record [30],.record [40]],#v[cl482 4,cl482 6,cl482 7,cl482 4,cl482 6,cl482 6,cl482 7]⟩
def rel482 : List (Fin 7 × Fin 7) :=
  [(0,0),(0,3),(3,0),(3,3)] ++ ([1,2,4,5,6] : List (Fin 7)).flatMap
    (fun i => ([1,2,4,5,6] : List (Fin 7)).map (fun j => (i,j)))
def outer482 : Checkpoint 7 :=
  ⟨0,3,2,⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 1 [2]],0⟩,
    ⟨#v[0,1,1],#v[.structural 0 [1],.structural 1 [1]]⟩⟩
def inner482 : Checkpoint 7 :=
  ⟨1,2,1,⟨#v[1,2],#v[.structural 1 [1],.structural 1 [1]],0⟩,⟨#v[0,0],#v[.structural 1 [0]]⟩⟩
def route482 : RouteWire 7 :=
  ⟨0,0,⟨outer482,[(⟨.field 30,[.payload]⟩,inner482)]⟩⟩
def finiteIssue482 : AuthoredIssueData := ⟨table482,⟨0,[⟨0,0⟩,⟨1,1⟩],[.payload]⟩,0⟩

def smallBranchChecks482 :=
  [readCheck input482.old.state.core pos482 rel482 (.logical 4) outer482 == some false,
   readCheck input482.old.state.core pos482 rel482 (.logical 6) inner482 == some true,
   (readSourceIssueAtRoute input482 gd482 pos482 rel482 route482 finiteIssue482).map
      (fun res => res.outcome) == some ([.payload],[.field 30],.logical 6,true),
   (runAtBeforeCapture ((readBeforeCapture attached482 gd482 exactKey482).get
      (by decide +kernel))).isSome]

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval smallBranchChecks482


def oldSmallInvocation482 : BeforeCapture attached482 gd482 exactKey482 :=
  (readBeforeCapture attached482 gd482 exactKey482).get (by decide +kernel)

def actualSmallRun482 : PinnedCapture oldSmallInvocation482 :=
  (runAtBeforeCapture oldSmallInvocation482).get (by decide +kernel)

def noOutputHead482 : PrecheckedHead (p := input482.old) gd482 :=
  oldSmallInvocation482.head

def noOutputRoot482 : Site input482.old.state.core pos482 :=
  ⟨0,noOutputHead482.orig.original,noOutputHead482.orig.code,raw482.right,rfl⟩

def noOutputFirst482 : Site input482.old.state.core pos482 :=
  (readHop noOutputRoot482 ⟨.field 30,[.payload]⟩ 1).get (by decide +kernel)

theorem exact_first_hop482 : Nonempty (Hop noOutputRoot482 noOutputFirst482 ⟨.field 30,[.payload]⟩) := by
  have seen : readHop noOutputRoot482 ⟨.field 30,[.payload]⟩ 1 = some noOutputFirst482 :=
    (Option.some_get _).symm
  exact (reified_hop_keeps_the_same_old_place479 seen).2

def sourceGate482 := gateFromAttachedAuthor472 (p := input482) attached482

theorem outer_false482 :
    readCheck input482.old.state.core pos482 rel482 (.logical 4) outer482 = some false := by
  decide +kernel

theorem inner_true482 :
    readCheck input482.old.state.core pos482 rel482 (.logical 6) inner482 = some true := by
  decide +kernel

noncomputable def independentlyTypedSource482 : TypedInput input482 gd482 pos482 rel482 := by
  have h := read_checkpoint_guards outer_false482
  have g := read_checkpoint_guards inner_true482
  have next : noOutputFirst482.index = inner482.which := by decide +kernel
  refine { head := noOutputHead482
           single := by decide +kernel
           declarationOrdinal := 0
           registered := by decide +kernel
           root := noOutputRoot482
           atHead := ⟨rfl,rfl⟩
           atPoint := by decide +kernel
           rawOrdinal := 0
           physicalRow := rfl
           rootRow := raw482
           existingRoot := rfl
           rootOwns := ⟨by decide +kernel,rfl⟩
           settled := _
           support := inputSourceOnly sourceGate482
           backing := .source (by simp [sourceGate482,inputSourceOnly,gateFromAttachedAuthor472,
             support,GeneralDeclarativeWitnessOrigins350.origin,table482])
           uses := actualSmallRun482.uses
           typed := exact_pinned_capture_uses_authored_not_output_only_support actualSmallRun482
           firstLabel := 30
           firstPose := [.payload]
           first := noOutputFirst482
           enters := Classical.choice exact_first_hop482
           rootGuard := h.1
           rootSafe := fun cy => Bool.false_ne_true (h.2.2.mpr cy)
           tail := []
           tailPoints := []
           final := noOutputFirst482
           bit := true
           visits := .stop (next ▸ g.1) (next ▸ g.2.2)
           endsInField := trivial }

def flatFit482 : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 cyclicTy .emptyRecord
      else if n = 6 ∨ n = 7 then cyclicTy else .emptyRecord),Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem no_output_input_fits482 : FitsFull input482.state flatFit482 := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [raw482,rep482,pending482,other482] at h
    have hh : row = raw482 ∨ row = rep482 ∨ row = pending482 ∨ row = other482 := by simpa using h
    rcases hh with rfl | rfl | rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact cyclicTy_step
    · exact cyclicTy_step
    · exact cyclicTy_step
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

def actualSourceBasis482 : PriorPhase := ⟨table482,[],some [⟨0,0⟩,⟨1,1⟩]⟩

theorem independently_typed_trace_has_an_exact_prior_source_without_any_output482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧
    input482.old.root.demand.outputs = [] ∧ FitsFull input482.state flatFit482 := by
  refine ⟨?_,rfl,no_output_input_fits482⟩
  change Nonempty _ ∧ (∀ _row, _) ∧ GeneralDeclarativeInlineTrace331.Read _ _ _ _ _ ∧ _
  refine ⟨⟨attached482⟩,?_,actualSmallRun482.actualRead,?_⟩
  · intro row
    rfl
  · intro indices exact
    have picked : indices = [⟨0,0⟩,⟨1,1⟩] := (Option.some.inj exact).symm
    subst indices
    refine ⟨[⟨0,0,raw482⟩,⟨1,1,rep482⟩],?_,⟨⟨0,0,raw482⟩,⟨by decide +kernel,[],[⟨1,1,rep482⟩],rfl,by simp⟩,rfl⟩,actualSmallRun482.actualRead⟩
    apply ordered_old_stamp_recovery_has_independent_exact_replay478.mpr
    exact .cons rfl rfl rfl (.cons rfl rfl rfl .nil)

theorem actual_qualified_event_can_reach_pending_only_physical_row482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧
    FitsFull input482.state flatFit482 ∧
    input482.old.root.demand.outputs = [] ∧
    oldPosition pos482 independentlyTypedSource482.final.index = .logical 6 ∧
    (rawAt input482).equations[(pos482.cells.get independentlyTypedSource482.final.index).oldOrdinal]? =
      some pending482 ∧
    independentlyTypedSource482.report.outcome.2.2.2 = true ∧
    pending482 ∉ actualSourceBasis482.authors.authored ∧
    (pending482,99) ∈ actualSourceBasis482.authors.produced ∧
    99 ∉ actualSourceBasis482.authors.released := by
  obtain ⟨qualified,outNone,fit⟩ :=
    independently_typed_trace_has_an_exact_prior_source_without_any_output482
  have phys : noOutputFirst482.index = 1 := by decide +kernel
  refine ⟨qualified,fit,outNone,?_,?_,rfl,?_,?_,?_⟩
  · change oldPosition pos482 noOutputFirst482.index = .logical 6
    rw [phys]
    rfl
  · change (rawAt input482).equations[(pos482.cells.get noOutputFirst482.index).oldOrdinal]? = _
    rw [phys]
    rfl
  · simp [actualSourceBasis482,table482,pending482,raw482,rep482]
  · simp [actualSourceBasis482,table482]
  · simp [actualSourceBasis482,table482]

open SourceExposure481.ClosedBank
open LiteralVisits473 (StepWire ReadStep readLiteralVisitStep)

def exactMove482 : StepWire := ⟨.field 30,[.payload]⟩
def exactGeometryStep482 : ReadStep input482.old.state.core exactMove482
    noOutputRoot482.pattern noOutputRoot482.query noOutputRoot482.term :=
  (readLiteralVisitStep input482.old.state.core noOutputRoot482.pattern noOutputRoot482.query
    noOutputRoot482.term exactMove482).get (by decide +kernel)

theorem no_card_can_bind_the_pending_geometry_visit_to_the_authored_prior482
    (card : ReadCard) (selected : Option SourceIndexPair478) :
    checkArrival (p := input482) table482 noOutputFirst482 (.variable 6) card ≠ some selected := by
  intro hit
  have found := checked_arrival_is_exact_original_source_row_or_literal_term hit
  rcases found with ⟨_,impossible,_⟩ | ⟨name,idx,row,_,_,raw,old,authored,_,_⟩
  · exact impossible 6 rfl
  · have phys : noOutputFirst482.index = 1 := by decide +kernel
    rw [phys] at raw
    change idx.raw = 2 at raw
    rw [raw] at old
    have rowMatch : some pending482 = some row := old
    have literalEq := Option.some.inj rowMatch
    subst row
    have owned := List.mem_of_getElem? authored
    exact actual_qualified_event_can_reach_pending_only_physical_row482.2.2.2.2.2.2.1 owned

/-- All possible supplied read cards fail to authenticate the exact pending
geometry step as an authored arrival. This is not a language rejection:
the independent old problem, typing event, prior and position are real. -/
theorem exact_qualified_old_geometry_does_not_reify_as_an_authored_focus482
    (card : ReadCard) :
    readFocusedCardHop (p := input482) table482 noOutputRoot482 exactMove482 card 1 = none := by
  cases hit : readFocusedCardHop (p := input482) table482 noOutputRoot482 exactMove482 card 1 with
  | none => rfl
  | some accepted =>
    have read : readLiteralVisitStep input482.old.state.core noOutputRoot482.pattern noOutputRoot482.query
        noOutputRoot482.term exactMove482 = some exactGeometryStep482 := (Option.some_get _).symm
    have first : readHop noOutputRoot482 exactMove482 1 = some noOutputFirst482 := (Option.some_get _).symm
    have exactStep := Option.some.inj (accepted.stepRead.symm.trans read)
    have exactSite := Option.some.inj (accepted.siteRead.symm.trans first)
    have name : exactGeometryStep482.actualRawChild = .variable 6 := by
      apply (GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp
      decide +kernel
    have origin := accepted.sameRow
    rw [exactStep,exactSite,name] at origin
    exact False.elim (no_card_can_bind_the_pending_geometry_visit_to_the_authored_prior482 _ _ origin)

#print axioms exact_qualified_old_geometry_does_not_reify_as_an_authored_focus482
#print axioms actual_qualified_event_can_reach_pending_only_physical_row482

def actualAuthoredTerminalCard482 (raw author : Nat) : ReadCard :=
  .record [⟨⟨raw,author⟩,[]⟩] [40] [(40,.variable 3)] empty
    (.cons .capture .nil) (.primitive .nil)

def actualTerminalComparison482 (raw author : Nat)
    (pairs : List (Fin 7 × Fin 7) := rel482) :=
  readAuthoredTerminalCompare input482 table482 pos482 pairs inner482 6
    noOutputFirst482.query (actualAuthoredTerminalCard482 raw author)

def terminalCompareTuple482 :=
  (actualTerminalComparison482 1 1).map fun out =>
    (out.author.ordinals.raw,out.author.ordinals.author,out.lexical.val,out.sign)

/-- info: [true, false, false, false, true] -/
#guard_msgs in
#eval [(actualTerminalComparison482 1 1).isSome,
  (actualTerminalComparison482 2 1).isSome,
  (actualTerminalComparison482 1 0).isSome,
  (actualTerminalComparison482 1 1 []).isSome,
  terminalCompareTuple482 == some (1,1,4,true)]

theorem real_authored_terminal_matches_the_pending_geometry_sign_without_using_it_as_source482 :
    FitsFull input482.state flatFit482 ∧
    (actualTerminalComparison482 1 1).isSome = true ∧
    (actualTerminalComparison482 2 1).isSome = false := by
  exact ⟨no_output_input_fits482,by decide +kernel,by decide +kernel⟩

#print axioms real_authored_terminal_matches_the_pending_geometry_sign_without_using_it_as_source482

def completeAuthoredCard482 (raw author : Nat) : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩] [30] [(30,.record 40 (.variable 3) empty)] empty
    (.cons (actualAuthoredTerminalCard482 raw author) .nil) (.primitive .nil)

def wholeTerminalWire482 (raw author : Nat) : NamedTerminalWire 7 :=
  ⟨0,0,outer482,[],exactMove482,inner482,completeAuthoredCard482 raw author,0,[outer482]⟩

def completeAlternate482 (raw author : Nat) (roots : List (Checkpoint 7) := [outer482]) :=
  readNamedTerminalRoute input482 gd482 pos482 rel482 actualSourceBasis482
    {wholeTerminalWire482 raw author with roots := roots}

def completeAlternateSummary482 :=
  (completeAlternate482 1 1).map fun out =>
    (out.initial.output.outcome, out.conclusion.author.ordinals.raw,
      out.conclusion.author.ordinals.author, out.last.index.val)

/-- info: [true, false, false, true] -/
#guard_msgs in
#eval [(completeAlternate482 1 1).isSome,(completeAlternate482 2 1).isSome,
  (completeAlternate482 1 1 []).isSome,
  completeAlternateSummary482 == some (([.payload],[.field 30],.logical 6,true),1,1,1)]

theorem pending_geometry_original_signed_report_has_a_source_checked_terminal_route482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧ FitsFull input482.state flatFit482 ∧
    (completeAlternate482 1 1).isSome = true := by
  exact ⟨independently_typed_trace_has_an_exact_prior_source_without_any_output482.1,
    no_output_input_fits482,by decide +kernel⟩

#print axioms pending_geometry_original_signed_report_has_a_source_checked_terminal_route482
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PendingGeometry482

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PendingGeometry482
open ArchiveValidation482

def archivedAndNamedRun482 (basis : Producer479.PriorPhase) (author : Nat := 1) :=
  readArchivedNamedRoute input482 gd482 pos482 rel482 basis
    ⟨wholeTerminalWire482 1 1,completeAuthoredCard482 1 author⟩

def archivedAndNamedSummary482 :=
  (archivedAndNamedRun482 actualSourceBasis482).map fun r =>
    (r.archival.archived.map (fun item => (item.raw,item.author)),
      r.exactRoute.initial.output.outcome,
      r.exactRoute.conclusion.author.ordinals.raw,r.exactRoute.last.index.val)

/-- info: [true, false, false, false, true] -/
#guard_msgs in
#eval [(archivedAndNamedRun482 actualSourceBasis482).isSome,
  (archivedAndNamedRun482 {actualSourceBasis482 with recordedReads := none}).isSome,
  (archivedAndNamedRun482 {actualSourceBasis482 with recordedReads := some [⟨0,1⟩,⟨1,1⟩]}).isSome,
  (archivedAndNamedRun482 actualSourceBasis482 0).isSome,
  archivedAndNamedSummary482 == some ([(0,0),(1,1)],([.payload],[.field 30],.logical 6,true),1,1)]

theorem exact_archive_and_distinct_old_geometry_can_coexist_in_the_same_checked_report482 :
    actualSourceBasis482.ExactFor independentlyTypedSource482 ∧
    FitsFull input482.state flatFit482 ∧
    (archivedAndNamedRun482 actualSourceBasis482).isSome = true :=
  ⟨independently_typed_trace_has_an_exact_prior_source_without_any_output482.1,
    no_output_input_fits482,by decide +kernel⟩

#print axioms exact_archive_and_distinct_old_geometry_can_coexist_in_the_same_checked_report482

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.PendingGeometry482
