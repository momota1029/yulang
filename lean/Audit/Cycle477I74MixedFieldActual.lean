import Yulang.GeneralDeclarativeI65I74MixedFieldReport477
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.MixedActual477
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

def mixedPattern : Pattern :=
  .record 30 (.record 40 (.record 50 (.record 60 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])) (.app 9 [])
def mixedDecl : Declaration := ⟨218,19,[mixedPattern],[],[],[]⟩
def m4 : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def m6 : Equation := ⟨6,.record 40 (.record 50 (.variable 7) empty) empty⟩
def m7 : Equation := ⟨7,.record 60 (.variable 7) empty⟩
def mRows : List Equation := [m4,m6,m7]
def mRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,mRows⟩
def mProblem : FullProblem := (buildProblem mixedDecl mRaw).get (by decide +kernel)
def mixedCriterion : CertificateProtocol mProblem.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = mixedDecl)
  sound := by
    intro d _ yes
    obtain rfl : d = mixedDecl := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits mProblem.old.state.core.current.environment mixedDecl = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h
def mReady := (prepareTable mixedCriterion [(mixedDecl,())]).get (by decide +kernel)
def mTable : Table := ⟨mRows,[],[]⟩
def mAttached := (attach mProblem.state.base.core.current.ordinary mTable).get (by decide +kernel)
def mWire : BeforeCaptureWire :=
  ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,m4⟩,⟨1,1,m6⟩,⟨2,2,m7⟩]⟩
def splitOne (n : Nat) : ExactEscapeWire := ⟨(List.range 10).map (fun k => if k = n then 1 else 0),[1,0]⟩
def cl (n : Nat) : ClassWire := ⟨[(n,.same)],splitOne n⟩
def mPositions : Positions 7 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,1⟩,⟨.rowPos 1 [.field 40],1⟩,⟨.logical 7,2⟩,
      ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩],
    [.record [30],.record [40],.record [50],.record [60]],
    #v[cl 4,cl 6,cl 6,cl 7,cl 4,cl 6,cl 7]⟩
def mRel : List (Fin 7 × Fin 7) :=
  [(0,0),(0,4),(4,0),(4,4),(1,1),(1,5),(5,1),(5,5),(2,2),(3,3),(3,6),(6,3),(6,6)]
def mOuter : Checkpoint 7 :=
  ⟨0,4,4,⟨#v[0,1,2,3],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [3]],0⟩,
    ⟨#v[0,1,2,3],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [3]]⟩⟩
def mInner : Checkpoint 7 :=
  ⟨1,3,3,⟨#v[1,2,3],#v[.structural 1 [1],.structural 2 [2],.structural 3 [2]],0⟩,
    ⟨#v[0,1,2],#v[.structural 1 [1],.structural 2 [2],.structural 3 [2]]⟩⟩
def mInline : Checkpoint 7 :=
  ⟨2,2,2,⟨#v[2,3],#v[.structural 2 [1],.structural 3 [1]],0⟩,
    ⟨#v[0,1],#v[.structural 2 [1],.structural 3 [1]]⟩⟩
def mTerminal : Checkpoint 7 :=
  ⟨3,1,1,⟨#v[3],#v[.structural 3 [0]],0⟩,⟨#v[0],#v[.structural 3 [0]]⟩⟩

def mMoves : List (LiteralVisits473.StepWire × Checkpoint 7) :=
  [(⟨.field 40,[.payload]⟩,mInline),(⟨.field 50,[.payload]⟩,mTerminal)]

def runMixedOn (moves : List (LiteralVisits473.StepWire × Checkpoint 7)) :
    Option (List WrittenPattern460.PhysicalOrigin.Pose × List QueryStep476 × Place × Bool) := do
  let first ← readBeforeCapture (p := mProblem) mAttached mReady mWire
  let fixed ← checkFixedFieldChoice476 first 30 [.payload]
  let result ← readMixedFieldReport477 fixed mPositions mRel mOuter mInner moves
  pure (result.result.pose,result.result.compiled,result.result.place,result.result.bit)

/-- info: [true, true, false, false] -/
#guard_msgs in
#eval [(runMixedOn mMoves).isSome,(runMixedOn (mMoves.take 1)).isSome,
  (runMixedOn [(⟨.field 40,[.payload]⟩,mTerminal)]).isSome,
  (runMixedOn [(⟨.field 40,[.payload]⟩,mInline),(⟨.field 50,[.tail]⟩,mTerminal)]).isSome]



def mMu : Ty := .record 60 (.block [.record 60 (.inl 0) .emptyRecord] 0) .emptyRecord
theorem mMuStep477 : Equivalent mMu (record 60 mMu .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k mMu =
      CommonNominalFullCarrier.observeTy k (record 60 mMu .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _
def mFit : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 40 (record 50 mMu .emptyRecord) .emptyRecord)
      .emptyRecord else if n = 6 then record 40 (record 50 mMu .emptyRecord) .emptyRecord
      else mMu,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem interleaved_named_inline_named_actual_has_fit477 : FitsFull mProblem.state mFit := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ mRows at h
    rcases List.mem_cons.mp h with rfl | after
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp after with rfl | last
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · obtain rfl := List.mem_singleton.mp last
      exact mMuStep477
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval
  [runMixedOn (mMoves.take 1) ==
      some ([.payload,.payload],[.field 30,.field 40],.rowPos 1 [.field 40],false),
   runMixedOn mMoves ==
      some ([.payload,.payload,.payload],[.field 30,.field 40,.field 50],.logical 7,true),
   (runMixedOn [(⟨.field 40,[.payload]⟩,mTerminal)]).isNone,
   (runMixedOn [(⟨.field 40,[.payload]⟩,mInline),(⟨.field 50,[.tail]⟩,mTerminal)]).isNone]

#print axioms interleaved_named_inline_named_actual_has_fit477
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.MixedActual477
