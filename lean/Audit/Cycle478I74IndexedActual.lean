import Yulang.GeneralDeclarativeI65I74IndexedBeforeCapture478
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.IndexedActual478
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
def mRows : List Equation := [m4,m6,m7,m7]
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
def mTable : Table := ⟨[m6,m7,m4,m7],[],[]⟩
def mAttached := (attach mProblem.state.base.core.current.ordinary mTable).get (by decide +kernel)
def mWire : BeforeCaptureWire :=
  ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,2,m4⟩,⟨1,0,m6⟩,⟨2,1,m7⟩]⟩
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

theorem the_old_snapshot_with_two_identical_child_rows_has_a_fit478 : FitsFull mProblem.state mFit := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ mRows at h
    rcases List.mem_cons.mp h with rfl | after
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp after with rfl | last
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · rcases List.mem_cons.mp last with rfl | other
      · exact mMuStep477
      · obtain rfl := List.mem_singleton.mp other
        exact mMuStep477
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h


def pickEither478 (other : Bool) : IndexedBeforeCapture478 :=
  ⟨⟨0,0⟩,[⟨0,2⟩,⟨1,0⟩,if other then ⟨3,3⟩ else ⟨2,1⟩]⟩

def indexedInputOutput478 (choice : IndexedBeforeCapture478) :
    Option ((List Nat × Nat × Nat) × List (List QueryStep476 × (Nat × Nat × Nat))) := do
  let exact ← readIndexedBeforeCapture478 (p := mProblem) mAttached mReady choice
  let actual ← readLocatedAtHead476 exact.2
  let frame := exact.1.frame
  pure ((frame.occurrence,frame.declaration,frame.sourceOrdinal),
    actual.marks.map (fun item => (item.path,exposurePosition item.exposure)))

def expectedIndexed478 (raw author : Nat) :
    (List Nat × Nat × Nat) × List (List QueryStep476 × (Nat × Nat × Nat)) :=
  (([71,2],218,0),[([],(4,0,2)),([.field 30],(6,1,0)),
    ([.field 30,.field 40,.field 50],(7,raw,author))])

/-- info: [true, true, false, false] -/
#guard_msgs in
#eval [indexedInputOutput478 (pickEither478 false) == some (expectedIndexed478 2 1),
  indexedInputOutput478 (pickEither478 true) == some (expectedIndexed478 3 3),
  (indexedInputOutput478 ⟨⟨0,0⟩,[⟨0,1⟩,⟨1,0⟩,⟨2,1⟩]⟩).isSome,
  (indexedInputOutput478 ⟨⟨0,0⟩,[⟨0,2⟩,⟨1,8⟩,⟨2,1⟩]⟩).isSome]

#print axioms the_old_snapshot_with_two_identical_child_rows_has_a_fit478

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.IndexedActual478
