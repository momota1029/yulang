import Yulang.GeneralDeclarativeI65I74LegacyPostErasure479
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.LegacyPostErasureActual479
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
def m7 : Equation := ⟨7,.record 60 empty empty⟩
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
def mMu : Ty := record 60 .emptyRecord .emptyRecord
def mFit : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 40 (record 50 mMu .emptyRecord) .emptyRecord)
      .emptyRecord else if n = 6 then record 40 (record 50 mMu .emptyRecord) .emptyRecord
      else mMu,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem the_old_snapshot_with_two_identical_child_rows_has_a_fit479 : FitsFull mProblem.state mFit := by
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
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      · obtain rfl := List.mem_singleton.mp other
        exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h



open C466WrittenBinderCoordinates (OldCaptureReceipt)
open WrittenPattern460.PhysicalOrigin (Pose)

def differentStampWire479 : BeforeCaptureWire :=
  {mWire with offered := [⟨0,2,m4⟩,⟨1,0,m6⟩,⟨3,3,m7⟩]}

def actualFullCaptureEmission479 (wire : BeforeCaptureWire) :=
  emitFromOldSourceView479 mProblem wire (point 4) mixedPattern 0

def primaryLite479 : Option (Nat × Nat × Nat × List Pose) :=
  (actualFullCaptureEmission479 mWire).map fun r => (r.rawOrdinal,r.target,r.captured.binder,r.written)

theorem two_verified_original_stamp_choices_have_one_exact_old_compiler_output479 :
    FitsFull mProblem.state mFit ∧
    (readBeforeCapture (p := mProblem) mAttached mReady mWire).isSome = true ∧
    (readBeforeCapture (p := mProblem) mAttached mReady differentStampWire479).isSome = true ∧
    (actualFullCaptureEmission479 mWire).isSome = true ∧
    offeredInputView mProblem mWire = offeredInputView mProblem differentStampWire479 ∧
    actualFullCaptureEmission479 mWire = actualFullCaptureEmission479 differentStampWire479 := by
  exact ⟨the_old_snapshot_with_two_identical_child_rows_has_a_fit479,by decide +kernel,
    by decide +kernel,by decide +kernel,rfl,
    exact_old_source_view_agreement_controls_every_legacy_emission479 _ _ _ rfl _ _ _⟩

/-- info: true -/
#guard_msgs in
#eval primaryLite479.isSome

#print axioms two_verified_original_stamp_choices_have_one_exact_old_compiler_output479


theorem no_decoder_of_even_the_full_actual_old_compiler_result_recovers_both_stamp_pairs479
    (decode : Option OldCaptureReceipt → List SourceIndexPair478)
    (matchesOuter : decode (actualFullCaptureEmission479 mWire) = mWire.offered.map StampedRead.indexPair478)
    (matchesOther : decode (actualFullCaptureEmission479 differentStampWire479) =
      differentStampWire479.offered.map StampedRead.indexPair478) : False := by
  have output := two_verified_original_stamp_choices_have_one_exact_old_compiler_output479.2.2.2.2.2
  have impossible := matchesOuter.symm.trans ((congrArg decode output).trans matchesOther)
  have distinct : mWire.offered.map StampedRead.indexPair478 ≠
      differentStampWire479.offered.map StampedRead.indexPair478 := by decide
  exact distinct impossible

#print axioms no_decoder_of_even_the_full_actual_old_compiler_result_recovers_both_stamp_pairs479

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.LegacyPostErasureActual479
