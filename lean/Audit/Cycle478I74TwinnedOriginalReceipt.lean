import Yulang.GeneralDeclarativeI65I74NamedSourceAutoOrdinal477
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedQuotientActual476
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

def sourcePattern : Pattern := .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])
def authoredDecl : Declaration := ⟨218,19,[.join sourcePattern sourcePattern],[],[],[]⟩
def rootEq : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def namedEq (cyclic : Bool) : Equation := ⟨6,.record 40 (.variable (if cyclic then 6 else 7)) empty⟩
def leafEq : Equation := ⟨7,empty⟩
def oldRows (cyclic : Bool) : List Equation := [rootEq,namedEq cyclic,leafEq]
def sourceState (cyclic : Bool) : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,oldRows cyclic⟩
def pp (cyclic : Bool) : FullProblem :=
  (buildProblem authoredDecl (sourceState cyclic)).get (by cases cyclic <;> decide +kernel)

def criterion (cyclic : Bool) : CertificateProtocol (pp cyclic).state.base.core.current where
  Data := Unit
  verify d _ := decide (d = authoredDecl)
  sound := by
    intro d _ yes
    obtain rfl : d = authoredDecl := of_decide_eq_true yes
    have or : RecordTrail455.localAuthorBits (pp cyclic).old.state.core.current.environment authoredDecl = true := by
      cases cyclic <;> decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp or
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c absent; cases absent
def gd (c : Bool) := (prepareTable (criterion c) [(authoredDecl,())]).get (by cases c <;> decide +kernel)
def table (c : Bool) : Table := ⟨oldRows c,[],[]⟩
def attached (c : Bool) := (attach (pp c).state.base.core.current.ordinary (table c)).get
  (by cases c <;> decide +kernel)
def firstWire (c : Bool) : BeforeCaptureWire :=
  ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,rootEq⟩,⟨1,1,namedEq c⟩,⟨2,2,leafEq⟩]⟩
def q : NamedSelectionWire476 := ⟨30,[.payload],1⟩

def splitOne (n : Nat) : ExactEscapeWire := ⟨(List.range 10).map (fun k => if k = n then 1 else 0),[1,0]⟩
def cl (n : Nat) : ClassWire := ⟨[(n,.same)],splitOne n⟩

def ppPositions : Positions 6 := ⟨
  #v[⟨.logical 4,0⟩,⟨.logical 6,1⟩,⟨.logical 7,2⟩,
    ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩],
  [.record [30],.record [40],.record []],
  #v[cl 4,cl 6,cl 7,cl 4,cl 6,cl 7]⟩

def bisimPairs : List (Fin 6 × Fin 6) :=
  [(0,0),(0,3),(3,0),(3,3),(1,1),(1,4),(4,1),(4,4),(2,2),(2,5),(5,2),(5,5)]

def outerCheck (c : Bool) : Checkpoint 6 :=
  if c then
    ⟨0,2,2,⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]],0⟩,
      ⟨#v[0,1],#v[.structural 0 [1],.structural 1 [1]]⟩⟩
  else
    ⟨0,3,3,⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 []],0⟩,
      ⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 []]⟩⟩

def innerCheck (c : Bool) : Checkpoint 6 :=
  if c then
    ⟨1,1,1,⟨#v[1],#v[.structural 1 [0]],0⟩,⟨#v[0],#v[.structural 1 [0]]⟩⟩
  else
    ⟨1,2,2,⟨#v[1,2],#v[.structural 1 [1],.structural 2 []],0⟩,
      ⟨#v[0,1],#v[.structural 1 [1],.structural 2 []]⟩⟩

def checkReport (c : Bool) (wire : NamedSelectionWire476) (graph : Positions 6)
    (outer inner : Checkpoint 6) : Option CheckedFieldBit := do
  let before ← readBeforeCapture (p := pp c) (attached c) (gd c) (firstWire c)
  let fixed ← checkFixedFieldChoice476 before 30 [.payload]
  let answer ← readNamedFieldQuotient476 fixed wire graph bisimPairs outer inner
  return answer.report

def expected (b : Bool) : CheckedFieldBit := ⟨[71,2],218,0,[.payload],30,b⟩
def runAt (c : Bool) := checkReport c q ppPositions (outerCheck c) (innerCheck c)
def wrongRow : Positions 6 :=
  { ppPositions with cells := ppPositions.cells.set (1 : Fin 6) ⟨.logical 6,2⟩ }

def regular40 : Ty := .record 40 (.block [.record 40 (.inl 0) .emptyRecord] 0) .emptyRecord
theorem regular40_exposes_one_fitting_step : Equivalent regular40 (record 40 regular40 .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k regular40 =
      CommonNominalFullCarrier.observeTy k (record 40 regular40 .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def assignmentModel (c : Bool) : I72.Model :=
  let right := if c then regular40 else record 40 .emptyRecord .emptyRecord
  ⟨fun n => (if n = 4 then record 30 right .emptyRecord else
      if n = 6 then right else .emptyRecord, Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem named_positive_and_safe_examples_really_have_fits :
    FitsFull (pp true).state (assignmentModel true) ∧ FitsFull (pp false).state (assignmentModel false) := by
  have both (c : Bool) : FitsFull (pp c).state (assignmentModel c) := by
    have rowFits : ∀ row ∈ (pp c).state.base.core.current.ordinary.equations,
        GeneralDeclarativeEntailment320.Holds (assignmentModel c).assignment row := by
      intro row h
      cases c with
      | false =>
        change row ∈ oldRows false at h
        rcases List.mem_cons.mp h with rfl | afterRoot
        · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
        rcases List.mem_cons.mp afterRoot with rfl | afterInner
        · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
        · obtain rfl := List.mem_singleton.mp afterInner
          exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      | true =>
        change row ∈ oldRows true at h
        rcases List.mem_cons.mp h with rfl | afterRoot
        · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
        rcases List.mem_cons.mp afterRoot with rfl | afterInner
        · exact regular40_exposes_one_fitting_step
        · obtain rfl := List.mem_singleton.mp afterInner
          exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    cases c <;> refine ⟨⟨⟨⟨⟨?_,?_⟩,rowFits⟩,?_⟩,?_⟩,?_⟩
      <;> intro _ h <;> cases h
  exact ⟨both true,both false⟩

open WrittenPattern460.PhysicalOrigin (Pose)

def sameFieldTwoOriginalPoses477 (path : List Pose) : Option (Nat × CheckedFieldBit) := do
  let before ← readBeforeCapture (p := pp true) (attached true) (gd true) (firstWire true)
  let fixed ← checkFixedFieldChoice476 before 30 path
  let answer ← readImmediateNamedQuotientWithoutOrdinal477 fixed ppPositions bisimPairs (outerCheck true) (innerCheck true)
  pure (answer.1,answer.2.report)

def beforeTwin477 := (readBeforeCapture (p := pp true) (attached true) (gd true) (firstWire true)).get (by decide +kernel)

def twinPathMarks477 := (readLocatedAtHead476 beforeTwin477).map (fun trace => trace.marks.map (fun m => (m.path,exposurePosition m.exposure)))

theorem real_duplicate_written_sites_are_not_disambiguated_by_a_unique_compiled_path478 :
    FitsFull (pp true).state (assignmentModel true) ∧
    twinPathMarks477 = some [([],(4,0,0)),([.field 30],(6,1,1))] ∧
    sameFieldTwoOriginalPoses477 [.left,.payload] =
      some (1,⟨[71,2],218,0,[.left,.payload],30,true⟩) ∧
    sameFieldTwoOriginalPoses477 [.right,.payload] =
      some (1,⟨[71,2],218,0,[.right,.payload],30,true⟩) ∧
    sameFieldTwoOriginalPoses477 [.payload] = none := by
  refine ⟨named_positive_and_safe_examples_really_have_fits.1,?_⟩
  decide +kernel

/-- info: [true, true, false] -/
#guard_msgs in
#eval [(sameFieldTwoOriginalPoses477 [.left,.payload]).isSome,
 (sameFieldTwoOriginalPoses477 [.right,.payload]).isSome,
 (sameFieldTwoOriginalPoses477 [.payload]).isSome]

#print axioms real_duplicate_written_sites_are_not_disambiguated_by_a_unique_compiled_path478


theorem one_compiled_ordinal_cannot_recover_both_written_paths478
    (decode : Nat → List Pose)
    (agrees : ∀ (pose : List Pose) (ordinal : Nat) (result : CheckedFieldBit),
      sameFieldTwoOriginalPoses477 pose = some (ordinal,result) → decode ordinal = pose) :
    False := by
  have f := real_duplicate_written_sites_are_not_disambiguated_by_a_unique_compiled_path478
  have first := agrees [.left,.payload] 1 _ f.2.2.1
  have second := agrees [.right,.payload] 1 _ f.2.2.2.1
  have impossible := first.symm.trans second
  cases impossible

#print axioms one_compiled_ordinal_cannot_recover_both_written_paths478

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedQuotientActual476
