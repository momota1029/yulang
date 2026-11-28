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
def authoredDecl : Declaration := ⟨218,19,[sourcePattern],[],[],[]⟩
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

def actualControls : List Bool :=
  [decide (runAt true = some (expected true)),
   decide (runAt false = some (expected false)),
   (checkReport true q wrongRow (outerCheck true) (innerCheck true)).isSome,
   (checkReport true {q with markOrdinal := 0} ppPositions (outerCheck true) (innerCheck true)).isSome,
   (checkReport true {q with writtenPath := [.tail,.payload]} ppPositions (outerCheck true) (innerCheck true)).isSome,
   (checkReport true q ppPositions (innerCheck true) (innerCheck true)).isSome,
   (checkReport false q ppPositions (outerCheck false) (innerCheck true)).isSome]

/-- info: [true, true, false, false, false, false, false] -/
#guard_msgs in
#eval actualControls

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

theorem exact_issued_path_named_positive_and_safe476 :
    runAt true = some (expected true) ∧ runAt false = some (expected false) ∧
    actualControls = [true,true,false,false,false,false,false] := by decide +kernel

#print axioms exact_issued_path_named_positive_and_safe476
#print axioms named_positive_and_safe_examples_really_have_fits

def backEq : Equation := ⟨6,.record 40 (.variable 4) empty⟩
def backRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootEq,backEq,leafEq]⟩
def backProblem : FullProblem := (buildProblem authoredDecl backRaw).get (by decide +kernel)

def backCriterion : CertificateProtocol backProblem.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = authoredDecl)
  sound := by
    intro d _ yes
    obtain rfl : d = authoredDecl := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits backProblem.old.state.core.current.environment authoredDecl = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def backReady := (prepareTable backCriterion [(authoredDecl,())]).get (by decide +kernel)
def backAuthor : Table := ⟨[rootEq,backEq,leafEq],[],[]⟩
def backAttached := (attach backProblem.state.base.core.current.ordinary backAuthor).get (by decide +kernel)
def backWire : BeforeCaptureWire :=
  ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,rootEq⟩,⟨1,1,backEq⟩,⟨2,2,leafEq⟩]⟩

def backOuter : Checkpoint 6 :=
  ⟨0,2,2,⟨#v[0,1],#v[.structural 0 [1],.structural 1 [0]],0⟩,
    ⟨#v[0,1],#v[.structural 0 [1],.structural 1 [0]]⟩⟩
def backInner : Checkpoint 6 :=
  ⟨1,2,2,⟨#v[1,0],#v[.structural 1 [1],.structural 0 [0]],0⟩,
    ⟨#v[0,1],#v[.structural 1 [1],.structural 0 [0]]⟩⟩

def stillActualNamedBeforeBack : Bool := Id.run do
  let read ← pure (readBeforeCapture (p := backProblem) backAttached backReady backWire)
  return read.any fun r =>
    (checkFixedFieldChoice476 r 30 [.payload]).any fun fixed =>
      (readNamedAtFixedChoice476 fixed q).isSome

def readBack : Option CheckedFieldBit := do
  let r ← readBeforeCapture (p := backProblem) backAttached backReady backWire
  let fixed ← checkFixedFieldChoice476 r 30 [.payload]
  let exact ← readNamedFieldQuotient476 fixed q ppPositions bisimPairs backOuter backInner
  pure exact.report

def twoBodies : List (CommonNominalSyntax.Layer Common.Row (Sum Nat (CommonNominalSyntax.State Common.Row))) :=
  [.record 30 (.inl 1) .emptyRecord,.record 40 (.inl 0) .emptyRecord]
def cycle30 : Ty := .record 30 (.block twoBodies 1) .emptyRecord
def cycle40 : Ty := .record 40 (.block twoBodies 0) .emptyRecord

theorem alt_cycle_left_stage476 : Equivalent cycle30 (record 30 cycle40 .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k cycle30 =
      CommonNominalFullCarrier.observeTy k (record 30 cycle40 .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

theorem alt_cycle_right_stage476 : Equivalent cycle40 (record 40 cycle30 .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k cycle40 =
      CommonNominalFullCarrier.observeTy k (record 40 cycle30 .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def backFit : I72.Model := ⟨fun n => (if n = 4 then cycle30 else if n = 6 then cycle40 else .emptyRecord,
  Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem genuine_cyclic_outer_blocks_the_named_field_report476 :
    FitsFull backProblem.state backFit ∧ stillActualNamedBeforeBack = true ∧
    LiteralVisits473.readCheck backProblem.old.state.core ppPositions bisimPairs (.logical 4) backOuter = some true ∧
    LiteralVisits473.readCheck backProblem.old.state.core ppPositions bisimPairs (.logical 6) backInner = some true ∧
    readBack = none := by
  constructor
  · refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro row h
      change row ∈ [rootEq,backEq,leafEq] at h
      rcases List.mem_cons.mp h with rfl | after
      · exact alt_cycle_left_stage476
      rcases List.mem_cons.mp after with rfl | last
      · exact alt_cycle_right_stage476
      · obtain rfl := List.mem_singleton.mp last
        exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · intro _ h; cases h
    · intro _ h; cases h
    · intro _ h; cases h
  · decide +kernel

/-- info: [true, true, true, false] -/
#guard_msgs in
#eval [stillActualNamedBeforeBack,
  LiteralVisits473.readCheck backProblem.old.state.core ppPositions bisimPairs (.logical 4) backOuter == some true,
  LiteralVisits473.readCheck backProblem.old.state.core ppPositions bisimPairs (.logical 6) backInner == some true,
  readBack.isSome]

#print axioms genuine_cyclic_outer_blocks_the_named_field_report476

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedQuotientActual476


namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedQuotientActual476
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open ObservationSyntax471
open InputCoordinates475
open PreparedDeclarations463
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open CommonNominalFullCarrier (Ty Equivalent record)
open GeneralDeclarativeHead320 (Equation)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

def unrolledLeaf : Equation := ⟨7,.record 40 (.variable 7) empty⟩
def unrolledRows : List Equation := [rootEq,namedEq false,unrolledLeaf]
def unrolledState : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,unrolledRows⟩
def pu : FullProblem := (buildProblem authoredDecl unrolledState).get (by decide +kernel)
def unrolledCriterion : CertificateProtocol pu.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = authoredDecl)
  sound := by
    intro d _ yes
    obtain rfl : d = authoredDecl := of_decide_eq_true yes
    have or : RecordTrail455.localAuthorBits pu.old.state.core.current.environment authoredDecl = true := by
      decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp or
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c absent; cases absent
def unrolledGD := (prepareTable unrolledCriterion [(authoredDecl,())]).get (by decide +kernel)
def unrolledAuthor : Table := ⟨unrolledRows,[],[]⟩
def unrolledAttached := (attach pu.state.base.core.current.ordinary unrolledAuthor).get (by decide +kernel)
def unrolledWire : BeforeCaptureWire :=
  ⟨⟨0,0⟩,⟨[71,2],218,0⟩,[⟨0,0,rootEq⟩,⟨1,1,namedEq false⟩,⟨2,2,unrolledLeaf⟩]⟩
def unrolledPositions : Positions 6 := ⟨
  #v[⟨.logical 4,0⟩,⟨.logical 6,1⟩,⟨.logical 7,2⟩,
    ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩],
  [.record [30],.record [40]],
  #v[cl 4,cl 6,cl 7,cl 4,cl 6,cl 7]⟩

def unrolledRel : List (Fin 6 × Fin 6) :=
  [(0,0),(0,3),(3,0),(3,3),
  (1,1),(1,2),(1,4),(1,5),(2,1),(2,2),(2,4),(2,5),
  (4,1),(4,2),(4,4),(4,5),(5,1),(5,2),(5,4),(5,5)]

def unrolledOuter : Checkpoint 6 :=
  ⟨0,3,2,⟨#v[0,1,2],#v[.structural 0 [1],.structural 1 [2],.structural 1 [2]],0⟩,
      ⟨#v[0,1,1],#v[.structural 0 [1],.structural 1 [1]]⟩⟩
def unrolledInner : Checkpoint 6 :=
  ⟨1,2,1,⟨#v[1,2],#v[.structural 1 [1],.structural 1 [1]],0⟩,
      ⟨#v[0,0],#v[.structural 1 [0]]⟩⟩

def runUnrolledAt (rel : List (Fin 6 × Fin 6)) : Option CheckedFieldBit := do
  let before ← readBeforeCapture (p := pu) unrolledAttached unrolledGD unrolledWire
  let fixed ← checkFixedFieldChoice476 before 30 [.payload]
  let answer ← readNamedFieldQuotient476 fixed q unrolledPositions rel unrolledOuter unrolledInner
  return answer.report

def unrolledFit : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 regular40 .emptyRecord else
      if n = 6 ∨ n = 7 then regular40 else .emptyRecord, Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem root_unrolled_actual_fits476 : FitsFull pu.state unrolledFit := by
  have rowFits : ∀ row ∈ pu.state.base.core.current.ordinary.equations,
      GeneralDeclarativeEntailment320.Holds unrolledFit.assignment row := by
    intro row h
    change row ∈ unrolledRows at h
    rcases List.mem_cons.mp h with rfl | first
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp first with rfl | next
    · exact regular40_exposes_one_fitting_step
    · obtain rfl := List.mem_singleton.mp next
      exact regular40_exposes_one_fitting_step
  refine ⟨⟨⟨⟨⟨?_,?_⟩,rowFits⟩,?_⟩,?_⟩,?_⟩ <;> intro _ h <;> cases h


def splitOnlyRawInner : Checkpoint 6 :=
  ⟨1,2,2,⟨#v[1,2],#v[.structural 1 [1],.structural 1 [1]],0⟩,
      ⟨#v[0,1],#v[.structural 1 [1],.structural 1 [1]]⟩⟩

def tryUnrolledAsTwoSemanticClasses : Option CheckedFieldBit := do
  let before ← readBeforeCapture (p := pu) unrolledAttached unrolledGD unrolledWire
  let fixed ← checkFixedFieldChoice476 before 30 [.payload]
  let answer ← readNamedFieldQuotient476 fixed q unrolledPositions unrolledRel unrolledOuter splitOnlyRawInner
  return answer.report

theorem root_unrolled_selected_name_checks_its_equal_cycle476 :
    FitsFull pu.state unrolledFit ∧
    runUnrolledAt unrolledRel = some (expected true) ∧
    tryUnrolledAsTwoSemanticClasses = none := by
  exact ⟨root_unrolled_actual_fits476,by decide +kernel,by decide +kernel⟩

def actualOneFieldNamedEdges476 : List (Nat × Nat) :=
  unrolledRows.filterMap fun row =>
    match row.right with
    | .record _ (.variable target) _ => some (row.left,target)
    | _ => none

theorem same_phase_unrolled_named_edges476 :
    actualOneFieldNamedEdges476 = [(4,6),(6,7),(7,7)] := rfl

inductive ActualPositivePhysicalPath476 : Nat → Nat → Prop
  | step {x y} : (x,y) ∈ actualOneFieldNamedEdges476 → ActualPositivePhysicalPath476 x y
  | tail {x y z} : ActualPositivePhysicalPath476 x y → (y,z) ∈ actualOneFieldNamedEdges476 →
      ActualPositivePhysicalPath476 x z

theorem selected_unrolled_name_has_no_physical_return476 :
    ¬ ActualPositivePhysicalPath476 6 6 := by
  intro path
  have start : ∀ k, ActualPositivePhysicalPath476 6 k → k = 7 := by
    intro k path
    induction path with
    | step h =>
      rw [same_phase_unrolled_named_edges476] at h
      simp at h
      exact h
    | tail _ h ih =>
      rw [same_phase_unrolled_named_edges476,ih] at h
      simp at h
      exact h
  exact (by decide : (6:Nat) ≠ 7) (start _ path)

theorem selected_unrolled_sources_have_no_raw_cycle_but_exact_quotient_k2476 :
    FitsFull pu.state unrolledFit ∧
    ¬ ActualPositivePhysicalPath476 6 6 ∧
    runUnrolledAt unrolledRel = some (expected true) ∧
    tryUnrolledAsTwoSemanticClasses = none := by
  exact ⟨root_unrolled_actual_fits476,selected_unrolled_name_has_no_physical_return476,
    root_unrolled_selected_name_checks_its_equal_cycle476.2⟩

#print axioms selected_unrolled_sources_have_no_raw_cycle_but_exact_quotient_k2476
#print axioms root_unrolled_selected_name_checks_its_equal_cycle476
/-- info: true -/
#guard_msgs in
#eval (runUnrolledAt unrolledRel).isSome
/-- info: false -/
#guard_msgs in
#eval tryUnrolledAsTwoSemanticClasses.isSome
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedQuotientActual476
