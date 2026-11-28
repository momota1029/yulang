import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482
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

import Yulang.GeneralDeclarativeI65I74ChildOrdinal483

/-! Two distinct original written fields can lead to one physical child
of the old graph. The written outer order here is 50 then 30, whereas
the observation graph labels are sorted. Neither the child index nor
the true terminal bit chooses the written field, path or binder.
This is a local exact-route control, not a choice of resolution order. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.TwoFieldsSameRawChild483
open RetainedFull445
open LiteralVisits473 (Checkpoint StepWire)

open Producer479 (RouteWire readRoute)
open ObservationAlternatives473 (Positions Place graphOf)
open ObservationRawAlias471 (ClassWire)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty record)
open CommonRoleRegularGraph (successors)
open GeneralDeclarations (Declaration)
open PreparedDeclarations463

open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open RoutedNominalPoint456 (cov)
open CommonNominalFullCarrier (Equivalent)

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

def cyclicTy : Ty := .record 40 (.block [.record 40 (.inl 0) .emptyRecord] 0) .emptyRecord

theorem cyclicTy_step : Equivalent cyclicTy (record 40 cyclicTy .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k cyclicTy =
      CommonNominalFullCarrier.observeTy k (record 40 cyclicTy .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def child (binder : Nat) : Pattern := .record 40 (.var binder) (.app 9 [])
def bothWritten : Pattern := .record 50 (child 3) (.record 30 (child 4) (.app 9 []))
def writtenDecl : Declaration := ⟨218,19,[bothWritten],[],[],[]⟩
def rootEq : Equation := ⟨4,.record 50 (.variable 6) (.record 30 (.variable 6) empty)⟩
def childEq : Equation := ⟨6,.record 40 (.variable 6) empty⟩
def rawSnap : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootEq,childEq]⟩
def actual : FullProblem := (buildProblem writtenDecl rawSnap).get (by decide +kernel)
def protocol : CertificateProtocol actual.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = writtenDecl)
  sound := by
    intro d _ yes
    obtain rfl : d=writtenDecl := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits actual.old.state.core.current.environment writtenDecl = true := by
      decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c impossible; cases impossible

def checked := (prepareTable protocol [(writtenDecl,())]).get (by decide +kernel)
def cl (n : Nat) : ClassWire :=
  ⟨[(n,.same)],⟨(List.range 7).map (fun k => if k = n then 1 else 0),[1]⟩⟩
def positions : Positions 4 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,1⟩,⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩],
    [.record [30,50],.record [40]], #v[cl 4,cl 6,cl 4,cl 6]⟩
def relation : List (Fin 4 × Fin 4) := [(0,0),(0,2),(2,0),(2,2),(1,1),(1,3),(3,1),(3,3)]
def r0 : Checkpoint 4 :=
  ⟨0,2,2,⟨#v[0,1],#v[.structural 0 [1,1],.structural 1 [1]],0⟩,
    ⟨#v[0,1],#v[.structural 0 [1,1],.structural 1 [1]]⟩⟩
def r1 : Checkpoint 4 :=
  ⟨1,1,1,⟨#v[1],#v[.structural 1 [0]],0⟩,⟨#v[0],#v[.structural 1 [0]]⟩⟩
def move50 : StepWire := ⟨.field 50,[.payload]⟩
def move30 : StepWire := ⟨.field 30,[.tail,.payload]⟩
def routeAt (w : StepWire) : RouteWire 4 := ⟨0,0,⟨r0,[(w,r1)]⟩⟩
def signedOut (w : StepWire) :=
  (readRoute actual checked positions relation (routeAt w)).map fun x => x.outcome

theorem exact_sorted_two (a b : Expr) :
    ObservationSyntax471.sortedFields [(50,a),(30,b)] = [(30,b),(50,a)] := by
  simp [ObservationSyntax471.sortedFields,CommonRoleCanonicalRows.normalize,CommonRoleCanonicalRows.residual]

theorem original_raw_children_are_the_two_literal_aliases :
    ObservationSyntax471.readDescription actual.old.state.core rootEq.right =
      some (.structural (.record [30,50]),[(.field 30,.variable 6),(.field 50,.variable 6)]) := by
  simp only [rootEq,ObservationSyntax471.readDescription,ObservationSyntax471.literalFields,empty,
    Option.map_some, exact_sorted_two]
  rfl

theorem old_actual_root_has_two_successor_positions_with_one_node :
    successors (graphOf actual.old.state.core positions) 0 = [1,1] := by
  have rootRead : ObservationAlternatives473.readTermAt actual.old.state.core positions 0 = some rootEq.right := by rfl
  have node : ObservationAlternatives473.readNodeAt actual.old.state.core positions 0 =
      some (.structural 0 [1,1]) := by
    unfold ObservationAlternatives473.readNodeAt
    simp only [rootRead, bind, Option.bind, original_raw_children_are_the_two_literal_aliases]
    rfl
  simp [successors,graphOf,node]

#print axioms old_actual_root_has_two_successor_positions_with_one_node
def preparedHead := (readPrecheckedHead (p := actual.old) checked ⟨0,0⟩).get (by decide +kernel)
def childMatchedBinder (w : StepWire) (binder : Nat) : Bool :=
  ((LiteralVisits473.readLiteralVisitStep actual.old.state.core preparedHead.orig.original preparedHead.orig.code
    rootEq.right w).map fun expected =>
      GeneralDeclarativeWitnessLiteral349.eqExpr expected.childQuery
        (.record 40 (.variable binder) empty)).getD false

/-- info: [true, true, true, false, false, true, true, false, false] -/
#guard_msgs in
#eval [(successors (graphOf actual.old.state.core positions) 0).map Fin.val == [1,1],
  signedOut move50 == some ([.payload],[.field 50],.logical 6,true),
  signedOut move30 == some ([.tail,.payload],[.field 30],.logical 6,true),
  (signedOut ⟨.field 30,[.payload]⟩).isSome,
  (signedOut ⟨.field 50,[.tail,.payload]⟩).isSome,
  childMatchedBinder move50 3,childMatchedBinder move30 4,
  childMatchedBinder move50 4,childMatchedBinder move30 3]

def value (n : Nat) : Ty :=
  if n = 4 then record 50 cyclicTy (record 30 cyclicTy .emptyRecord)
  else if n = 6 then cyclicTy else .emptyRecord

def sameFit : I72.Model := ⟨fun n => (value n,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem actual_matches_one_original_model : FitsFull actual.state sameFit := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootEq,childEq] at h
    have which : row=rootEq ∨ row=childEq := by simpa using h
    rcases which with rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact cyclicTy_step
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

theorem no_raw_target_only_function_recovers_both_written_poses
    (pick : Fin 4 → List WrittenPattern460.PhysicalOrigin.Pose) :
    ¬ (pick r1.which = move50.written ∧ pick r1.which = move30.written) := by
  intro h
  have falsePose := h.1.symm.trans h.2
  change [WrittenPattern460.PhysicalOrigin.Pose.payload] = [.tail,.payload] at falsePose
  cases falsePose

#print axioms actual_matches_one_original_model
#print axioms no_raw_target_only_function_recovers_both_written_poses
end Yulang.GeneralDeclarativeI65.I72.TwoFieldsSameRawChild483
