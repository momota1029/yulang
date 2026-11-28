import Yulang.GeneralDeclarativeI65I74RootedInteriorReport483
import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.RootedInteriorActual483
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


open SourceExposure481.ClosedBank
open WrittenPattern460.PhysicalOrigin (Pose)
open LiteralVisits473 (StepWire)

def queryPattern : Pattern :=
  .record 30 (.record 40 (.record 50 (.record 61 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])) (.app 9 [])
def declaration : Declaration := ⟨218,19,[queryPattern],[],[],[]⟩
def rootRaw : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def wrap (e : Expr) : Expr := .record 61 e empty
def middle (e : Expr) : Expr := .record 50 e empty
def authoredRaw : Equation := ⟨6,.record 40 (middle (wrap (.variable 7))) empty⟩
def ambientRaw : Equation := ⟨6,.record 40 (middle (wrap (wrap (.variable 7)))) empty⟩
def recurrence : Equation := ⟨7,wrap (.variable 7)⟩
def rawOriginal : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRaw,authoredRaw,ambientRaw,recurrence]⟩
def problem : FullProblem := (buildProblem declaration rawOriginal).get (by decide +kernel)

def cert : CertificateProtocol problem.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = declaration)
  sound := by
    intro d _ yes
    obtain rfl : d = declaration := of_decide_eq_true yes
    have test : RecordTrail455.localAuthorBits problem.old.state.core.current.environment declaration = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp test
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c h; cases h

def gd := (prepareTable cert [(declaration,())]).get (by decide +kernel)
def table : Table := ⟨[rootRaw,authoredRaw],[(ambientRaw,99),(recurrence,99)],[]⟩

def clazz (n : Nat) : ClassWire :=
  ⟨[(n,.same)],⟨(List.range 8).map (fun i => if i = n then 1 else 0),[1]⟩⟩

def positions : Positions 12 :=
  ⟨#v[⟨.logical 4,0⟩,⟨.logical 6,2⟩,⟨.logical 7,3⟩,
      ⟨.rowPos 0 [],0⟩,⟨.rowPos 1 [],1⟩,⟨.rowPos 2 [],2⟩,
      ⟨.rowPos 1 [.field 40],1⟩,⟨.rowPos 2 [.field 40],2⟩,
      ⟨.rowPos 1 [.field 40,.field 50],1⟩,⟨.rowPos 2 [.field 40,.field 50],2⟩,
      ⟨.rowPos 2 [.field 40,.field 50,.field 61],2⟩,⟨.rowPos 3 [],3⟩],
    [.record [30],.record [40],.record [50],.record [61]],
    #v[clazz 4,clazz 6,clazz 7,clazz 4,clazz 6,clazz 6,clazz 6,clazz 6,clazz 6,clazz 6,clazz 6,clazz 7]⟩
def pairs : List (Fin 12 × Fin 12) :=
  ([[0,3],[1,4,5],[6,7],[2,8,9,10,11]] : List (List (Fin 12))).flatMap
    fun block => block.flatMap fun i => block.map fun j => (i,j)

def before : Checkpoint 12 :=
  ⟨1,5,3,⟨#v[1,7,9,10,2],#v[.structural 1 [1],.structural 2 [2],.structural 3 [3],.structural 3 [4],.structural 3 [4]],0⟩,
    ⟨#v[0,1,2,2,2],#v[.structural 1 [1],.structural 2 [2],.structural 3 [2]]⟩⟩
def between : Checkpoint 12 :=
  ⟨7,4,2,⟨#v[7,9,10,2],#v[.structural 2 [1],.structural 3 [2],.structural 3 [3],.structural 3 [3]],0⟩,
    ⟨#v[0,1,1,1],#v[.structural 2 [1],.structural 3 [1]]⟩⟩
def finish : Checkpoint 12 :=
  ⟨9,3,1,⟨#v[9,10,2],#v[.structural 3 [1],.structural 3 [2],.structural 3 [2]],0⟩,
    ⟨#v[0,0,0],#v[.structural 3 [0]]⟩⟩

def head : PrecheckedHead (p := problem.old) gd :=
  (readPrecheckedHead (p := problem.old) gd ⟨0,0⟩).get (by decide +kernel)
def root : Site problem.old.state.core positions :=
  ⟨0,head.orig.original,head.orig.code,rootRaw.right,rfl⟩
def ambient : Site problem.old.state.core positions :=
  (readHop root ⟨.field 30,[.payload]⟩ 1).get (by decide +kernel)

def card (raw : Nat) : ReadCard :=
  .record [⟨⟨raw,1⟩,[]⟩] [40] [(40,middle (wrap (.variable 3)))] empty
    (.cons (.record [] [50] [(50,wrap (.variable 3))] empty
      (.cons (.record [] [61] [(61,.variable 3)] empty
        (.cons .capture .nil) (.primitive .nil)) .nil) (.primitive .nil)) .nil) (.primitive .nil)

def outer : Checkpoint 12 :=
  ⟨0,6,4,⟨#v[0,1,7,9,10,2],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [4],.structural 3 [5],.structural 3 [5]],0⟩,
    ⟨#v[0,1,2,3,3,3],#v[.structural 0 [1],.structural 1 [2],.structural 2 [3],.structural 3 [3]]⟩⟩
def prior : PriorPhase := ⟨table,[],some [⟨0,0⟩,⟨1,1⟩]⟩
def rootCard : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩] [30] [(30,.record 40 (middle (wrap (.variable 3))) empty)] empty
    (.cons (card 1) .nil) (.primitive .nil)
def approachWire : NamedTerminalWire 12 :=
  ⟨0,0,outer,[],⟨.field 30,[.payload]⟩,before,rootCard,0,[outer]⟩
def phrase : RootedInteriorWire 12 :=
  ⟨approachWire,[(6,between,⟨.field 40,[.payload]⟩),(8,finish,⟨.field 50,[.payload]⟩)]⟩
def readAt := readRootedInterior problem gd positions pairs prior
def sameReport := (readAt phrase).map (·.report.outcome)

def controls := [
  sameReport == some ([.payload,.payload,.payload],[.field 30,.field 40,.field 50],.rowPos 2 [.field 40,.field 50],true),
  (readAt {phrase with after := [(7,between,⟨.field 40,[.payload]⟩),(8,finish,⟨.field 50,[.payload]⟩)]}).isNone,
  (readAt {phrase with after := [(6,between,⟨.field 40,[.tail]⟩),(8,finish,⟨.field 50,[.payload]⟩)]}).isNone,
  (readAt {phrase with approach := {approachWire with roots := []}}).isNone,
  (readAt {phrase with approach := {approachWire with initialAuthor := 1}}).isNone]

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval controls

def recursiveTy : Ty := .record 61 (.block [.record 61 (.inl 0) .emptyRecord] 0) .emptyRecord

theorem recursiveTy_unfolds : Equivalent recursiveTy (record 61 recursiveTy .emptyRecord) := by
  have eq (k : Nat) : CommonNominalFullCarrier.observeTy k recursiveTy =
      CommonNominalFullCarrier.observeTy k (record 61 recursiveTy .emptyRecord) := by cases k <;> rfl
  constructor
  · intro k; rw [←eq k]; exact CommonNominalFullDemand.producerLe_refl _
  · intro k; rw [eq k]; exact CommonNominalFullDemand.producerLe_refl _

def beforeTy : Ty := record 40 (record 50 recursiveTy .emptyRecord) .emptyRecord

def sameFit : I72.Model :=
  ⟨fun n => ((if n = 4 then record 30 beforeTy .emptyRecord
      else if n = 6 then beforeTy
      else if n = 7 then recursiveTy else .emptyRecord),Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem actual_rooted_interior_has_an_original_fit :
    FitsFull problem.state sameFit ∧ problem.old.root.demand.outputs = [] ∧
      ambientRaw ∉ table.authored ∧ (ambientRaw,99) ∈ table.produced ∧ 99 ∉ table.released := by
  refine ⟨?_,rfl,by decide +kernel,by decide +kernel,by decide⟩
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRaw,authoredRaw,ambientRaw,recurrence] at h
    have found : row = rootRaw ∨ row = authoredRaw ∨ row = ambientRaw ∨ row = recurrence := by
      simpa using h
    rcases found with rfl | rfl | rfl | rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · apply GeneralNominalCenteredHeadMatPatternSemantics.record_congr ..
      · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
          recursiveTy_unfolds (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · apply GeneralNominalCenteredHeadMatPatternSemantics.record_congr ..
      · exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans recursiveTy_unfolds
            (GeneralNominalCenteredHeadMatPatternSemantics.record_congr _
              recursiveTy_unfolds (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)))
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · exact recursiveTy_unfolds
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h


#print axioms actual_rooted_interior_has_an_original_fit
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.RootedInteriorActual483
