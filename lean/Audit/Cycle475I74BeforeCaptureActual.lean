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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.BeforeCaptureActual475
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
def written : Pattern := .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])
def physical : Equation := ⟨4,.record 30 (.record 40 (.variable 6) empty) empty⟩
def other : Equation := ⟨5,empty⟩
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physical,other,physical]⟩
def onlyDecl : Declaration := ⟨218,19,[written],[],[],[]⟩

def buildProblem (physicalState : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    (let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
      ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
     ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[onlyDecl]⟩)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,physicalState,[]⟩,List.replicate 20 [] ++ [[cov]],
    [],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

def sourceOnlyInline := buildProblem inlineRaw
def inlined : FullProblem := sourceOnlyInline.get (by decide +kernel)
def model : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 40 .emptyRecord .emptyRecord) .emptyRecord
    else .emptyRecord,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem before_capture_actual_problem_fits :
    FitsFull inlined.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro row present
    change row ∈ [physical,other,physical] at present
    rcases List.mem_cons.mp present with rfl | rest
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp rest with rfl | rest
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · obtain rfl := List.mem_singleton.mp rest
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro _ bad; cases bad

theorem actual_checked_declaration_is_ready_even_in_inline_only_state463 :
    DeclarationReady (authoredRegistry inlined.old.state.core.current) onlyDecl := by
  have exact : RecordTrail455.localAuthorBits inlined.old.state.core.current.environment onlyDecl = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp exact
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c appears
  cases appears

def inlinePreparedProtocol : CertificateProtocol inlined.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = onlyDecl)
  sound := fun _ _ chosen => (of_decide_eq_true chosen).symm ▸
    actual_checked_declaration_is_ready_even_in_inline_only_state463

def preparedInlineTable := (prepareTable inlinePreparedProtocol [(onlyDecl,())]).get (by decide +kernel)

theorem exact_inline_candidate_is_really_prechecked463 :
    (readPrecheckedHead (p := inlined.old) preparedInlineTable ⟨0,0⟩).isSome = true := by
  decide +kernel


open GeneralDeclarativeWitnessOrigins350 (Table attach)
open InputCoordinates475
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)

def authorRows : Table := ⟨[physical,other,physical],[],[]⟩
def attachedRows := (attach inlined.state.base.core.current.ordinary authorRows).get (by decide +kernel)
def frameKey : FrameKey := ⟨[71,2],218,0⟩
def left : BeforeCaptureWire := ⟨⟨0,0⟩,frameKey,[⟨0,0,physical⟩,⟨2,2,physical⟩]⟩
def right : BeforeCaptureWire := ⟨⟨0,0⟩,frameKey,[⟨2,2,physical⟩,⟨0,0,physical⟩]⟩

def checkActual (w : BeforeCaptureWire) (label : Nat) : Option (Nat × Nat × Bool) := do
  let r ← readBeforeCapture (p := inlined) attachedRows preparedInlineTable w
  let f ← readBoundField r label [.payload]
  pure (r.picked.raw,r.picked.author,(readTyping f).isSome)

def testCases : List Bool :=
  [checkActual left 30 == some (0,0,true),
   checkActual right 30 == some (2,2,true),
   (checkActual { left with frame := ⟨[71,3],218,0⟩ } 30).isSome,
   (checkActual { left with frame := ⟨[71,2],219,0⟩ } 30).isSome,
   (checkActual { left with frame := ⟨[71,2],218,1⟩ } 30).isSome,
   (checkActual { left with offered := [⟨1,0,physical⟩] } 30).isSome,
   (checkActual { left with offered := [⟨0,1,physical⟩] } 30).isSome,
   (checkActual left 40).isSome]

/-- info: [true, true, false, false, false, false, false, false] -/
#guard_msgs in
#eval testCases

theorem actual_before_capture_bound_to_old_field_in_same_problem :
    FitsFull inlined.state model ∧
    inlined.root.demand.outputs = [] ∧
    testCases = [true,true,false,false,false,false,false,false] := by
  exact ⟨before_capture_actual_problem_fits,rfl,by decide +kernel⟩

#print axioms actual_before_capture_bound_to_old_field_in_same_problem
open GeneralDeclarativeTermWalk322 (Occurrence)

def capturesBefore (wire : BeforeCaptureWire) : Option (List Occurrence) := do
  let r ← readBeforeCapture (p := inlined) attachedRows preparedInlineTable wire
  let visited ← runAtBeforeCapture r
  pure visited.uses

def actualBinder : Option (List Occurrence) → Bool
  | some [⟨3,.actual,.variable 6⟩] => true
  | _ => false

theorem actual_capture_executes_on_the_same_no_output_problem :
    actualBinder (capturesBefore left) = true ∧
    actualBinder (capturesBefore right) = true ∧
    (capturesBefore { left with offered := [⟨1,1,other⟩] }).isSome = false := by
  decide +kernel

/-- info: [true, true, false] -/
#guard_msgs in
#eval [actualBinder (capturesBefore left),actualBinder (capturesBefore right),
  (capturesBefore { left with offered := [⟨1,1,other⟩] }).isSome]

#print axioms actual_capture_executes_on_the_same_no_output_problem
/-- The old one-owner typing cut and the full independently supplied
source list are not interchangeable once a genuine named continuation is
visited. Both procedures below use exactly the same original problem. -/
def namedRoot : Equation := ⟨4,.record 30 (.variable 6) empty⟩
def namedNext : Equation := ⟨6,.record 40 (.variable 7) empty⟩
def namedRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[namedRoot,namedNext]⟩
def named : FullProblem := (buildProblem namedRaw).get (by decide +kernel)
def namedProtocol : CertificateProtocol named.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = onlyDecl)
  sound := by
    intro d wire chosen
    have name : d = onlyDecl := of_decide_eq_true chosen
    have original := actual_checked_declaration_is_ready_even_in_inline_only_state463
    subst d
    exact original
def namedReady := (prepareTable namedProtocol [(onlyDecl,())]).get (by decide +kernel)
def namedAuthor : Table := ⟨[namedRoot,namedNext],[],[]⟩
def namedAttached := (attach named.state.base.core.current.ordinary namedAuthor).get (by decide +kernel)
def namedWire : BeforeCaptureWire := ⟨⟨0,0⟩,frameKey,[⟨0,0,namedRoot⟩,⟨1,1,namedNext⟩]⟩
def namedBefore := readBeforeCapture (p := named) namedAttached namedReady namedWire
def namedOldHasField := namedBefore.any fun r => (readBoundField r 30 [.payload]).isSome
def namedOldSingleRow := namedBefore.any fun r =>
  (readBoundField r 30 [.payload]).any fun f => (readTyping f).isSome
def namedWholeCapture : Bool := namedBefore.any fun r =>
  match (runAtBeforeCapture r).map PinnedCapture.uses with
  | some [⟨3,.actual,.variable 7⟩] => true
  | _ => false

def namedModel : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 40 .emptyRecord .emptyRecord) .emptyRecord
    else if n = 6 then record 40 .emptyRecord .emptyRecord
    else .emptyRecord,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem named_actual_same_input_state_fits : FitsFull named.state namedModel := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro eq h
    change eq ∈ [namedRoot,namedNext] at h
    rcases List.mem_cons.mp h with rfl | other
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · obtain rfl := List.mem_singleton.mp other
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

theorem show_real_named_continuation_needs_more_than_the_first_row :
    FitsFull named.state namedModel ∧ named.root.demand.outputs = [] ∧
    namedOldHasField = true ∧ namedOldSingleRow = false ∧ namedWholeCapture = true := by
  exact ⟨named_actual_same_input_state_fits,rfl,by decide +kernel⟩

/-- info: [true, false, true] -/
#guard_msgs in
#eval [namedOldHasField,namedOldSingleRow,namedWholeCapture]

#print axioms show_real_named_continuation_needs_more_than_the_first_row

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.BeforeCaptureActual475
