import Yulang.GeneralDeclarativeI65I74SelectedCaptureFootprint476
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
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

def sourceOnlyInline := buildProblem onlyDecl inlineRaw
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
def named : FullProblem := (buildProblem onlyDecl namedRaw).get (by decide +kernel)
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

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
open InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CertificateProtocol prepareTable)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open CommonNominalFullCarrier (record)

def doubleWritten : Pattern :=
  .record 30 (.record 40 (.var 3) (.app 9 []))
    (.record 31 (.record 40 (.var 8) (.app 9 [])) (.app 9 []))
def doubleDecl : Declaration := ⟨218,19,[doubleWritten],[],[],[]⟩
def doubleRoot : Equation := ⟨4,.record 30 (.variable 6) (.record 31 (.variable 6) empty)⟩
def doubleRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[doubleRoot,namedNext]⟩
def doubleP : FullProblem := (buildProblem doubleDecl doubleRaw).get (by decide +kernel)
def doublePrepared : CertificateProtocol doubleP.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = doubleDecl)
  sound := by
    intro d _ h
    have fits : d = doubleDecl := of_decide_eq_true h
    subst d
    have yes : RecordTrail455.localAuthorBits doubleP.old.state.core.current.environment doubleDecl = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp yes
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro c no; cases no
def doubleReady := (prepareTable doublePrepared [(doubleDecl,())]).get (by decide +kernel)
def doubleAuthor : Table := ⟨[doubleRoot,namedNext],[],[]⟩
def doubleAttached := (attach doubleP.state.base.core.current.ordinary doubleAuthor).get (by decide +kernel)
def doubleWire : BeforeCaptureWire := ⟨⟨0,0⟩,frameKey,[⟨0,0,doubleRoot⟩,⟨1,1,namedNext⟩]⟩
def doubleBefore := readBeforeCapture (p := doubleP) doubleAttached doubleReady doubleWire
def doubleMark := doubleBefore.bind readMarkedCapture

def reportOn (field : Nat) (path : List WrittenPattern460.PhysicalOrigin.Pose) :=
  doubleBefore.any fun r => (readBoundField r field path).isSome
def allMarks {rows : List StampedRead} (inferred : Option (Traced rows)) :=
  inferred.map (fun x => x.opened.map exposurePosition)
def doubleTy := record 40 .emptyRecord .emptyRecord
def doubleModel : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 doubleTy (record 31 doubleTy .emptyRecord)
    else if n = 6 then doubleTy else .emptyRecord,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem a_two_field_original_problem_has_a_genuine_fit : FitsFull doubleP.state doubleModel := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro eq h
    change eq ∈ [doubleRoot,namedNext] at h
    rcases List.mem_cons.mp h with rfl | other
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · obtain rfl := List.mem_singleton.mp other
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

theorem before_capture_marks_alone_cannot_recover_which_two_fields_was_requested :
    FitsFull doubleP.state doubleModel ∧
    allMarks doubleMark = some [(4,0,0),(6,1,1),(6,1,1)] ∧
    ¬ ∃ decoder : Option (List (Nat × Nat × Nat)) → Nat,
        decoder (allMarks doubleMark) = 30 ∧ decoder (allMarks doubleMark) = 31 := by
  refine ⟨a_two_field_original_problem_has_a_genuine_fit,
    by decide +kernel,?_⟩
  rintro ⟨f,left,right⟩
  have contra : 30 = 31 := left.symm.trans right
  omega

/-- info: [true, true, false, false] -/
#guard_msgs in
#eval [reportOn 30 [.payload],reportOn 31 [.tail,.payload],
  reportOn 30 [.tail,.payload],reportOn 31 [.payload]]

#print axioms before_capture_marks_alone_cannot_recover_which_two_fields_was_requested
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
open RetainedFull445 (FullProblem)
open InputCoordinates475
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationSyntax471 (FieldOrigin readDescription ReadsDescription description_exact
  RecordEntries Slot Label gateFromAttachedAuthor472 sortedFields sorted_fields_keep_exact_first_visible_entries)
open WrittenPattern460.PhysicalOrigin (Pose exact_original_occurrences)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open GeneralDeclarativeInspect321 (Inspects)

def beforeDouble := doubleBefore.get (by decide +kernel)
def q30 : Expr := .record 40 (.variable 3) empty
def q31 : Expr := .record 40 (.variable 8) empty
def p30 : Pattern := .record 40 (.var 3) (.app 9 [])
def p31 : Pattern := .record 40 (.var 8) (.app 9 [])
def qRows : List (Nat × Expr) := [(30,q30),(31,q31)]
def rRows : List (Nat × Expr) := [(30,.variable 6),(31,.variable 6)]
def qChildren := RecordEntries qRows
def rChildren := RecordEntries rRows
def qLabel : Label := .structural (.record ((sortedFields qRows).map Prod.fst))
def rLabel : Label := .structural (.record ((sortedFields rRows).map Prod.fst))

theorem exact_double_query_code :
    beforeDouble.head.orig.code = .record 30 q30 (.record 31 q31 empty) :=
  (eq_expr ..).mp (by decide +kernel)

theorem whole_query_described :
    ReadsDescription doubleP.old.state.core beforeDouble.head.orig.code qLabel qChildren := by
  rw [exact_double_query_code]
  exact .record (.field .empty)

theorem whole_raw_described :
    ReadsDescription doubleP.old.state.core doubleRoot.right rLabel rChildren :=
  .record (.field .empty)

private theorem a_field_of_these_rows_is_literal {rows : List (Nat × Expr)} {label : Nat} {q : Expr}
    (h : (label,q) ∈ CommonRoleCanonicalRows.normalize rows) :
    (.field label,q) ∈ RecordEntries rows :=
  List.mem_map.mpr ⟨(label,q),(sorted_fields_keep_exact_first_visible_entries rows _).mpr h,rfl⟩

def makeExactField (label : Nat) (path : List Pose) (chosen : Pattern) (query : Expr)
    (literal : WrittenPattern460.PhysicalOrigin.Origin beforeDouble.head.orig.original (.field label) path chosen)
    (compiled : AuthoredQuery doubleP.old.state.core (normalize chosen) query)
    (addressed : (.field label,query) ∈ qChildren) (nonvar : Inspects query)
    (rawChild : (.field label,.variable 6) ∈ rChildren) :
    FieldOrigin (gateFromAttachedAuthor472 (p := doubleP) doubleAttached) doubleReady
      ((exactFieldWire doubleWire beforeDouble.picked label path).atGate doubleAttached) := by
  refine ⟨beforeDouble.head,beforeDouble.address,?_,?_,chosen,literal,query,compiled,
    qLabel,qChildren,whole_query_described,addressed,nonvar,doubleRoot,?_,?_,?_,
    rLabel,rChildren,whole_raw_described,.variable 6,rawChild⟩
  · decide +kernel
  · have fact := (literal_frame_and_input_rows_before_any_capture beforeDouble).2.2.1
    exact fact
  · have fact := (literal_frame_and_input_rows_before_any_capture beforeDouble).2.2.2.1
    have own : beforeDouble.picked.row = doubleRoot := by decide +kernel
    exact fact.trans (congrArg some own)
  · decide +kernel
  · have fact := (literal_frame_and_input_rows_before_any_capture beforeDouble).2.2.2.1
    have own : beforeDouble.picked.row = doubleRoot := by decide +kernel
    exact ⟨rfl,fact.trans (congrArg some own),List.mem_cons_self⟩

def realWritten30 := makeExactField 30 [.payload] p30 q30
  (by
    have eq : beforeDouble.head.orig.original = doubleWritten := by decide +kernel
    rw [eq]
    exact .field)
  ((compile_query_exact ..).mp (by rfl))
  (a_field_of_these_rows_is_literal (by simp [qRows,CommonRoleCanonicalRows.normalize,CommonRoleCanonicalRows.residual]))
  .record
  (a_field_of_these_rows_is_literal (by simp [rRows,CommonRoleCanonicalRows.normalize,CommonRoleCanonicalRows.residual]))

def realWritten31 := makeExactField 31 [.tail,.payload] p31 q31
  (by
    have eq : beforeDouble.head.orig.original = doubleWritten := by decide +kernel
    rw [eq]
    exact .tail (by decide) .field)
  ((compile_query_exact ..).mp (by rfl))
  (a_field_of_these_rows_is_literal (by simp [qRows,CommonRoleCanonicalRows.normalize,CommonRoleCanonicalRows.residual]))
  .record
  (a_field_of_these_rows_is_literal (by simp [rRows,CommonRoleCanonicalRows.normalize,CommonRoleCanonicalRows.residual]))

theorem both_exact_original_field_receipts_replay_with_identical_mark_input :
    readBoundField beforeDouble 30 [.payload] = some realWritten30 ∧
    readBoundField beforeDouble 31 [.tail,.payload] = some realWritten31 ∧
    rootExposure ((readMarkedCapture beforeDouble).get (by decide +kernel)) = some (4,0,0) :=
  ⟨supplied_before_capture_replays_exact_original_field _ _ _ _,
   supplied_before_capture_replays_exact_original_field _ _ _ _,by decide +kernel⟩

theorem no_decoder_from_marks_of_actual_capture_returns_both_exact_literal_fields :
    FitsFull doubleP.state doubleModel ∧
    readBoundField beforeDouble 30 [.payload] = some realWritten30 ∧
    readBoundField beforeDouble 31 [.tail,.payload] = some realWritten31 ∧
    ¬ ∃ decoder : Option (List (Nat × Nat × Nat)) → (Nat × List Pose),
      decoder (allMarks doubleMark) = (30,[.payload]) ∧
      decoder (allMarks doubleMark) = (31,[.tail,.payload]) := by
  refine ⟨a_two_field_original_problem_has_a_genuine_fit,
    both_exact_original_field_receipts_replay_with_identical_mark_input.1,
    both_exact_original_field_receipts_replay_with_identical_mark_input.2.1,?_⟩
  rintro ⟨decode,first,last⟩
  exact before_capture_marks_alone_cannot_recover_which_two_fields_was_requested.2.2
    ⟨fun xs => (decode xs).1,congrArg Prod.fst first,congrArg Prod.fst last⟩

#print axioms both_exact_original_field_receipts_replay_with_identical_mark_input
#print axioms no_decoder_from_marks_of_actual_capture_returns_both_exact_literal_fields
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CertificateProtocol prepareTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeHead320 (Equation)
open InputCoordinates475

def unusedRow : Equation := ⟨90,empty⟩
def footprintRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[namedRoot,namedNext,unusedRow]⟩
def exactFootprintProblem : FullProblem := (buildProblem onlyDecl footprintRaw).get (by decide +kernel)
def footProtocol : CertificateProtocol exactFootprintProblem.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = onlyDecl)
  sound := by
    intro d _ h
    have eq : d = onlyDecl := of_decide_eq_true h
    subst d
    exact actual_checked_declaration_is_ready_even_in_inline_only_state463
def footReady := (prepareTable footProtocol [(onlyDecl,())]).get (by decide +kernel)
def footAuthor : Table := ⟨[namedRoot,namedNext,unusedRow],[],[]⟩
def footAttached := (attach exactFootprintProblem.state.base.core.current.ordinary footAuthor).get (by decide +kernel)
def footWire : BeforeCaptureWire :=
  ⟨⟨0,0⟩,frameKey,[⟨0,0,namedRoot⟩,⟨2,2,unusedRow⟩,⟨1,1,namedNext⟩]⟩

def exactlyFootprintOfActualRun : Option (List (Nat × Nat) × Bool) := do
  let initial ← readBeforeCapture (p := exactFootprintProblem) footAttached footReady footWire
  let _ ← readBoundField initial 30 [.payload]
  let seen ← readMarkedCapture initial
  let smaller := clippedWire footWire seen
  let back ← readBeforeCapture (p := exactFootprintProblem) footAttached footReady smaller
  let _ ← readBoundField back 30 [.payload]
  let result ← runAtBeforeCapture back
  return (smaller.offered.map (fun e => (e.raw,e.author)),
    match result.uses with
    | [⟨3,.actual,.variable 7⟩] => true
    | _ => false)

theorem real_footprint_input_has_unchanged_fitting_model_and_clips_only_unmarked :
    FitsFull exactFootprintProblem.state namedModel ∧
    exactlyFootprintOfActualRun = some ([(0,0),(1,1)],true) := by
  constructor
  · refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro eq h
      change eq ∈ [namedRoot,namedNext,unusedRow] at h
      rcases List.mem_cons.mp h with rfl | rest
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      rcases List.mem_cons.mp rest with rfl | last
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      · obtain rfl := List.mem_singleton.mp last
        exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · intro _ h; cases h
    · intro _ h; cases h
    · intro _ h; cases h
  · decide +kernel

/-- info: true -/
#guard_msgs in
#eval exactlyFootprintOfActualRun == some ([(0,0),(1,1)],true)
#print axioms real_footprint_input_has_unchanged_fitting_model_and_clips_only_unmarked
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
open InputCoordinates475
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)
open PreparedDeclarations463 (CertificateProtocol prepareTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)

def binderDecl : Declaration := ⟨218,19,[.var 3],[],[],[]⟩
def binderP : FullProblem := (buildProblem binderDecl namedRaw).get (by decide +kernel)
def binderProtocol : CertificateProtocol binderP.state.base.core.current where
  Data := Unit
  verify d _ := decide (d = binderDecl)
  sound := by
    intro d wire h
    have eq : d = binderDecl := of_decide_eq_true h
    subst d
    have yes : RecordTrail455.localAuthorBits binderP.old.state.core.current.environment binderDecl = true := by decide +kernel
    obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp yes
    refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
    intro u absent; cases absent

def binderReady := (prepareTable binderProtocol [(binderDecl,())]).get (by decide +kernel)
def binderAttached := (attach binderP.state.base.core.current.ordinary namedAuthor).get (by decide +kernel)

def actualBinderClip : Option (Nat × Bool) := do
  let r ← readBeforeCapture (p := binderP) binderAttached binderReady namedWire
  let trace ← readMarkedCapture r
  let smaller := clippedWire namedWire trace
  pure (smaller.offered.length,
    (readBeforeCapture (p := binderP) binderAttached binderReady smaller).isSome)

theorem before_capture_stamp_is_not_a_binding_site_decision :
    FitsFull binderP.state namedModel ∧ actualBinderClip = some (0,false) := by
  constructor
  · refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
    · intro _ h; cases h
    · intro _ h; cases h
    · intro eq h
      change eq ∈ [namedRoot,namedNext] at h
      rcases List.mem_cons.mp h with rfl | rest
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      · obtain rfl := List.mem_singleton.mp rest
        exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · intro _ h; cases h
    · intro _ h; cases h
    · intro _ h; cases h
  · decide +kernel

/-- info: true -/
#guard_msgs in
#eval actualBinderClip == some (0,false)

#print axioms before_capture_stamp_is_not_a_binding_site_decision
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.SelectedCaptureActual476
