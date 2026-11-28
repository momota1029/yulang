import Yulang.GeneralDeclarativeI65I74FixedNamedSourceChoice476
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
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
def frameKey : FrameKey := ⟨[71,2],218,0⟩
def namedNext : Equation := ⟨6,.record 40 (.variable 7) empty⟩
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
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


end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
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


def fixed30 : FixedFieldChoice476 beforeDouble := ⟨30,[.payload],realWritten30⟩
def fixed31 : FixedFieldChoice476 beforeDouble := ⟨31,[.tail,.payload],realWritten31⟩
def want30 : NamedSelectionWire476 := ⟨30,[.payload],1⟩
def want31 : NamedSelectionWire476 := ⟨31,[.tail,.payload],2⟩

def selectedNamed {q : NamedSelectionWire476} (chosen : Option (NamedSelection476 beforeDouble q)) :
    Option (List QueryStep476 × (Nat × Nat × Nat) × List Pose) :=
  chosen.map fun r => (r.mark.path,exposurePosition r.mark.exposure,q.writtenPath)

def select30 := selectedNamed (readNamedAtFixedChoice476 fixed30 want30)
def select31 := selectedNamed (readNamedAtFixedChoice476 fixed31 want31)

def checkedControls : List Bool :=
  [(select30 == some ([.field 30],(6,1,1),[.payload])),
   (select31 == some ([.field 31],(6,1,1),[.tail,.payload])),
   (readNamedAtFixedChoice476 fixed30 want31).isSome,
   (readNamedAtFixedChoice476 fixed31 want30).isSome,
   (readNamedAtFixedChoice476 fixed30 {want30 with markOrdinal := 2}).isSome,
   (readNamedAtFixedChoice476 fixed31 {want31 with markOrdinal := 1}).isSome,
   (readNamedAtFixedChoice476 fixed30 {want30 with writtenPath := [.tail,.payload]}).isSome,
   (readNamedAtFixedChoice476 fixed31 {want31 with writtenPath := [.payload]}).isSome,
   (readNamedAtFixedChoice476 fixed30 {want30 with markOrdinal := 0}).isSome]

theorem both_independent_old_choices_still_replay_on_one_fitting_input476 :
    FitsFull doubleP.state doubleModel ∧
    checkFixedFieldChoice476 beforeDouble 30 [.payload] = some fixed30 ∧
    checkFixedFieldChoice476 beforeDouble 31 [.tail,.payload] = some fixed31 ∧
    readNamedAtFixedChoice476 fixed30 want31 = none ∧
    readNamedAtFixedChoice476 fixed31 want30 = none :=
  ⟨a_two_field_original_problem_has_a_genuine_fit,
   original_fixed_field_replays_in_same_input476 fixed30,
   original_fixed_field_replays_in_same_input476 fixed31,
   wrong_original_label_or_path_cannot_use_a_fixed_receipt476 fixed30 want31 (.inl (by decide)),
   wrong_original_label_or_path_cannot_use_a_fixed_receipt476 fixed31 want30 (.inl (by decide))⟩

/-- info: [true, true, false, false, false, false, false, false, false] -/
#guard_msgs in
#eval checkedControls

#print axioms both_independent_old_choices_still_replay_on_one_fitting_input476
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.NamedSourceChoiceActual476
