import Yulang.GeneralDeclarativeI65I74C332SourceErasure473
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.DuplicateInputCoordinates473
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
def oneRow (i field child : Nat) : Equation := ⟨i,.record field (.variable child) empty⟩
def terminalTerm : TyTerm Nat := .record 40 (.var 5) .emptyRecord
def lastOpened : TyTerm Nat := .record 30 (.record 31 (.record 40 (.var 6) .emptyRecord) .emptyRecord) .emptyRecord
def escape (here : Nat) (atSame reached : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = here || atSame.contains i then 0 else if reached.contains i then 1 else 2⟩
def recState (field : Nat) : CommonNominalSyntax.State Common.Row :=
  .block [.record field (.inl 0) .emptyRecord] 0
def mu (field : Nat) : Ty := .record field (recState field) .emptyRecord
theorem unfold_mu455 (f : Nat) :
    Equivalent (mu f) (record f (mu f) .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k (mu f) =
      CommonNominalFullCarrier.observeTy k (record f (mu f) .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [←each k]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each k]
    exact CommonNominalFullDemand.producerLe_refl _

def written : Pattern :=
  .record 30 (.record 31 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])
def writtenCode : Expr := .record 30 (.record 31 (.record 40 (.variable 3) empty) empty) empty
def physicallyInline : Equation := ⟨4,.record 30 (.record 31 (.record 40 (.variable 6) empty) empty) empty⟩
def terminalRow : Equation := oneRow 5 40 5
def secondDefinition : Equation := oneRow 6 40 6
def rawLink : Equation := ⟨6,.variable 5⟩
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physicallyInline,terminalRow,secondDefinition,rawLink,physicallyInline]⟩
def onlyDecl : Declaration := ⟨218,19,[written],[],[],[]⟩

def sourceOnlyInline : Option FullProblem := do
  let graph ← compile bodies
  let auth ← GeneralSourceMetadataBareBundle291.compile
    (let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
      ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
     ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[onlyDecl]⟩)
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,inlineRaw,[]⟩,List.replicate 20 [] ++ [[cov]],
    [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

def inlined : FullProblem := sourceOnlyInline.get (by decide +kernel)
def actualCap : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 6

theorem actual_written_closed_record_is_an_ordinary_source_head463 :
    Nonempty (SourceHead inlined.old.state.core inlined.old.root onlyDecl) := by
  refine ⟨.ordered actualCap (.cons (.ordinary ?_) .nil)⟩
  refine ⟨⟨Bound.refl _,Bound.refl _⟩,writtenCode,?_,.direct (.whole ?_)⟩
  · rfl
  · exact List.mem_cons_self

def model : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (record 31 (record 40 (mu 40) .emptyRecord) .emptyRecord) .emptyRecord else mu 40,Common.rowEmpty),
    fun _ => none,fun n => if n = 4 then some (.ordinary lastOpened)
      else if n = 5 then some (.ordinary terminalTerm) else none⟩

theorem actual_inline_source_model_fits_without_named_parent_row464 :
    FitsFull inlined.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro row present
    change row ∈ [physicallyInline,terminalRow,secondDefinition,rawLink,physicallyInline] at present
    rcases List.mem_cons.mp present with rfl | rest
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    rcases List.mem_cons.mp rest with rfl | rest
    · exact unfold_mu455 40
    rcases List.mem_cons.mp rest with rfl | rest
    · exact unfold_mu455 40
    · rcases List.mem_cons.mp rest with rfl | ending
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
      · obtain rfl := List.mem_singleton.mp ending
        exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro src present
    change src ∈ [⟨4,[402],.ordinary lastOpened⟩,⟨5,[402],.ordinary terminalTerm⟩] at present
    rcases List.mem_cons.mp present with rfl | present
    · rfl
    · obtain rfl := List.mem_singleton.mp present
      rfl
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
open GeneralDeclarativeTermWalk322 (Occurrence)
open ObservationSyntax471 (AttachedFieldWire472 gateFromAttachedAuthor472 readFieldOrigin readTyping)

def authorRows : Table := ⟨[physicallyInline,terminalRow,physicallyInline],[],[]⟩

def checkedUsesAt (rawOrdinal authorOrdinal : Nat) : Option (List Occurrence) := do
  let a ← attach inlined.state.base.core.current.ordinary authorRows
  let token : AttachedFieldWire472 := ⟨⟨0,0⟩,0,30,[.payload],rawOrdinal,authorOrdinal⟩
  let f ← readFieldOrigin (gateFromAttachedAuthor472 (p := inlined) a) preparedInlineTable (token.atGate a)
  let t ← readTyping f
  pure t.uses

theorem two_distinct_source_and_raw_addresses_really_store_the_same_input_row :
    inlined.state.base.core.current.ordinary.equations[0]? = some physicallyInline ∧
    inlined.state.base.core.current.ordinary.equations[4]? = some physicallyInline ∧
    authorRows.authored[0]? = some physicallyInline ∧
    authorRows.authored[2]? = some physicallyInline ∧
    FitsFull inlined.state model := by
  exact ⟨rfl,rfl,rfl,rfl,actual_inline_source_model_fits_without_named_parent_row464⟩

/-- info: [true, true, false, false, false, false] -/
#guard_msgs in
#eval [(checkedUsesAt 0 0).isSome,(checkedUsesAt 4 2).isSome,
  (checkedUsesAt 0 1).isSome,(checkedUsesAt 4 1).isSome,
  (checkedUsesAt 5 0).isSome,(checkedUsesAt 4 3).isSome]

def actualPayloadAtCapture (trace : Option (List Occurrence)) : Bool :=
  match trace with
  | some [⟨3,.actual,.variable 6⟩] => true
  | _ => false

/-- info: [true, true] -/
#guard_msgs in
#eval [(actualPayloadAtCapture (checkedUsesAt 0 0)),(actualPayloadAtCapture (checkedUsesAt 4 2))]

#print axioms two_distinct_source_and_raw_addresses_really_store_the_same_input_row

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473.DuplicateInputCoordinates473
