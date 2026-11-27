import Yulang.CommonRoleGraphBisimulation
import Yulang.GeneralDeclarativeI65I74LiteralFold471
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
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471.Actual
open Yulang.GeneralDeclarativeI65
open WrittenPattern460 (CoreState)
open RetainedFull445
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
def lastOpened : TyTerm Nat := .record 30 terminalTerm .emptyRecord
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
  .record 30 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])
def writtenCode : Expr := .record 30 (.record 40 (.variable 3) empty) empty
def physicallyInline : Equation := ⟨4,.record 30 (.record 40 (.variable 5) empty) empty⟩
def terminalRow : Equation := oneRow 5 40 5
def inlineRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[physicallyInline,terminalRow]⟩
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
def actualCap : Nat → GeneralDeclarativeWhere319.Capture := fun _ => point 5

theorem actual_written_closed_record_is_an_ordinary_source_head463 :
    Nonempty (SourceHead inlined.old.state.core inlined.old.root onlyDecl) := by
  refine ⟨.ordered actualCap (.cons (.ordinary ?_) .nil)⟩
  refine ⟨⟨Bound.refl _,Bound.refl _⟩,writtenCode,?_,.direct (.whole ?_)⟩
  · rfl
  · exact List.mem_cons_self

def model : I72.Model :=
  ⟨fun n => (if n = 4 then record 30 (mu 40) .emptyRecord else mu 40,Common.rowEmpty),
    fun _ => none,fun n => if n = 4 then some (.ordinary lastOpened)
      else if n = 5 then some (.ordinary terminalTerm) else none⟩

theorem actual_inline_source_model_fits_without_named_parent_row464 :
    FitsFull inlined.state model := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro row present
    change row ∈ [physicallyInline,terminalRow] at present
    rcases List.mem_cons.mp present with rfl | present
    · change Equivalent (record 30 (mu 40) .emptyRecord)
          (record 30 (record 40 (mu 40) .emptyRecord) .emptyRecord)
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30 (unfold_mu455 40) (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · obtain rfl := List.mem_singleton.mp present
      exact unfold_mu455 40
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

open Yulang.GeneralDeclarativeI65.I72.LiteralFold471

def wire : HeadWire := ⟨⟨0,0⟩,[.payload],⟨0,1,⟨⟨1,.same,5⟩,[],.same⟩⟩,40,3⟩

def exactReport : Report := ⟨[71,2],218,19,⟨0,0⟩,[.payload],4,30,5⟩

theorem exact_written_source_only_field_report :
    FitsFull inlined.state model ∧ checkHeadReport inlined preparedInlineTable wire exactReport = true ∧
    GeneralDeclarativeGraphRows321.shapeOf physicallyInline.right = none := by
  exact ⟨actual_inline_source_model_fits_without_named_parent_row464,by decide +kernel,rfl⟩

/-- info: [true, false, false, false, false, false, false] -/
#guard_msgs in
#eval [checkHeadReport inlined preparedInlineTable wire exactReport,
  checkHeadReport inlined preparedInlineTable { wire with path := [.tail] } exactReport,
  checkHeadReport inlined preparedInlineTable { wire with label := 30 } exactReport,
  checkHeadReport inlined preparedInlineTable { wire with binder := 5 } exactReport,
  checkHeadReport inlined preparedInlineTable { wire with source := ⟨1,0⟩ } exactReport,
  checkHeadReport inlined preparedInlineTable { wire with physical :=
    { wire.physical with pointOrdinal := 0 } } exactReport,
  checkHeadReport inlined preparedInlineTable wire { exactReport with occurrence := [71,3] }]

open GeneralDeclarativeOrigins321 (Origin Backed)

def sourceGate471 : SourceGate inlined where
  completed := fun _ => False
  ledger := ⟨fun eq role => eq = physicallyInline ∧ role = .source,
    by intro eq o h; rcases h with ⟨rfl,_⟩; exact List.mem_cons_self⟩
  Authenticates := fun occ i eq => occ = [71,2] ∧ i = 0 ∧ eq.left = 4 ∧ eq.right = physicallyInline.right
  Data := Unit
  verify := fun occ i eq _ => decide (occ = [71,2] ∧ i = 0 ∧ eq.left = 4) &&
    GeneralDeclarativeWitnessLiteral349.eqExpr eq.right physicallyInline.right
  exact := by
    intro occ i eq
    simp [GeneralDeclarativeWitnessLiteral349.eq_expr,and_assoc]
  source := by
    intro occ i eq h
    rcases eq with ⟨slot,code⟩
    rcases h with ⟨_,_,rfl,h⟩
    change code = physicallyInline.right at h
    cases h
    exact ⟨rfl,rfl⟩

def pendingGate471 : SourceGate inlined where
  completed := fun _ => False
  ledger := ⟨fun eq role => eq = physicallyInline ∧ role = .output 0,
    by intro eq o h; rcases h with ⟨rfl,_⟩; exact List.mem_cons_self⟩
  Authenticates := fun _ _ _ => False
  Data := Unit
  verify := fun _ _ _ _ => false
  exact := by intro; simp
  source := by intro q i eq none; exact none.elim

def sourceWire471 : SourceWire sourceGate471 := ⟨wire,0,()⟩
def sourceReport471 : SourceReport := ⟨exactReport,0⟩

theorem exact_source_only_report_requires_the_separate_ordinary_source_gate :
    checkSourceReport sourceGate471 preparedInlineTable sourceWire471 sourceReport471 = true ∧
    checkSourceReport pendingGate471 preparedInlineTable ⟨wire,0,()⟩ sourceReport471 = false ∧
    ¬Backed pendingGate471.ledger physicallyInline := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro existsSupport
  obtain ⟨o,h,availability⟩ := existsSupport
  change physicallyInline = physicallyInline ∧ o = .output 0 at h
  rw [h.2] at availability
  cases availability with
  | completed h => exact h

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [checkSourceReport sourceGate471 preparedInlineTable sourceWire471 sourceReport471,
  checkSourceReport pendingGate471 preparedInlineTable ⟨wire,0,()⟩ sourceReport471,
  checkSourceReport sourceGate471 preparedInlineTable {sourceWire471 with declarationOrdinal := 1} sourceReport471,
  checkSourceReport sourceGate471 preparedInlineTable sourceWire471 {sourceReport471 with declarationOrdinal := 1}]

#print axioms source_receipt_is_available_from_source
#print axioms unchecked_pending_row_cannot_be_a_source_receipt
#print axioms exact_source_only_report_requires_the_separate_ordinary_source_gate

#print axioms scoped_positive_exact_finite_source_report
#print axioms source_report_has_actual_literal_position_and_same_fit
#print axioms checked_report_pinpoints_receipt
#print axioms receipt_exact_selected_observations
#print axioms head_receipt_same_original_fit
#print axioms exact_written_source_only_field_report
end Yulang.GeneralDeclarativeI65.I72.LiteralFold471.Actual
