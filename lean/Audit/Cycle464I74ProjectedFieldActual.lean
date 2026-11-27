import Yulang.GeneralDeclarativeI65I74SameRawProgram462
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualPhaseAudit
open Yulang.GeneralDeclarativeI65
open WrittenPattern460 (CoreState)
open InstalledProtocolSum462
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
open Derivation

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

def independentlyNamed : Equation := oneRow 4 30 5
def extendedOrdinary : GeneralDeclarativeHead320.State :=
  {inlineRaw with equations := inlineRaw.equations ++ [independentlyNamed]}

def independentSnapshot : FullProblem :=
  let before := inlined.old.state.core
  let switched : CoreState := {before with current := {before.current with ordinary := extendedOrdinary}}
  let atlas : B6OccurrenceAtlas401 switched := ⟨fun _ _ _ _ => none⟩
  liftProblem ⟨⟨switched,atlas⟩,inlined.root⟩

def givenPhysical (u : FullProblem) (row : Nat) : HeadFieldWire u.old :=
  let spine : Wire emptyPolicy :=
    .down ⟨row,.same,.field 0 0,(.field ⟨0,1,0,.same⟩ : InlineStructuralPolicy458.Ticket)⟩ (escape 4 [] [5]) .stop
  let cycle : FieldCycleWire := ⟨⟨1,.same,5⟩,[],.same⟩
  ⟨⟨0,0⟩,(onOldCursor u.old .plain 9 ⟨spine,cycle⟩).along⟩


def phases : SnapshotPair := ⟨inlined,independentSnapshot,rfl,rfl⟩

def equality : EqWire :=
  .compose (.old (.currentRow 0))
    (.record 30 (.reverse (.old (.currentRow 1))) (.old (.refl empty)))

def cut : ProjectionWire := ⟨equality,escape 4 [] [5]⟩
def actualWire : ProjectionFieldWire phases := ⟨cut,0,givenPhysical phases.after 2⟩
def exactNamedReceipt := readProjectionField phases preparedInlineTable 4 actualWire
def expected : Bool := exactNamedReceipt.any fun r =>
  r.field.path == [(.field 30,5)] && r.field.rows == [2] && r.field.literal.length == 1 &&
  r.field.terminal == 5 && r.field.stamp && r.hop == 0

theorem same_fitting_assignments_carry_actual_projection_native_receipt :
    (∀ m, FitsFull inlined.state m ↔ FitsFull independentSnapshot.state m) ∧
      FitsFull independentSnapshot.state model ∧ expected = true := by
  have accepted : checkProjection phases.pre phases.post 4 cut = true := by decide +kernel
  have correct := (independent_one_row_projection_iff_finite_data ..).mp ⟨cut,accepted⟩
  have frame : SameFitFrame phases.before.state phases.after.state :=
    unchanged_empty_retention_frame rfl rfl rfl rfl
  have allFits := exact_projection_transfers_full_fits_under_same_stored_frame correct frame
  exact ⟨allFits,(allFits model).mp actual_inline_source_model_fits_without_named_parent_row464,by decide +kernel⟩

def noIssuedSource : FullProblem :=
  let before := independentSnapshot.old.state.core
  let without : CoreState := {before with origins := []}
  let atlas : B6OccurrenceAtlas401 without := ⟨fun _ _ _ _ => none⟩
  liftProblem ⟨⟨without,atlas⟩,independentSnapshot.root⟩

def missingPhase : SnapshotPair := ⟨inlined,noIssuedSource,rfl,rfl⟩

theorem actual_same_model_raw_row_and_readiness_without_issuer :
    FitsFull noIssuedSource.state model ∧ checkProjection missingPhase.pre missingPhase.post 4 cut = true ∧
      (readPrecheckedHead (p := missingPhase.after.old)
        (missingPhase.afterTable preparedInlineTable) ⟨0,0⟩).isSome = true := by
  exact ⟨⟨⟨same_fitting_assignments_carry_actual_projection_native_receipt.2.1.1.1,
    by intro _ bad; cases bad⟩,by intro _ bad; cases bad⟩,by decide +kernel,by decide +kernel⟩

theorem missing_actual_issuer_refuses_every_projection_wire
    (w : ProjectionFieldWire missingPhase) :
    readProjectionField missingPhase preparedInlineTable 4 w = none := by
  cases ok : readProjectionField missingPhase preparedInlineTable 4 w with
  | none => rfl
  | some r =>
    exfalso
    have checked := (exact_projected_field_iff_finite_checked_wire ..).mpr ⟨w,ok⟩
    obtain ⟨a,last,_,trail,term,_,_⟩ := checked.2.1
    rw [without_issued_origin_a_finite_existing_trail_can_only_stop rfl trail] at term
    simp [RoutedMixed456.endsAtField] at term

/-- info: [true, false, false, false, false, false] -/
#guard_msgs in
#eval [expected,
  (readProjectionField phases preparedInlineTable 5 actualWire).isSome,
  (readProjectionField phases preparedInlineTable 4 {actualWire with hop := 1}).isSome,
  (readProjectionField phases preparedInlineTable 4 {actualWire with field := givenPhysical phases.after 0}).isSome,
  (readProjectionField phases preparedInlineTable 4 {actualWire with projection := ⟨.old (.currentRow 1),cut.cut⟩}).isSome,
  (readProjectionField missingPhase preparedInlineTable 4 ⟨cut,0,givenPhysical missingPhase.after 2⟩).isSome]

#print axioms actual_written_closed_record_is_an_ordinary_source_head463
#print axioms actual_inline_source_model_fits_without_named_parent_row464
#print axioms actual_checked_declaration_is_ready_even_in_inline_only_state463
#print axioms same_fitting_assignments_carry_actual_projection_native_receipt
#print axioms actual_same_model_raw_row_and_readiness_without_issuer
#print axioms missing_actual_issuer_refuses_every_projection_wire

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualPhaseAudit
