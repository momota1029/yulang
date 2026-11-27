import Yulang.GeneralDeclarativeI65I74LiteralCapturePullback466
import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65Heads367

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ShadowedCapture
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralSourceMetadataRows291 (Row)
open CommonNominalFullCarrier (Ty Equivalent record)
open Core.PresenceGeneration (TyTerm)
open AuthenticatedHop458 (Wire CycleWire)
open RecordK2412 (FieldCycleWire cycle_at_sound412)
open InlineStructuralPolicy458 (emptyPolicy)
open RoutedNominalPoint456 (cov)
open RetainedFull445 (FullProblem liftProblem)
open PreparedDeclarations463
open List410 (ExactEscapeWire)

private def empty : Expr := .primitive .emptyRecord []
private def mkNamed (x label child : Nat) : Equation := ⟨x,.record label (.variable child) empty⟩
private def rawSelf : Equation := mkNamed 5 40 5
private def inlineMid : Equation := ⟨6,.record 31 rawSelf.right empty⟩
private def inlineRoot : Equation := ⟨4,.record 30 (.variable 6) (.record 40 rawSelf.right empty)⟩
private def oldRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf]⟩

private def pattern : Pattern :=
  .record 30 (.var 33) (.record 30 (.var 999) (.record 40 (.var 3) (.app 9 [])))
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 (.var 6) (.record 40 syntax5 .emptyRecord)
private def native : List Origin :=
  [⟨4,[402],.ordinary syntax4⟩,⟨6,[402],.ordinary syntax6⟩,⟨5,[402],.ordinary syntax5⟩]

private def pairAt (s : GeneralDeclarativeHead320.State) : Option FullProblem := do
  let bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← compile bodies
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  let auth ← GeneralSourceMetadataBareBundle291.compile
    ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[declaration]⟩
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,List.replicate 20 [] ++ [[cov]],native,[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure (liftProblem ⟨⟨core,atlas⟩,⟨[71,2],⟨19,[point 4],[]⟩⟩⟩)

private def before : FullProblem := (pairAt oldRaw).get (by decide +kernel)

private theorem ready : DeclarationReady (authoredRegistry before.old.state.core.current) declaration := by
  have bits : RecordTrail455.localAuthorBits before.old.state.core.current.environment declaration = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp bits
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c absent
  cases absent

open Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose)

private def certified : CheckedTable before.state.base.core.current :=
  ⟨[declaration],fun _d mem => (List.mem_singleton.mp mem).symm ▸ ready⟩

private def legacySupport : Supported (ordinary before.old) (fun _ => False) :=
  ⟨fun e o => e ∈ oldRaw.equations ∧ o = .source,fun got => got.1⟩

private noncomputable def groundedRows : GeneralDeclarativeNestedView332.Sources (restriction legacySupport) :=
  ofRows oldRaw.equations (fun _ h => from_source _ ⟨h,rfl⟩)

open Yulang.C466LiteralCapturePullback (pullPos)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource)
open GeneralDeclarationPatterns (normalize covered)

private noncomputable def chosen :=
  readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0
private theorem chosenExists : chosen.isSome = true := by decide +kernel
private noncomputable def receipt := chosen.get chosenExists

theorem actual_compiler_capture_rebases_to_third_written_field_not_shadow :
    receipt.allocated.target = 7 ∧ receipt.allocated.rawOrdinal = 3 ∧
    receipt.allocated.captureOrdinal = 1 ∧
    receipt.allocated.written = [.tail,.payload] ∧
    receipt.allocated.captured.binder = 3 ∧
    pullPos receipt.original.orig.original receipt.allocated.written = some [.tail,.tail,.payload] := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem backed_raw_coordinate_replays_at_the_same_original_written_binder :
    receipt.allocated.after.equations[3]? = some ⟨7,receipt.allocated.captured.term⟩ ∧
      atSource receipt.original.orig.original [.tail,.tail,.payload] = some (.var 3) ∧
      atSource receipt.original.orig.original [.tail,.payload] = some (.var 999) := by
  have runs : readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0 = some receipt :=
    (Option.some_get chosenExists).symm
  have evidence := ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate
    before.old certified groundedRows ⟨0,0⟩ [] 0 receipt runs
  have ordinal : receipt.allocated.rawOrdinal = 3 := by decide +kernel
  have target : receipt.allocated.target = 7 := by decide +kernel
  refine ⟨?_,by decide +kernel,by decide +kernel⟩
  simpa only [ordinal,target] using evidence.2.2.1

private def recState : CommonNominalSyntax.State Common.Row :=
  .block [.record 40 (.inl 0) .emptyRecord] 0
private def mu : Ty := .record 40 recState .emptyRecord
private theorem unfolded : Equivalent mu (record 40 mu .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k mu =
      CommonNominalFullCarrier.observeTy k (record 40 mu .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [← each]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each]
    exact CommonNominalFullDemand.producerLe_refl _

private def midTy := record 31 mu .emptyRecord
private def rootTy := record 30 midTy (record 40 mu .emptyRecord)
private def concrete : I72.Model :=
  ⟨fun n => (if n = 4 then rootTy else if n = 6 then midTy else mu,Common.rowEmpty),
    fun _ => none,
    fun n => if n = 4 then some (.ordinary syntax4)
      else if n = 6 then some (.ordinary syntax6)
      else if n = 5 then some (.ordinary syntax5) else none⟩

theorem actual_shadowed_visible_source_has_a_real_fitting_model :
    FitsFull before.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [inlineRoot,inlineMid,rawSelf] at row
    rcases List.mem_cons.mp row with rfl|row
    · change Equivalent (record 30 midTy (record 40 mu .emptyRecord))
          (record 30 midTy (record 40 (record 40 mu .emptyRecord) .emptyRecord))
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
        (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 40 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))
    · rcases List.mem_cons.mp row with rfl|row
      · change Equivalent (record 31 mu .emptyRecord) (record 31 (record 40 mu .emptyRecord) .emptyRecord)
        exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
      · obtain rfl := List.mem_singleton.mp row
        exact unfolded
  · intro _ bad; cases bad
  · intro source here
    change source ∈ native at here
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad



/-- info: [true, true, true, true] -/
#guard_msgs in
#eval
  let r := readCaptureFromReadyHead before.old certified (ofRows oldRaw.equations (fun _ h => h)) ⟨0,0⟩ [] 0
  [r.any (fun a => a.allocated.target == 7 && a.allocated.rawOrdinal == 3 && a.allocated.captureOrdinal == 1),
   r.any (fun a => decide (a.allocated.written = [.tail,.payload])),
   r.any (fun a => decide (pullPos a.original.orig.original a.allocated.written = some [.tail,.tail,.payload])),
   r.any (fun a => a.allocated.captured.binder == 3)]

#print axioms actual_shadowed_visible_source_has_a_real_fitting_model
#print axioms actual_compiler_capture_rebases_to_third_written_field_not_shadow
#print axioms backed_raw_coordinate_replays_at_the_same_original_written_binder
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ShadowedCapture
