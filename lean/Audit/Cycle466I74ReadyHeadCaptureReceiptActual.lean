import Yulang.GeneralDeclarativeI65I74LiteralSuppliedProjection464
import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65Heads367

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ReadyCapture
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
private def inlineRoot : Equation := ⟨4,.record 30 inlineMid.right empty⟩
private def oldRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf]⟩

private def pattern : Pattern :=
  .record 30 (.record 31 (.var 3) (.app 9 [])) (.app 9 [])
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 syntax6 .emptyRecord
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

private structure KeySummary where
  decl : Nat
  target : Nat
  raw : Nat
  occurrence : Nat
  path : List Pose
  binder : Nat
  deriving DecidableEq

private def reduced (found : CheckedCaptureHead before.old certified) : KeySummary :=
  ⟨found.original.orig.declaration.id,found.allocated.target,found.allocated.rawOrdinal,
    found.allocated.captureOrdinal,found.allocated.written,found.allocated.captured.binder⟩

private noncomputable def accepted :=
  (readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0).map reduced

theorem actual_prechecked_native_request_has_the_exact_old_ordinary_capture_receipt :
    accepted = some ⟨218,7,3,0,[Pose.payload,Pose.payload],3⟩ := by
  decide +kernel

private def missingGD : CheckedTable before.state.base.core.current :=
  ⟨[],fun _ not => False.elim (List.not_mem_nil not)⟩
private def routable := ofRows (s := oldRaw) oldRaw.equations (fun _ h => h)

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [
  decide ((readCaptureFromReadyHead before.old certified routable ⟨0,0⟩ [] 0).map reduced =
    some ⟨218,7,3,0,[Pose.payload,Pose.payload],3⟩),
  (readCaptureFromReadyHead before.old certified routable ⟨0,1⟩ [] 0).isNone,
  (readCaptureFromReadyHead before.old missingGD routable ⟨0,0⟩ [] 0).isNone,
  (readCaptureFromReadyHead before.old certified routable ⟨0,0⟩ [] 1).isNone,
  (readCaptureFromReadyHead before.old certified (ofRows (s := oldRaw) [] (fun _ h => False.elim (List.not_mem_nil h))) ⟨0,0⟩ [] 0).isNone]

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
private def rootTy := record 30 midTy .emptyRecord
private def concrete : I72.Model :=
  ⟨fun n => (if n = 4 then rootTy else if n = 6 then midTy else mu,Common.rowEmpty),
    fun _ => none,
    fun n => if n = 4 then some (.ordinary syntax4)
      else if n = 6 then some (.ordinary syntax6)
      else if n = 5 then some (.ordinary syntax5) else none⟩

theorem actual_prechecked_input_with_capture_has_a_real_fitting_model :
    FitsFull before.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [inlineRoot,inlineMid,rawSelf] at row
    rcases List.mem_cons.mp row with rfl|row
    · change Equivalent (record 30 (record 31 mu .emptyRecord) .emptyRecord)
          (record 30 (record 31 (record 40 mu .emptyRecord) .emptyRecord) .emptyRecord)
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30
        (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
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


theorem original_input_has_no_native_origin_at_the_fresh_allocated_target :
    ∀ o ∈ before.state.base.core.origins, o.slot ≠ 7 := by
  intro o inside
  change o ∈ native at inside
  simp only [native,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl|rfl|rfl <;> decide

open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Alias321 (no_nonempty_alias_only)

private noncomputable def chosen :=
  readCaptureFromReadyHead before.old certified groundedRows ⟨0,0⟩ [] 0

private theorem realCaptureExists : chosen.isSome = true := by
  decide +kernel

private noncomputable def witness := chosen.get realCaptureExists

private def expectedAfter : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
    ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩]⟩

theorem genuine_compiler_adds_its_ordinary_row_but_not_all_named_graph_coordinates :
    witness.allocated.after = expectedAfter ∧
    witness.allocated.after.equations[3]? = some ⟨7,rawSelf.right⟩ ∧
    ∀ e ∈ witness.allocated.after.equations, e.left = 4 → shapeOf e.right = none := by
  have h : exactOrdinaryState witness.allocated.after expectedAfter = true := by
    decide +kernel
  have q := (exact_ordinary_snapshot_iff ..).mp h
  refine ⟨q,?_,?_⟩
  · rw [q]
    rfl
  · rw [q]
    intro e row owns
    change e ∈ [inlineRoot,inlineMid,rawSelf,⟨7,rawSelf.right⟩,
      ⟨4,.record 30 (.record 31 (.variable 7) empty) empty⟩] at row
    simp only [List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with (rfl|rfl|rfl|rfl|rfl)
    · rfl
    · cases owns
    · cases owns
    · cases owns
    · rfl

#print axioms genuine_compiler_adds_its_ordinary_row_but_not_all_named_graph_coordinates

#print axioms actual_prechecked_input_with_capture_has_a_real_fitting_model
#print axioms original_input_has_no_native_origin_at_the_fresh_allocated_target
#print axioms actual_prechecked_native_request_has_the_exact_old_ordinary_capture_receipt
open GeneralDeclarativeI65.I72.NamedProjection464
  (LiteralProjectionWire checkLiteralSuppliedPhase accepted_literal_phase_has_exact_ordinary_batch_and_original_plans
   SourceRowSelection readSourceProposal)
open GeneralDeclarativeK2Graph321.AddAtOneSource (extendedRows)

private def projectedRoot : Equation := mkNamed 4 30 6
private def projectedMid : Equation := mkNamed 6 31 7
private def projectedAfter : GeneralDeclarativeHead320.State :=
  extendedRows (extendedRows expectedAfter projectedRoot) projectedMid

private def slotCut (start : Nat) (sub : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = start then 0 else if sub.contains i then 1 else 2⟩

private def originalRootFrame : SourceRowSelection := ⟨0,1,[.recordPayload 30 empty]⟩
private def originalMidFrame : SourceRowSelection := ⟨1,3,[.recordPayload 31 empty]⟩
private def scopedPhase : List LiteralProjectionWire :=
  [⟨originalRootFrame,slotCut 4 [6]⟩,
   ⟨originalMidFrame,slotCut 6 [7,5]⟩]

theorem same_actual_compiler_post_snapshot_allows_safe_named_raw_presentation :
    checkLiteralSuppliedPhase witness.allocated.after projectedAfter scopedPhase = true ∧
      readSourceProposal witness.allocated.after originalRootFrame = some projectedRoot ∧
      readSourceProposal witness.allocated.after originalMidFrame = some projectedMid := by
  have real := genuine_compiler_adds_its_ordinary_row_but_not_all_named_graph_coordinates.1
  rw [real]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩


private def projectedInput : FullProblem := (pairAt projectedAfter).get (by decide +kernel)

theorem safe_named_route_still_has_no_issued_payload_for_the_inline_field :
    (shapeOf projectedMid.right).isSome = true ∧
      (∀ o ∈ projectedInput.old.state.core.origins,
        ¬ OriginRoute projectedInput.old.state.core o 7) ∧
      ¬ ClosedInlineField458.OriginalInlineField projectedInput.old.state.core 6 projectedMid 31 7 := by
  have missing : ∀ o ∈ projectedInput.old.state.core.origins,
        ¬ OriginRoute projectedInput.old.state.core o 7 := by
    intro o seen route
    change o ∈ native at seen
    have routed := (RecordTrail455.original_route_iff_data455 ..).mpr route
    change RecordTrail455.checkOriginalRoute projectedInput.old.state.core o 7 = true at routed
    unfold RecordTrail455.checkOriginalRoute at routed
    change ((7 == o.slot) || false) = true at routed
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl|rfl <;> cases routed
  refine ⟨rfl,missing,?_⟩
  rintro ⟨words,chosen,src,raw,forms,rawRows,labels,occurrence,selected,inline,
    parent,inParent,payload,inPayload,physical,pr,route,issuer,alias,pep,oep⟩
  exact missing payload inPayload route

#print axioms safe_named_route_still_has_no_issued_payload_for_the_inline_field
#print axioms same_actual_compiler_post_snapshot_allows_safe_named_raw_presentation


end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ReadyCapture
