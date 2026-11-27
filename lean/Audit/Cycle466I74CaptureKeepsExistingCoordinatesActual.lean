import Yulang.GeneralDeclarativeI65I74CaptureKeepsExistingCoordinates466
import Yulang.GeneralDeclarativeI65I74StableCaptureAcrossKeep466
import Yulang.GeneralDeclarativeI65I74CaptureLedgerErasure466
import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65Heads367

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466NativeSlotReservation
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

private def pairAt (s : GeneralDeclarativeHead320.State) (extra : List Origin := []) : Option FullProblem := do
  let bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← compile bodies
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  let auth ← GeneralSourceMetadataBareBundle291.compile
    ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[declaration]⟩
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,List.replicate 20 [] ++ [[cov]],native ++ extra,[]⟩
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

open GeneralDeclarativeI65.I72.NamedProjection464 (SnapshotPair SameCompilerFrame)

private def prior : Origin := ⟨7,[801],.ordinary (.base .bool)⟩
private def occupied : FullProblem := (pairAt oldRaw [prior]).get (by decide +kernel)
private def pair : SnapshotPair := ⟨before,occupied,rfl,rfl⟩
private theorem sameCompiler : SameCompilerFrame pair := ⟨rfl,rfl⟩
private def oldIndex := ofRows (s := oldRaw) oldRaw.equations (fun _ h => h)
private def keepNative := existingNativeCoordinates occupied.old.state.core
private def noneKept :=
  readCaptureFromReadyHead occupied.old (pair.afterTable certified) oldIndex ⟨0,0⟩ [] 0
private def kept :=
  readCaptureFromReadyHead occupied.old (pair.afterTable certified) oldIndex ⟨0,0⟩ keepNative 0

theorem ordinary_replay_does_not_observe_the_already_stored_opaque_slot :
    (readCaptureFromReadyHead before.old certified oldIndex ⟨0,0⟩ [] 0).map CheckedCaptureHead.allocated =
        noneKept.map CheckedCaptureHead.allocated ∧
    prior ∈ occupied.old.state.core.origins ∧
    (noneKept.map (fun r => r.allocated.target)) = some prior.slot ∧
    (kept.map (fun r => r.allocated.target)) = some 8 := by
  refine ⟨both_same_state_snapshots_have_the_same_compiled_ordinary_capture_data
    pair sameCompiler rfl certified oldIndex ⟨0,0⟩ [] 0,?_,by decide +kernel,by decide +kernel⟩
  exact List.mem_append_right _ List.mem_cons_self

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [
  decide ((noneKept.map (fun r => r.allocated.target)) = some 7),
  decide ((kept.map (fun r => r.allocated.target)) = some 8),
  decide ((noneKept.map (fun r => r.allocated.rawOrdinal)) = (kept.map (fun r => r.allocated.rawOrdinal))),
  decide ((noneKept.map (fun r => r.allocated.written)) = (kept.map (fun r => r.allocated.written)))]

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
      else if n = 5 then some (.ordinary syntax5) else if n = 7 then some prior.endpoint else none⟩

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



theorem extra_preexisting_slot_and_original_allocation_observation_fit_the_same_model :
    FitsFull before.state concrete ∧ FitsFull occupied.state concrete := by
  have old := actual_prechecked_input_with_capture_has_a_real_fitting_model
  refine ⟨old,⟨⟨old.1.1,?_⟩,?_⟩⟩
  · intro row present
    change row ∈ native ++ [prior] at present
    rcases List.mem_append.mp present with oldRow|extraRow
    · exact old.1.2 row oldRow
    · obtain rfl := List.mem_singleton.mp extraRow
      rfl
  · intro _ absent
    cases absent

private def attemptedPayload : Origin := ⟨7,[402],.ordinary syntax5⟩
private def conflicting : FullProblem := (pairAt oldRaw [prior,attemptedPayload]).get (by decide +kernel)

/-- Recording both the old native cell and a distinct derived ordinary
endpoint is not a way around the reservation. This is a supplied test
state, not an installed output or an alternative issuer. -/
theorem wrongly_reusing_the_stored_physical_position_cannot_preserve_any_fit :
    ¬ ∃ m, FitsFull conflicting.state m := by
  rintro ⟨m,fit⟩
  have first : prior ∈ conflicting.state.base.core.origins :=
    List.mem_append_right _ List.mem_cons_self
  have later : attemptedPayload ∈ conflicting.state.base.core.origins :=
    List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have a := fit.1.2 prior first
  have b := fit.1.2 attemptedPayload later
  have eq : (some prior.endpoint : Option _) = some attemptedPayload.endpoint := a.symm.trans b
  cases (Option.some.inj eq)

#print axioms wrongly_reusing_the_stored_physical_position_cannot_preserve_any_fit
#print axioms ordinary_replay_does_not_observe_the_already_stored_opaque_slot
#print axioms extra_preexisting_slot_and_original_allocation_observation_fit_the_same_model
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466NativeSlotReservation
