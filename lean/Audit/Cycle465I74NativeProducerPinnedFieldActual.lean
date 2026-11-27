import Yulang.GeneralDeclarativeI65I74NativeProducerPinnedField465
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualPinnedPhase465
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
open InstalledProtocolSum462 (onOldCursor)
open PreparedDeclarations463
open GeneralDeclarativeK2Graph321.AddAtOneSource
open List410 (ExactEscapeWire)

private def empty : Expr := .primitive .emptyRecord []
private def mkNamed (x label child : Nat) : Equation := ⟨x,.record label (.variable child) empty⟩
private def rawSelf : Equation := mkNamed 5 40 5
private def inlineMid : Equation := ⟨6,.record 31 rawSelf.right empty⟩
private def inlineRoot : Equation := ⟨4,.record 30 inlineMid.right empty⟩
private def namedRoot : Equation := mkNamed 4 30 6
private def namedMid : Equation := mkNamed 6 31 5
private def oldRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf]⟩
private def afterRaw : GeneralDeclarativeHead320.State := extendedRows (extendedRows oldRaw namedRoot) namedMid

private def cutAt (root : Nat) (descendants : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = root then 0 else if descendants.contains i then 1 else 2⟩
private def pattern : Pattern :=
  .record 30 (.record 31 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 syntax6 .emptyRecord
private def native : List Origin :=
  [⟨4,[402],.ordinary syntax4⟩,⟨6,[402],.ordinary syntax6⟩,⟨5,[402],.ordinary syntax5⟩,
    ⟨4,[499],.ordinary syntax4⟩,⟨6,[499],.ordinary syntax6⟩]

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

private def after : FullProblem := (pairAt afterRaw).get (by decide +kernel)

private theorem ready : DeclarationReady (authoredRegistry after.old.state.core.current) declaration := by
  have bits : RecordTrail455.localAuthorBits after.old.state.core.current.environment declaration = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp bits
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c absent
  cases absent

open PhysicalVisit463
open NativeProducer465.PinnedTicket

private def postTable : CheckedTable after.state.base.core.current :=
  ⟨[declaration],fun _d mem => (List.mem_singleton.mp mem).symm ▸ ready⟩

private def rawTrail (first second owner payload : Nat) : Wire emptyPolicy :=
  .down ⟨first,.same,.field 0 0,.field ⟨owner,payload,0,.same⟩⟩ (cutAt 4 [6,5])
    (.down ⟨second,.same,.field 0 0,.field ⟨1,2,0,.same⟩⟩ (cutAt 6 [5]) .stop)
private def wire (first second owner payload : Nat) : HeadFieldWire after.old :=
  let cyc : FieldCycleWire := ⟨⟨2,.same,5⟩,[],.same⟩
  ⟨⟨0,0⟩,(onOldCursor after.old .plain 9 ⟨rawTrail first second owner payload,cyc⟩).along⟩
private def visibleReport (owner payload : Nat) : Option HeadFieldReceipt :=
  readHeadField (p := after.old) postTable (wire 3 4 owner payload)

private def firstPinned (owner payload : Nat) : Option (Nat × Nat) :=
  (pinnedOrdinals (wire 3 4 owner payload).spine.visit)[0]?

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [(visibleReport 0 1).isSome, (visibleReport 3 4).isSome,
  firstPinned 0 1 == some (3,0), firstPinned 3 4 == some (3,3),
  (visibleReport 0 4).isNone, (visibleReport 3 1).isNone]

theorem two_actual_wires_replay_the_same_report_with_different_pinned_issuers :
    (visibleReport 0 1).isSome = true ∧
    (visibleReport 0 1).map (fun x => (x.path,x.rows,x.terminal)) =
      (visibleReport 3 4).map (fun x => (x.path,x.rows,x.terminal)) ∧
    firstPinned 0 1 = some (3,0) ∧ firstPinned 3 4 = some (3,3) ∧
    (after.old.state.core.origins[0]?).map Origin.issuer = some [402] ∧
    (after.old.state.core.origins[3]?).map Origin.issuer = some [499] := by
  decide +kernel

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

theorem actual_two_issuer_record_graph_has_one_fit :
    FitsFull after.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [inlineRoot,inlineMid,rawSelf,namedRoot,namedMid] at row
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
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at row
        rcases row with rfl|rfl|rfl
        · exact unfolded
        · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
        · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro source here
    change source ∈ native at here
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad


open NativeProducer465
open GeneralDeclarativeWitnessNativeValue360 (Write)

theorem a_native_release_cannot_manufacture_either_inline_owner
    (phase : CheckedPhase after.old.state.core) (w : Write) :
    (readPinnedHeadField (phase := phase) postTable ⟨wire 3 4 0 1,⟨0,0,w⟩⟩).isNone = true ∧
    (readPinnedHeadField (phase := phase) postTable ⟨wire 3 4 3 4,⟨0,3,w⟩⟩).isNone = true := by
  have neither : ∀ (ordinal : Nat),
      after.old.state.core.origins[ordinal]?.map Origin.endpoint = some (.ordinary syntax4) →
      ∀ (a : PinnedHeadField after.old), a.phase.sourceOrdinal = ordinal →
      a.phase.write = w → (readPinnedHeadField (phase := phase) postTable a).isNone = true := by
    intro ordinal endpoint a addr write
    cases hit : readPinnedHeadField (phase := phase) postTable a with
    | none => rfl
    | some r =>
      exfalso
      obtain ⟨_,_,c,_,raw,near,_,_,actual⟩ :=
        (same_existing_report_checked_at_exact_ordinal ..).mp hit
      have stored := congrArg (Option.map Origin.endpoint) actual.1
      rw [addr,endpoint] at stored
      have formula := Option.some.inj stored.symm
      rw [write] at formula
      exact concrete_nonvariable_ordinary_source_is_never_native360_emission w.code syntax4
        (fun _ h => by cases h) formula
  exact ⟨neither 0 rfl _ rfl rfl,neither 3 rfl _ rfl rfl⟩

#print axioms actual_two_issuer_record_graph_has_one_fit
#print axioms a_native_release_cannot_manufacture_either_inline_owner

#print axioms two_actual_wires_replay_the_same_report_with_different_pinned_issuers
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualPinnedPhase465
