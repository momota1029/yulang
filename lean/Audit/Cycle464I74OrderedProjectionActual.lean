import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeI65I74ProjectionBatchField464
import Yulang.GeneralDeclarativeI65I74OrderedProjectionDerivation464
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualTwoStageAudit
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
open Derivation
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
private def rootProof : EqWire :=
  .compose (.old (.currentRow 0)) (.record 30 (.reverse (.old (.currentRow 1))) (.old (.refl empty)))
private def midProof : EqWire :=
  .compose (.old (.currentRow 1)) (.record 31 (.reverse (.old (.currentRow 2))) (.old (.refl empty)))
private def evidence : List DerivedAppendData :=
  [⟨⟨namedRoot,cutAt 4 [6]⟩,rootProof⟩,⟨⟨namedMid,cutAt 6 [5]⟩,midProof⟩]

private def pattern : Pattern :=
  .record 30 (.record 31 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])
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
private def after : FullProblem := (pairAt afterRaw).get (by decide +kernel)

private theorem ready : DeclarationReady (authoredRegistry before.old.state.core.current) declaration := by
  have bits : RecordTrail455.localAuthorBits before.old.state.core.current.environment declaration = true := by
    decide +kernel
  obtain ⟨cover,sig,id,prod,only,scope⟩ := (RecordTrail455.local_author_bits_exact455 ..).mp bits
  refine ⟨sig,id,prod,only,scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cover,?_⟩
  intro c absent
  cases absent

private def certified : CheckedTable before.state.base.core.current :=
  ⟨[declaration],fun _d mem => (List.mem_singleton.mp mem).symm ▸ ready⟩
private def phases : SnapshotPair := ⟨before,after,rfl,rfl⟩
private def postTable : CheckedTable after.state.base.core.current := phases.afterTable certified

private def rawTrail (first second : Nat) : Wire emptyPolicy :=
  .down ⟨first,.same,.field 0 0,.field ⟨0,1,0,.same⟩⟩ (cutAt 4 [6,5])
    (.down ⟨second,.same,.field 0 0,.field ⟨1,2,0,.same⟩⟩ (cutAt 6 [5]) .stop)
private def wire (first second : Nat) : HeadFieldWire after.old :=
  let cyc : FieldCycleWire := ⟨⟨2,.same,5⟩,[],.same⟩
  ⟨⟨0,0⟩,(onOldCursor after.old .plain 9 ⟨rawTrail first second,cyc⟩).along⟩
private def accepted := (readHeadField (p := after.old) postTable (wire 3 4)).any fun r =>
  r.path == [(.field 30,6),(.field 31,5)] && r.rows == [3,4] &&
    r.terminal == 5 && r.stamp && r.literal.length == 1

private theorem ordinary_batch_reads_supplied_post : readDerivedAppends oldRaw evidence = some afterRaw := by
  have recognized : (readDerivedAppends oldRaw evidence).isSome = true := by decide +kernel
  cases yes : readDerivedAppends oldRaw evidence with
  | none => simp [yes] at recognized
  | some after =>
    have got := (read_derived_batch_validates_exact_supplied_source_proofs_and_cut yes).1
    have eq := unfolding_full_named_batch_is_exact_ordered_target got
    have exactState : after = afterRaw := eq
    rw [exactState]

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

theorem actual_old_inline_full_state_has_an_inhabited_fit_for_two_projections :
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

theorem all_actual_models_agree_for_the_two_supplied_stages (m : I72.Model) :
    FitsFull before.state m ↔ FitsFull after.state m := by
  have ordinary := (checked_derived_batch_preserves_all_exact_ordinary_models_and_raw_cycles
      ordinary_batch_reads_supplied_post m.assignment 4).1
  constructor
  · intro fit
    exact ⟨⟨⟨ordinary.mpr fit.1.1.1,fit.1.1.2⟩,fit.1.2⟩,by intro _ bad; cases bad⟩
  · intro fit
    exact ⟨⟨⟨ordinary.mp fit.1.1.1,fit.1.1.2⟩,fit.1.2⟩,by intro _ bad; cases bad⟩

private def phaseKeys : List ProjectionWire :=
  [⟨rootProof,cutAt 4 [6]⟩,⟨midProof,cutAt 6 [5]⟩]
private def actual : ProjectionBatchWire phases := ⟨phaseKeys,wire 3 4⟩
private def acceptedPair := (readProjectionBatchField phases certified actual).any fun r =>
  r.path == [(.field 30,6),(.field 31,5)] && r.rows == [3,4] &&
    r.terminal == 5 && r.stamp && r.literal.length == 1

theorem exact_actual_two_distinct_named_stages_advance_to_old_terminal_cycle :
    readDerivedAppends oldRaw evidence = some afterRaw ∧ accepted = true ∧ acceptedPair = true ∧
      AliasCycle oldRaw (observed oldRaw) 5 := by
  refine ⟨ordinary_batch_reads_supplied_post,by decide +kernel,by decide +kernel,?_⟩
  exact cycle_at_sound412 (w := ⟨⟨2,.same,5⟩,[],.same⟩) (by decide +kernel)

/-- info: [true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [accepted, acceptedPair, (readDerivedAppends oldRaw evidence).isSome,
  (readProjectionBatchField phases certified { actual with rows := phaseKeys.reverse }).isNone,
  (readProjectionBatchField phases certified { actual with rows := phaseKeys.take 1 }).isNone,
  (readHeadField (p := after.old) postTable (wire 0 4)).isNone,
  (readHeadField (p := after.old) postTable (wire 3 1)).isNone,
  (readHeadField (p := after.old) postTable (wire 4 3)).isNone]

#print axioms actual_old_inline_full_state_has_an_inhabited_fit_for_two_projections
#print axioms all_actual_models_agree_for_the_two_supplied_stages
#print axioms exact_actual_two_distinct_named_stages_advance_to_old_terminal_cycle
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualTwoStageAudit
