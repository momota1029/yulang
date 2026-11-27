import Yulang.GeneralDeclarativeI65I74ProjectionBatchSound464
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464
import Yulang.GeneralDeclarativeI65I74ProjectionBatchField464
import Yulang.GeneralDeclarativeI65I74OrderedProjectionDerivation464
import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualMovedOwnerAudit
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
private def inlineMid : Equation := ⟨11,.record 31 rawSelf.right empty⟩
private def namedRoot : Equation := mkNamed 4 30 6
private def namedMid : Equation := mkNamed 11 31 5
private def oldAlias : Equation := ⟨6,.variable 11⟩
private def oldRaw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[namedRoot,inlineMid,rawSelf,oldAlias]⟩
private def afterRaw : GeneralDeclarativeHead320.State := extendedRows oldRaw namedMid

private def cutAt (root : Nat) (peers descendants : List Nat) : ExactEscapeWire :=
  ⟨List.range 12,(List.range 12).map fun i =>
    if i = root || peers.contains i then 0 else if descendants.contains i then 1 else 2⟩
private def midProof : EqWire :=
  .compose (.old (.currentRow 1)) (.record 31 (.reverse (.old (.currentRow 2))) (.old (.refl empty)))

private def pattern : Pattern :=
  .record 30 (.record 31 (.record 40 (.var 3) (.app 9 [])) (.app 9 [])) (.app 9 [])
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 syntax6 .emptyRecord
private def native : List Origin :=
  [⟨4,[402],.ordinary syntax4⟩,⟨11,[402],.ordinary syntax6⟩,⟨5,[402],.ordinary syntax5⟩]

private def nativeRoutes : List GeneralDeclarativeI65.Alias := [⟨6,11,[402]⟩]
private def pairAt (s : GeneralDeclarativeHead320.State)
    (routes : List GeneralDeclarativeI65.Alias := nativeRoutes) : Option FullProblem := do
  let bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← compile bodies
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨8,some ⟨[.type,.type],8⟩,.primitive .pair⟩]
  let auth ← GeneralSourceMetadataBareBundle291.compile
    ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[declaration]⟩
  let env : Environment := ⟨3,2,0,bodies,graph,auth⟩
  let core : GeneralDeclarativeI65.State := ⟨⟨env,s,[]⟩,List.replicate 20 [] ++ [[cov]],native,routes⟩
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
  .down ⟨first,.same,.field 0 0,.field ⟨0,1,0,.forward 3⟩⟩ (cutAt 4 [] [6,5,11])
    (.down ⟨second,.forward 3,.field 0 0,.field ⟨1,2,0,.same⟩⟩ (cutAt 6 [11] [5]) .stop)
private def wire (post : FullProblem) (first second : Nat) : HeadFieldWire post.old :=
  let cyc : FieldCycleWire := ⟨⟨2,.same,5⟩,[],.same⟩
  ⟨⟨0,0⟩,(onOldCursor post.old .plain 9 ⟨rawTrail first second,cyc⟩).along⟩
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
  ⟨fun n => (if n = 4 then rootTy else if n = 6 ∨ n = 11 then midTy else mu,Common.rowEmpty),
    fun _ => none,
    fun n => if n = 4 then some (.ordinary syntax4)
      else if n = 11 then some (.ordinary syntax6)
      else if n = 5 then some (.ordinary syntax5) else none⟩

theorem moved_owner_actual_old_inline_full_state_fits :
    FitsFull before.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [namedRoot,inlineMid,rawSelf,oldAlias] at row
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at row
    rcases row with rfl|rfl|rfl|rfl
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · change Equivalent (record 31 mu .emptyRecord) (record 31 (record 40 mu .emptyRecord) .emptyRecord)
      exact GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)
    · exact unfolded
    · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
  · intro _ bad; cases bad
  · intro source here
    change source ∈ native at here
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad


private def data : ProjectionWire := ⟨midProof,cutAt 11 [6] [5]⟩
private def expected := (readProjectionBatchField phases certified ⟨[data],wire phases.after 0 4⟩).any fun r =>
  r.path == [(.field 30,6),(.field 31,5)] && r.rows == [0,4] &&
  r.terminal == 5 && r.stamp && r.literal.length == 1

private def noRoute : FullProblem := (pairAt afterRaw []).get (by decide +kernel)
private def wrongIssuer : FullProblem := (pairAt afterRaw [⟨6,11,[403]⟩]).get (by decide +kernel)
private def lacking : SnapshotPair := ⟨before,noRoute,rfl,rfl⟩
private def wrong : SnapshotPair := ⟨before,wrongIssuer,rfl,rfl⟩

theorem actual_old_authored_route_is_not_substituted_by_raw_alias_or_native_values :
    expected = true ∧ FitsFull after.state concrete ∧ FitsFull noRoute.state concrete ∧
      FitsFull wrongIssuer.state concrete := by
  have checked : checkSuppliedBatch phases.pre phases.post [data] = true := by decide +kernel
  have models := batch_preserves_all_full_fits_with_independent_stored_frame
    (p := phases) (checked_batch_has_exact_independent_supplied_prefix_evidence checked)
    (unchanged_empty_retention_frame rfl rfl rfl rfl) concrete
  have fit := models.mp moved_owner_actual_old_inline_full_state_fits
  exact ⟨by decide +kernel,fit,⟨fit.1,by intro _ bad; cases bad⟩,⟨fit.1,by intro _ bad; cases bad⟩⟩

/-- info: [true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [expected,checkSuppliedBatch lacking.pre lacking.post [data],
  checkSuppliedBatch wrong.pre wrong.post [data],
  (readProjectionBatchField lacking certified ⟨[data],wire lacking.after 0 4⟩).isNone,
  (readProjectionBatchField wrong certified ⟨[data],wire wrong.after 0 4⟩).isNone,
  (readProjectionBatchField phases certified ⟨[data],wire phases.after 0 1⟩).isNone,
  (readProjectionBatchField phases certified ⟨[data],wire phases.after 4 0⟩).isNone]

#print axioms moved_owner_actual_old_inline_full_state_fits
#print axioms actual_old_authored_route_is_not_substituted_by_raw_alias_or_native_values
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ActualMovedOwnerAudit
