import Yulang.GeneralDeclarativeI65I74ExactHeadCompilerReceipt466
import Yulang.GeneralDeclarativeI65I74ScopedHeadCompileAtPose466
import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeI65Heads367

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ModernHead
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
open CommonNominalFullCarrier (Ty Equivalent record nominal)
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
private def inlineMid : Equation := ⟨6,.nominal 20 [.record 31 rawSelf.right empty]⟩
private def inlineRoot : Equation := ⟨4,.record 30 inlineMid.right empty⟩
private def oldRaw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[inlineRoot,inlineMid,rawSelf]⟩

private def pattern : Pattern :=
  .record 30 (.app 20 [.record 31 (.var 3) (.app 9 [])]) (.app 9 [])
private def declaration : Declaration := ⟨218,19,[pattern],[],[],[]⟩
private def syntax5 : TyTerm Nat := .record 40 (.var 5) .emptyRecord
private def syntax6 : TyTerm Nat := .record 31 syntax5 .emptyRecord
private def syntax4 : TyTerm Nat := .record 30 (.var 6) .emptyRecord
private def native : List Origin :=
  [⟨4,[402],.ordinary syntax4⟩,⟨6,[402],.nominal 20 [.inl (.point (.ordinary syntax6))]⟩,⟨5,[402],.ordinary syntax5⟩]

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

open Yulang.C466HeadCompileAtPose
open Yulang.C466ExactOriginalHeadOldReceipt
open GeneralDeclarativeI65.I72.AuthoredInspectQuery456 (compileQuery)

private def modern :=
  readPrecheckedHead (p := before.old) certified ⟨0,0⟩

private theorem actualModernExists : modern.isSome = true := by
  decide +kernel

private def chosen := modern.get actualModernExists

theorem edited_fixture_retains_the_exact_actual_modern_nominal_head :
    chosen.orig.declaration.id = 218 ∧
      chosen.orig.code = .record 30 (.nominal 20 [.record 31 (.variable 3) empty]) empty := by
  exact ⟨rfl,rfl⟩

theorem the_existing_producer_cannot_read_the_actual_modern_source_head :
    oldCompile before.old.state.core (.app 20 [.record 31 (.var 3) (.app 9 [])]) = none ∧
    ∀ oldSource (src : GeneralDeclarativeNestedView332.Sources oldSource) keep job,
      readCaptureFromReadyHead before.old certified src ⟨0,0⟩ keep job = none := by
  have noHere : oldCompile before.old.state.core (.app 20 [.record 31 (.var 3) (.app 9 [])]) = none := by rfl
  refine ⟨noHere,?_⟩
  intro _ src keep job
  have noLegacy : oldCompile before.old.state.core (GeneralDeclarationPatterns.normalize chosen.orig.original) = none := by rfl
  have read : readPrecheckedHead (p := before.old) certified ⟨0,0⟩ = some chosen :=
    (Option.some_get actualModernExists).symm
  have one : (visible before.old.state.core before.old.root).length = 1 := rfl
  unfold oldCompile at noLegacy
  simp [readCaptureFromReadyHead,one,read,readOldCaptureReceipt,Option.bind,
    actualConstructors,actualInterpretation,noLegacy]

/-- info: [true, true, true] -/
#guard_msgs in
#eval [modern.isSome, (oldCompile before.old.state.core pattern).isNone,
  (readCaptureFromReadyHead before.old certified (ofRows oldRaw.equations (fun _ h => h)) ⟨0,0⟩ [] 0).isNone]

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

private def midPayload := record 31 mu .emptyRecord
private def midTy := nominal 20 [.inl midPayload]
private def rootTy := record 30 midTy .emptyRecord
private def concrete : I72.Model :=
  ⟨fun n => (if n = 4 then rootTy else if n = 6 then midTy else mu,Common.rowEmpty),
    fun _ => none,
    fun n => if n = 4 then some (.ordinary syntax4)
      else if n = 6 then some (.nominal 20 [.inl (.point (.ordinary syntax6))])
      else if n = 5 then some (.ordinary syntax5) else none⟩

theorem actual_modern_visible_source_has_a_real_fitting_model :
    FitsFull before.state concrete := by
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ bad; cases bad
  · intro _ bad; cases bad
  · intro r row
    change r ∈ [inlineRoot,inlineMid,rawSelf] at row
    rcases List.mem_cons.mp row with rfl|row
    · change Equivalent (record 30 (nominal 20 [.inl (record 31 mu .emptyRecord)]) .emptyRecord)
          (record 30 (nominal 20 [.inl (record 31 (record 40 mu .emptyRecord) .emptyRecord)]) .emptyRecord)
      apply GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30
      · apply GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr (first := [record 31 mu .emptyRecord])
          (last := [record 31 (record 40 mu .emptyRecord) .emptyRecord]) 20
        exact .cons (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)) .nil
      · exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _
    · rcases List.mem_cons.mp row with rfl|row
      · change Equivalent (nominal 20 [.inl (record 31 mu .emptyRecord)])
          (nominal 20 [.inl (record 31 (record 40 mu .emptyRecord) .emptyRecord)])
        apply GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr (first := [record 31 mu .emptyRecord])
          (last := [record 31 (record 40 mu .emptyRecord) .emptyRecord]) 20
        exact .cons (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 31 unfolded
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)) .nil
      · obtain rfl := List.mem_singleton.mp row
        exact unfolded
  · intro _ bad; cases bad
  · intro source here
    change source ∈ native at here
    simp only [native,List.mem_cons,List.not_mem_nil,or_false] at here
    rcases here with rfl|rfl|rfl <;> rfl
  · intro _ bad; cases bad



#print axioms actual_modern_visible_source_has_a_real_fitting_model
#print axioms edited_fixture_retains_the_exact_actual_modern_nominal_head
#print axioms the_existing_producer_cannot_read_the_actual_modern_source_head
end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Actual466ModernHead
