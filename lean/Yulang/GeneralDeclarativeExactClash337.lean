import Yulang.GeneralDeclarativeExactDictionary337
import Yulang.GeneralDeclarativeEndpointClashChecked336

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeExactClash337
open GeneralDeclarativeEndpointClash336
open GeneralDeclarativeEndpointChildren336 (initial scalar)
open GeneralDeclarativeEndpointChildModels336 (sourceModel source_valid)
open GeneralDeclarativeEndpointProgram336 (Projection)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeEndpointRecord336 (field_interval)
open GeneralDeclarativeExactOverlay337 (ModelsExact approved)
open GeneralDeclarativeExactDictionary337 (Rule Clash ties_exact)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype exactEmpty subtype_trans observeTy)
open CommonNominalFullDemand (ProbeAt ProbeStep)

theorem clash_exact (before : GeneralDeclarativeHead320.State)
    (reads : List Entry) (spans : List (Nat × GeneralDeclarativeWhere319.Capture)) (fallback) :
    Clash before reads spans fallback ↔
    (∃ m, ModelsExact before reads m) ∧
      ∀ m, ModelsExact before reads m → ¬GeneralDeclarativeStableCanonical329.EqualUses m spans := by
  constructor
  · rintro ⟨found,no⟩
    exact ⟨found,fun m fit equal => no ⟨m,(ties_exact _ _ _ _ _).mpr ⟨fit,equal⟩⟩⟩
  · rintro ⟨found,no⟩
    refine ⟨found,?_⟩
    rintro ⟨m,fit⟩
    obtain ⟨model,eq⟩ := (ties_exact _ _ _ _ _).mp fit
    exact no m model eq

theorem before_model : ∃ m, ModelsExact named sidecar m := by
  obtain ⟨m,fit,_⟩ := approved GeneralDeclarativeEndpointClash336.approved program
    sourceModel source_valid protect
  exact ⟨m,fit⟩

theorem field_agrees (m : Assignment) (fit : ModelsExact named sidecar m) :
    Equivalent (m 7).1 int := by
  have initialFit := GeneralDeclarativeGrowth327.restrict (GeneralDeclarativeEndpointBatch336.grows _ _ _) m fit.1
  have actualField := initialFit.2 scalar (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨mid,project,ranges⟩ := field_interval GeneralDeclarativeEndpointClash336.approved
    List.mem_cons_self List.mem_cons_self m initialFit
  let e : Entry := ⟨.field GeneralDeclarativeWitnessCutDecl334.arg 7 (.variable 3) (.variable 3),⟨6,7,8⟩⟩
  obtain ⟨ideal,wrote,agrees⟩ := fit.2 e List.mem_cons_self
  change (GeneralDeclarativeRecordChannel330.project 7 false [] (m 1).1).map
      (fun x => ((m 3).1,x,(m 3).1)) = some ideal at wrote
  have h : ((m 3).1,mid,(m 3).1) = ideal := Option.some.inj (by rw [project] at wrote; exact wrote)
  rw [← h] at agrees
  exact eqv_trans agrees.2.1 (eqv_trans ⟨ranges.2,ranges.1⟩ actualField)

theorem rest_above (m : Assignment) (fit : ModelsExact named sidecar m) :
    Subtype exactEmpty (m 10).1 := by
  have initialFit := GeneralDeclarativeGrowth327.restrict (GeneralDeclarativeEndpointBatch336.grows _ _ _) m fit.1
  have residual := GeneralDeclarativeExactDeleteAuth337.supported GeneralDeclarativeEndpointClash336.approved m initialFit
  let e : Entry := ⟨.rest GeneralDeclarativeWitnessCutDecl334.arg [7] endL endU,⟨9,10,11⟩⟩
  obtain ⟨ideal,wrote,agrees⟩ := fit.2 e (List.mem_cons_of_mem _ List.mem_cons_self)
  have h : (exactEmpty,GeneralDeclarativeExactDelete337.subtract [7] (m 1).1,
    CommonNominalFullCarrier.emptyRecord) = ideal := Option.some.inj wrote
  rw [← h] at agrees
  exact subtype_trans residual.1 agrees.2.1.2

theorem disjoint : ¬ Subtype exactEmpty int := by
  intro below
  let env : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row := ⟨fun _ => .bottom,fun _ => []⟩
  have yes : ProbeAt Common.rowLe 0 env (observeTy 0 int) (.base .int) := rfl
  have no := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env _ yes
  change ProbeAt Common.rowLe 0 env .exactEmpty (.base .int) at no
  simp [ProbeAt,ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at no

theorem exact_clash : Clash named sidecar used fallback := by
  apply (clash_exact _ _ _ _).mpr
  refine ⟨before_model,?_⟩
  intro m fits tied
  have eq := tied 0 ⟨6,7,8⟩ ⟨9,10,11⟩ (by rw [used_exact]; exact List.mem_cons_self)
    (by rw [used_exact]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact disjoint (subtype_trans (rest_above m fits) (subtype_trans eq.2 (field_agrees m fits).1))

/-- The real checked repeated binder elects before the tie. Its exact
(non-masked) standalone center cannot agree with the field center, so
the modeled contradiction yields genuine rejection, not waiting. -/
theorem regression :
    GeneralDeclarations.Checked registry ∧
    (∃ m, ModelsExact named sidecar m) ∧
    Rule current sidecar registry GeneralDeclarativeNestedExample332.interpretation wait root .rejected :=
  ⟨GeneralDeclarativeEndpointClashChecked336.checked,before_model,
    .tieClash (slice := ⟨initial,GeneralDeclarativeEndpointChildren336.support,grown,
      GeneralDeclarativeObserverGrowth330.sources_grow _ grown⟩) elected input exact_clash⟩

end Yulang.GeneralDeclarativeExactClash337
