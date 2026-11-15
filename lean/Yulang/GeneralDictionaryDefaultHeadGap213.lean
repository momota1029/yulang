import Yulang.GeneralDictionaryDefaultPointRegression213
import Yulang.GeneralDictionaryDefaultMergeRevisionProbe210

/-! A closed test of the raw-head part of the terminal common-model bridge.
Centered equations do not determine the allocation's merge endpoints. This
is not a reachable EvidenceNode counterexample. -/
namespace Yulang.GeneralDictionaryDefaultHeadGap213
open GeneralDictionaryDefaultPointRegression213
open GeneralDictionarySemanticCollapseExample
open GeneralDictionarySemanticCollapseOutputExample
open GeneralNominalAllocation GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

abbrev lower : Nat := GeneralNominalAllocation.source GeneralDictionarySemanticCollapseExample.source registry outputRoot.identity (origin outputRoot.identity declaration.id 0 7 0)

abbrev modified : GeneralNominalCommonBridge.Assignment := fun name =>
  if name = lower then (.bottom,Common.rowEmpty) else model name

theorem keeps (different : name ≠ lower) : modified name = model name := by
  exact ite_eq_right different

theorem keeps_zero : modified 0 = model 0 := keeps (by decide +kernel)
theorem keeps_one : modified 1 = model 1 := keeps (by decide +kernel)
theorem keeps_two : modified 2 = model 2 := keeps (by decide +kernel)
theorem keeps_three : modified 3 = model 3 := keeps (by decide +kernel)
theorem keeps_binder : modified (before.binder 7) = model (before.binder 7) := by
  rw [before_binder]
  exact keeps (by decide +kernel)

theorem source_models : GeneralNominalState.Models GeneralDictionarySemanticCollapseExample.source modified := by
  apply GeneralNominalCenteredModelExtension.source_models_same _ _ GeneralDictionarySemanticCollapseExample.source_models
  intro name member
  change name ∈ [0,1,2,3] ++ [0,1,2,3] ++ [] ++ [] at member
  simp only [List.mem_append,List.not_mem_nil,or_false,or_self] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact keeps_zero.symm
  · exact keeps_one.symm
  · exact keeps_two.symm
  · exact keeps_three.symm

theorem head_holds : before.SchemaHolds before.headSchema modified := by
  apply (GeneralNominalModeFrame181.schema_iff before before.headSchema (first := model) (last := modified) ?_).mp
    GeneralDictionaryDefaultPointRegression213.head_holds
  intro name member
  rw [GeneralDictionaryDefaultPointRegression213.head_schema] at member
  change name ∈ [0,0,0,before.binder 7] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact keeps_zero.symm
  · exact keeps_zero.symm
  · exact keeps_zero.symm
  · exact keeps_binder.symm

theorem head_equations : GeneralNominalCenteredHeadOutputs.HeadEquations before modified := by
  refine ⟨?_,?_,head_holds⟩
  · intro index
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name member
    cases List.mem_singleton.mp member
    unfold GeneralNominalPacketSupport.capture
    rw [before_bindings]
    change Subtype (modified lower).1 (modified (before.binder 7)).1 ∧
      Subtype (modified (before.binder 7)).1 (modified (GeneralNominalAllocation.source GeneralDictionarySemanticCollapseExample.source registry
        outputRoot.identity (origin outputRoot.identity declaration.id 1 7 0))).1
    rw [keeps_binder,before_value]
    constructor
    · intro depth
      apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
      intro rank env obs _
      exact CommonNominalFullDemand.probeAt_bottom rank obs
    · exact subtype_refl _

 theorem not_head_models : ¬ GeneralNominalCenteredHeadCandidates.HeadModels registry context outputRoot declaration bounds modified := by
  intro head
  have ordinary := (GeneralNominalPacketSupport.private_exact before.packet modified).mp head.1 |>.2
  have merges := ordinary.2.1
  rw [before_bindings] at merges
  have equal := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (state := GeneralDictionarySemanticCollapseExample.source) (registry := registry) (root := outputRoot.identity)
    (declaration := declaration) (name := 7) (lower := 3) (upper := 3)
    (by change 7 ∈ [7]; simp) merges
  change Equivalent (modified lower).1 (modified 3).1 at equal
  rw [keeps_three] at equal
  change Equivalent .bottom (.base .int) at equal
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int) equal

 theorem raw_and_centered_not_raw_head :
    GeneralNominalState.Models GeneralDictionarySemanticCollapseExample.source modified ∧
    GeneralNominalCenteredHeadOutputs.HeadEquations before modified ∧
    ¬ GeneralNominalCenteredHeadCandidates.HeadModels registry context outputRoot declaration bounds modified :=
  ⟨source_models,head_equations,not_head_models⟩


/-- Even the nonempty emitted associated output survives the perturbation. -/
theorem outputs : GeneralNominalCenteredHeadMatStepPackets.Outputs before modified := by
  intro equation member
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema at member
  rw [GeneralDictionaryDefaultTerminalOutputs210.terminal_requests before rfl] at member
  change equation ∈ (GeneralNominalCenteredHeadMatSchemas.generated
    GeneralDictionarySemanticCollapseExample.source.constructors interpretation
    (GeneralNominalMaterialization.rootRequests declaration outputRoot)).equations at member
  rw [root_request] at member
  change equation ∈ [⟨3,.actual,.variable 7⟩] at member
  cases List.mem_singleton.mp member
  change Equivalent (modified 3).1 (modified (before.binder 7)).1
  rw [keeps_three,keeps_binder,before_value]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem not_packet : ¬ GeneralNominalCenteredHeadMatStepPackets.Holds before modified := by
  intro packet
  exact not_head_models
    ((GeneralDictionaryDefaultTerminalReduction212.packet_iff (plan := before) rfl).mp packet).1

/-- Thus rawHeadModels cannot be dropped even after preserving all other
terminal-packet conjuncts and the old source model. -/
theorem remaining_terminal_conjuncts_do_not_suffice :
    GeneralNominalState.Models GeneralDictionarySemanticCollapseExample.source modified ∧
    GeneralNominalCenteredHeadOutputs.HeadEquations before modified ∧
    GeneralNominalCenteredHeadMatStepPackets.Outputs before modified ∧
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds before modified :=
  ⟨source_models,head_equations,outputs,not_packet⟩

end Yulang.GeneralDictionaryDefaultHeadGap213
