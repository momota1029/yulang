import Yulang.GeneralNominalSharedPositive
import Yulang.GeneralNominalSharedPump

/-! The source Display/Wrap fixtures meet the new expansion certificates.
Leaf Len retains the generation check without inspecting its captured μ. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSharedExamples
open GeneralNominalSaturationState GeneralNominalRecursiveInspection GeneralNominalSharedCaptures
open GeneralDeclarationExamples (roles display wrap display_checked wrap_checked)
open GeneralNominalExamples (registry context displayRoot wrapRoot)
open GeneralNominalSupport (initial)

abbrev packet (wrapping : Bool) : Packet roles :=
  ⟨registry,context true,
    if wrapping then GeneralNominalDemandMerging.pointSite wrapRoot else GeneralNominalDemandMerging.pointSite displayRoot,
    if wrapping then wrap else display,
    by cases wrapping <;> first | exact display_checked | exact wrap_checked,[(0,0)]⟩
abbrev origin : Origin := .nominal (.source 0) 0 0

private theorem queries (wrapping : Bool) : GeneralNominalInspection.queries (packet wrapping).context.state
    (packet wrapping).context.interpretation (packet wrapping).declaration = [.nominal 0 [.variables [0]]] := by
  cases wrapping <;> simp [packet,GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,display,wrap]

private theorem old_report (wrapping : Bool) : GeneralNominalPacketSupport.report (packet wrapping) =
    GeneralNominalUnaryCaptureFacts.captured (GeneralNominalExamples.state true) 0 0 0 (1,1) := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries]
  cases wrapping <;> simp [packet,inspectMany,inspect,GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,
    typeArguments,Report.visit,Report.append,GeneralNominalUnaryCaptureFacts.captured]
  all_goals repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,GeneralNominalUnaryCaptureFacts.captured]

private theorem inherited (wrapping : Bool) : (inheritedReport (packet wrapping)).captures = [⟨0,(1,1),some origin⟩] := by
  unfold inheritedReport
  rw [queries]
  cases wrapping <;> simp [packet,inspectMany,inspect,GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,
    typeArguments,Report.visit,Report.append,GeneralNominalDemandMerging.pointSite,
    displayRoot,wrapRoot,GeneralNominalExamples.displayDemand,GeneralNominalExamples.wrapDemand,
    roles,GeneralDeclarationExamples.bareRole,GeneralDeclarationExamples.outputRole,List.ofFn_succ,origin]
  all_goals repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append]

theorem usable (wrapping : Bool) : Usable (packet wrapping) 0 origin :=
  GeneralNominalSharedPositive.single_capture_usable (packet wrapping) 0 (1,1) origin
    (by rw [old_report]; rfl) (inherited wrapping) (by rw [old_report]; simp [GeneralNominalUnaryCaptureFacts.captured,origin])

theorem generation (wrapping : Bool) (state : GeneralNominalSupport.Tracked roles) : GenerationGuard state (packet wrapping) := by
  rintro name ⟨clause,member,used⟩
  have zero : name = 0 := by
    cases wrapping <;> simp only [packet,Bool.false_eq_true,ite_false,ite_true] at member used
    all_goals have same := List.mem_singleton.mp member
    all_goals subst clause
    all_goals simpa [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using used
  subst name
  exact ⟨origin,usable wrapping⟩

theorem input_empty (wrapping : Bool) : GeneralNominalPacketSupport.inputSchema (packet wrapping) = {} := by
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration (packet wrapping).declaration = (packet wrapping).declaration := by
    cases wrapping <;> simp [packet,GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  cases wrapping <;> simp [packet,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,GeneralDeclarationPatterns.normalize,
    GeneralNominalMaterialization.generated,List.ofFn_succ]

theorem display_guard : GeneralNominalSharedSteps.PacketGuard (initial (context true) displayRoot) (packet false) [] := by
  have old := GeneralNominalSupportExamples.display_guard
  refine ⟨GeneralNominalValueSupport.source_packet _ _ old,?_,generation false _,?_⟩
  · exact GeneralNominalSharedPositive.initial_decision _ _ _ _ _ old.2
  · exact empty_input_coherent (by rw [input_empty])

theorem wrap_guard : GeneralNominalSharedSteps.PacketGuard (initial (context true) wrapRoot) (packet true) [] := by
  have old := GeneralNominalSupportExamples.wrap_guard
  refine ⟨GeneralNominalValueSupport.source_packet _ _ old,?_,generation true _,?_⟩
  · exact GeneralNominalSharedPositive.initial_decision _ _ _ _ _ old.2
  · exact empty_input_coherent (by rw [input_empty])

abbrev lenPacket : Packet roles :=
  ⟨GeneralNominalRecursiveExamples.lenRegistry,GeneralNominalMixedExamples.context,
    GeneralNominalDemandMerging.pointSite GeneralNominalRecursiveExamples.lenRoot,
    GeneralNominalRecursiveExamples.len,GeneralNominalRecursiveExamples.len_checked,[(1,1)]⟩

theorem len_generation (state : GeneralNominalSupport.Tracked roles) : GenerationGuard state lenPacket :=
  no_children_guard rfl

theorem len_input_coherence : InputCoherence lenPacket :=
  GeneralNominalSharedPositive.leaf_input_coherent lenPacket rfl

theorem pump_leaf_coherence : InputCoherence GeneralNominalSharedPump.leaf :=
  GeneralNominalSharedPositive.leaf_input_coherent _ rfl

end Yulang.GeneralNominalSharedExamples
