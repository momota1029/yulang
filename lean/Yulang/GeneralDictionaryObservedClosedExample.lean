import Yulang.GeneralDictionaryObservedClosedRequests
import Yulang.GeneralNominalExamples

/-! A non-scalar request at an inhabited existing nominal source; it is not
covered by the earlier scalar-only certificate. No fresh output is claimed. -/
namespace Yulang.GeneralDictionaryObservedClosedExample
open GeneralDictionaryObservedClosedRequests GeneralNominalMaterialization
open GeneralNominalExamples

abbrev request : Request := ⟨.app 0 [.app 2 []],0,.actual⟩

abbrev tree : Tree (state true) 0 (.nominal 0 [.scalar .int]) :=
  Tree.one (state := state true) 0 1 listDescriptor rfl rfl (.scalar 1 .int rfl)

theorem observed : Observed (state true) interpretation [request] := by
  intro r member
  have same := List.mem_singleton.mp member
  subst r
  refine ⟨0,rfl,?_⟩
  simpa [GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,interpretation,request] using (show Nonempty (Tree (state true) 0 (.nominal 0 [.scalar .int])) from ⟨tree⟩)

theorem not_scalar_observed :
    ¬ GeneralDictionaryObservedScalarRequests.Observed (state true) interpretation [request] := by
  intro h
  obtain ⟨slot,base,target,head,_⟩ := h request (List.mem_singleton_self _)
  have zero : slot = 0 := Fin.ext target.symm
  subst slot
  cases head

/-- Both the root nominal test and its exact argument projection test remain. -/
theorem tests_exact : (generated (state true) interpretation [request]).tests =
    [(.source 0,.nominal 0 1),(.nominal (.source 0) 0 0,.scalar .int)] := by
  simp [generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,interpretation,
    schema,schemas,Schema.append]

theorem every_source_model (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report (state true))
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) assignment) :
    Models (state true) declaration capture report (generated (state true) interpretation [request]) assignment :=
  generated_models (state true) interpretation [request] observed declaration capture report assignment valid

/-- Explicitly inhabited, rather than an implication from inconsistent Models. -/
theorem inhabited_request_models (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : GeneralNominalRecursiveInspection.Report (state true)) :
    GeneralNominalState.Models (state true) model ∧
      Models (state true) declaration capture report (generated (state true) interpretation [request]) model :=
  ⟨state_models true,every_source_model declaration capture report model (state_models true)⟩
end Yulang.GeneralDictionaryObservedClosedExample
