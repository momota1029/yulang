import Yulang.GeneralDictionaryNominalCandidateReadback
import Yulang.GeneralNominalExamples

/-!
# Computed nominal frames retain actual source child identities

The root Plan is obtained from the existing display Survivor. The leaf Plan
uses the visible terminal Int declaration only. Thus this is exact structural
reconstruction, not a proof that the complete forest has candidate evidence.
-/
namespace Yulang.GeneralDictionaryNominalCandidateReadbackExamples
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries
open GeneralDictionaryNominalCandidateReadback

abbrev payload : GeneralDictionaryReadback.Payload := .node 1 [.node 3 []]
abbrev sourceTree : Dictionary roles := .node displayRoot 1 [.node displayChild 3 []]

theorem root_plan : GeneralDictionaryEmissionPlans.Plan registry registry_checked
    (frames registry (context true) displayRoot) displayRoot 1 [displayChild] :=
  survivor_plan registry registry_checked (context true) displayRoot 1 [displayChild] display_survivor

/-- No leaf applicability claim is needed for terminal plan reconstruction. -/
theorem leaf_plan : GeneralDictionaryEmissionPlans.Plan registry registry_checked
    (frames registry (context true) displayChild) displayChild 3 [] := by
  refine ⟨intDisplay, by simp, rfl, rfl, ?_⟩
  simp [GeneralDictionaryEmissionPlans.children, GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll, intDisplay]

theorem source_plan_evidence :
    Evidence (GeneralDictionaryPayloadReconstruction.Rule registry registry_checked
      (frames registry (context true))) sourceTree := by
  apply Evidence.node root_plan
  intro child member
  have same := List.mem_singleton.mp member
  subst child
  apply Evidence.node leaf_plan
  intro grandchild absent
  cases absent

/-- The executor takes only the raw key tree, root, context and checked registry. -/
theorem tree_reconstructed : reconstruct registry registry_checked (context true) payload displayRoot =
    some sourceTree :=
  GeneralDictionaryPayloadReconstruction.reconstruct_complete registry registry_checked
    (frames registry (context true)) sourceTree source_plan_evidence

theorem omitted_child_defers :
    reconstruct registry registry_checked (context true) (.node 1 []) displayRoot = none := by
  have found := (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked
    (frames registry (context true) displayRoot) displayRoot 1 [displayChild]).mpr root_plan
  rw [reconstruct, GeneralDictionaryPayloadReconstruction.reconstruct, found]
  change (GeneralDictionaryPayloadReconstruction.reconstructChildren registry registry_checked
    (frames registry (context true)) [] [displayChild]).bind
      (fun trees => some (Dictionary.node displayRoot 1 trees)) = none
  rw [GeneralDictionaryPayloadReconstruction.reconstructChildren]
  rfl

/-- Exact identity and full demand, rather than only the number of children. -/
theorem source_child_preserved :
    ∃ result, reconstruct registry registry_checked (context true) payload displayRoot = some result ∧
      observations result = [(displayRoot, 1), (displayChild, 3)] :=
  ⟨sourceTree, tree_reconstructed, rfl⟩

theorem source_readback : Readback displayRoot payload sourceTree :=
  (GeneralDictionaryPayloadReconstruction.reconstruct_sound registry registry_checked
    (frames registry (context true)) payload displayRoot sourceTree tree_reconstructed).1

end Yulang.GeneralDictionaryNominalCandidateReadbackExamples
