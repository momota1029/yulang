import Yulang.GeneralCandidateBoundaryParts
import Yulang.GeneralDictionaryHeadlessExamples

/-!
# Output-bearing dictionaries and the current candidate coverage boundary

The newly integrated candidate component deliberately requires no root outputs.
The headless materializer can already construct a genuine output-bearing tree.
This mismatch is a coverage handoff, not a language rejection or a change to
the candidate rules. The candidate-owned definitions remain unchanged.
-/
namespace Yulang.GeneralDictionaryHeadlessCandidateBoundary
open GeneralSourceDictionaries (Occurrence)
open GeneralCandidateBoundaryParts (Context Survivor Prepared)
open GeneralDeclarations (Registry)

/-- This follows from the current explicit conservative emission certificate,
not from any language restriction forbidding associated output obligations. -/
theorem survivor_outputs_empty (registry : Registry) (context : Context roles)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry context root key children) : root.demand.outputs = [] := by
  obtain ⟨_, declaration, _, checked, _, _, prepared, _⟩ := survivor
  obtain ⟨_, _, _, _, _, emissions, _⟩ := prepared
  exact emissions.1

/-- An output-bearing demand is outside this candidate component's current
supported range; this is not the complete language's no-survivor result. -/
theorem output_demand_outside_range (registry : Registry) (context : Context roles)
    (root : Occurrence roles) (outputs : root.demand.outputs ≠ []) :
    ∀ key children, ¬ Survivor registry context root key children := by
  intro key children survivor
  exact outputs (survivor_outputs_empty registry context root key children survivor)

/-- A checked actual producer/leaf recipe already materializes the nonempty
outputs, but cannot yet be joined to the current no-root-output candidate range. -/
theorem prepared_output_tree_outside_range
    (context : Context GeneralDictionaryHeadlessFixture.roles) :
    GeneralDictionaryHeadlessPreparation.prepare GeneralDictionaryHeadlessFixture.registry
      GeneralDictionaryHeadlessFixture.registry_checked
      (fun _ => GeneralDictionaryHeadlessFixture.frame)
      GeneralDictionaryHeadlessExamples.recipe = some GeneralDictionaryHeadlessFixture.tree ∧
    ∀ key children, ¬ Survivor GeneralDictionaryHeadlessFixture.registry context
      GeneralDictionaryHeadlessFixture.root key children := by
  refine ⟨GeneralDictionaryHeadlessExamples.tree_prepared, ?_⟩
  apply output_demand_outside_range
  simp

end Yulang.GeneralDictionaryHeadlessCandidateBoundary
