import Yulang.GeneralDictionaryComputedOutputPlans
import Yulang.GeneralDictionaryBinderLocationExamples

/-!
# One checked visible declaration supplies plans and computed output terms

The fixture supplies head terms and locations, never output terms to lookup.
The head predicate remains an explicit premise; these tests do not elaborate
heads or establish unrestricted general dictionary completion.
-/
namespace Yulang.GeneralDictionaryComputedOutputExamples
open GeneralDeclarations GeneralDeclarationDemands GeneralSourceDictionaries
open GeneralDeclarationExamples (constructors roles display display_checked)
open GeneralDictionaryOutputBinderExamples
open GeneralDictionaryBinderLocationExamples
open GeneralDictionaryEmissionPlans
open GeneralDictionaryComputedOutputPlans

abbrev registry : Registry := ⟨constructors, roles, [display, binderWrap]⟩

theorem registry_checked : Checked registry := by
  refine ⟨by simp, ?_⟩
  intro declaration member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact display_checked
  · exact binderWrap_checked

abbrev root : Occurrence roles := ⟨9, demand⟩
abbrev frame : Frame roles where
  capture := fun _ => capture
  allocation := fun _ clause => allocations clause
  identity := fun _ _ clause => clause

abbrev result : Result state root :=
  ⟨children frame root binderWrap binderWrap_checked, located⟩

theorem actual_lookup : lookup registry registry_checked frame root 2 inputs = some result := by
  apply (lookup_exact registry registry_checked frame root 2 inputs result).mpr
  exact ⟨binderWrap, by simp, rfl, rfl, reconstructs_prior_located, rfl⟩

theorem absent_key_defers : lookup registry registry_checked frame root 99 inputs = none := rfl

theorem wrong_role_defers : lookup registry registry_checked frame root 1 inputs = none := rfl

theorem computes_repeated_outputs :
    (lookup registry registry_checked frame root 2 inputs).map
      (fun r => [r.located.output ⟨0, by decide⟩, r.located.output ⟨1, by decide⟩]) =
      some [.var 2, .var 2] := by
  rw [actual_lookup]
  rfl

theorem retains_distinct_targets :
    (lookup registry registry_checked frame root 2 inputs).map
      (fun r => [state.source (r.located.target ⟨0, by decide⟩),
        state.source (r.located.target ⟨1, by decide⟩)]) = some [3, 4] := by
  rw [actual_lookup]
  rfl

theorem supplies_complete_plan :
    Plan registry registry_checked frame root 2 result.children :=
  lookup_plan registry registry_checked frame root 2 inputs result actual_lookup

/-- The remaining premise concerns the selected declaration head only. -/
theorem supplies_concrete_terms
    (heads : HeadInstances roles state)
    (head : heads root binderWrap capture inputs.head) :
    Terms registry (fun _ => frame) heads root 2 result.located := by
  apply lookup_terms registry registry_checked (fun _ => frame) heads root 2 inputs result actual_lookup
  intro declaration present identity _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · cases identity
  · exact head

theorem same_visible_declaration :
    ∃ declaration, ∃ _present : declaration ∈ registry.declarations,
      declaration.id = 2 ∧ declaration.role = root.demand.role ∧
      GeneralDictionaryPlannedOutputs.OutputPlan registry registry_checked frame root 2
        (result.children, GeneralDictionaryAssociatedProvenance.outputs roles declaration root.demand) ∧
      GeneralDictionaryOutputBinderTerms.Interpreted declaration
        (frame.capture declaration.id) result.located :=
  lookup_output_plan registry registry_checked frame root 2 inputs result actual_lookup

abbrev shiftedRoot : Occurrence roles := ⟨9, shiftedDemand⟩
abbrev shiftedFrame : Frame roles := { frame with capture := fun _ => shiftedCapture }
abbrev shiftedResult : Result shiftedState shiftedRoot :=
  ⟨children shiftedFrame shiftedRoot binderWrap binderWrap_checked, shiftedLocated⟩

theorem nonidentity_lookup :
    lookup registry registry_checked shiftedFrame shiftedRoot 2 shiftedInputs = some shiftedResult := by
  apply (lookup_exact registry registry_checked shiftedFrame shiftedRoot 2 shiftedInputs shiftedResult).mpr
  exact ⟨binderWrap, by simp, rfl, rfl, builds_nonidentity_locations, rfl⟩

/-- The local RHS slot is 2 while its actual source identity is 12. -/
theorem nonidentity_computed_output :
    (lookup registry registry_checked shiftedFrame shiftedRoot 2 shiftedInputs).map
      (fun r => GeneralDictionaryStateEquations.liftType shiftedState
        (r.located.output ⟨0, by decide⟩)) = some (.var 12) := by
  rw [nonidentity_lookup]
  rfl

theorem nonidentity_repeated_targets :
    (lookup registry registry_checked shiftedFrame shiftedRoot 2 shiftedInputs).map
      (fun r => [shiftedState.source (r.located.target ⟨0, by decide⟩),
        shiftedState.source (r.located.target ⟨1, by decide⟩)]) = some [13, 14] := by
  rw [nonidentity_lookup]
  rfl

abbrev absentFrame : Frame roles := { frame with capture := fun _ => absentCapture }

/-- A matching checked key/role still defers if a captured binder is absent. -/
theorem missing_binder_defers :
    lookup registry registry_checked absentFrame shiftedRoot 2 shiftedInputs = none := by
  change (GeneralDictionaryBinderLocations.build binderWrap absentCapture shiftedInputs).map
    (fun located => (⟨children absentFrame shiftedRoot binderWrap binderWrap_checked, located⟩ :
      Result shiftedState shiftedRoot)) = none
  rw [missing_binder_source_defers]
  rfl

end Yulang.GeneralDictionaryComputedOutputExamples
