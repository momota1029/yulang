import Yulang.GeneralDictionaryNonpointStrictOutput

/-! Directional actual replay cannot be silently used for lower-mode requests.
This is a materialization-mode boundary, not a counterexample to operational
reobservation or to the proved actual root-output transport. -/
namespace Yulang.GeneralDictionaryNonpointModeBoundary
open GeneralDictionaryNonpointStrict
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseSchema
open GeneralNominalMaterialization GeneralNominalRecursiveInspection CommonNominalFullCarrier
abbrev d := GeneralDictionaryNonpointStrictOutput.declaration
abbrev r := GeneralDictionaryNonpointStrictOutput.registry
abbrev target := GeneralDictionaryNonpointStrictOutput.outputRoot
abbrev body : Schema := ⟨[⟨7,.source 4,.lower⟩],[],false⟩

theorem old_lower : VariableHolds d (oldCapture shape r target.identity d) model 7 .lower leafValue := by
  unfold VariableHolds
  simp only [d,GeneralDictionaryNonpointStrictOutput.declaration,GeneralDeclarations.Declaration.outputNames]
  unfold oldCapture
  rw [bindings_before shape]
  change Equivalent leafValue (model loId).1
  rw [at_merge_lower]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem current_lower_fails :
    ¬ VariableHolds d (newCapture shape r target.identity d) model 7 .lower leafValue := by
  intro h
  unfold VariableHolds at h
  simp only [d,GeneralDictionaryNonpointStrictOutput.declaration,GeneralDeclarations.Declaration.outputNames] at h
  unfold newCapture at h
  rw [bindings_after shape] at h
  change Equivalent leafValue (model 3).1 at h
  apply merged_lower_not_equivalent
  rw [at_merge_lower]
  exact h

theorem old_schema : Models source d (oldCapture shape r target.identity d)
    (inspect source (query shape) (0,0) none) body model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member; cases member
  · intro entry member
    cases List.mem_singleton.mp member
    refine ⟨⟨(model 4).1,.source 4⟩,?_⟩
    intro actual seen
    have same := nominal_observation_unique model (.source 4) actual (model 4).1 seen (.source 4)
    unfold VariableHolds
    simp only [d,GeneralDictionaryNonpointStrictOutput.declaration,GeneralDeclarations.Declaration.outputNames]
    unfold oldCapture
    rw [bindings_before shape]
    change Equivalent actual (model loId).1
    rw [at_merge_lower]
    rw [at_upper] at same
    exact same
  · intro first one last two name mode1 mode2 a b seenA seenB
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact nominal_observation_unique model (.source 4) a b seenA seenB
  · intro entry member captured present same actual
    cases List.mem_singleton.mp member
    cases actual

theorem current_schema_fails :
    ¬ Models revision.snapshot d (newCapture shape r target.identity d)
      (inspect revision.snapshot (query shape) ((0 : Fin 5),(0 : Fin 5)) none) body model := by
  intro valid
  have h := (valid.2.1 ⟨7,.source 4,.lower⟩ (by simp)).2 (model 4).1 (.source 4)
  apply current_lower_fails
  rw [at_upper] at h
  exact h
end Yulang.GeneralDictionaryNonpointModeBoundary
