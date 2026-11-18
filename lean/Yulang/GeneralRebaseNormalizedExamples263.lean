import Yulang.GeneralRebaseHeadSupport263
import Yulang.GeneralDictionaryDefault214ActualShadowRegression
import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralNominalVersionedCurrentProjection237

namespace Yulang.GeneralRebaseNormalizedExamples263
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefault214ActualShadowRegression

/-- The inherited shadowed variable is a raw read but is not needed by the
cross-Plan theorem. No agreement at binder77 is assumed. -/
theorem shadow_body (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last) (target : Nat) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment (.explicit equation) ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment (.explicit equation) := by
 apply GeneralRebaseNormalizedBody263.explicit_body first last assignment layout equation target
 intro name member
 simp [equation,pattern,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.hide,
   GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.variablesArgs,
   GeneralDeclarationPatterns.normalizeArgs] at member

theorem shadow_boundary : 77 ∈ GeneralNominalCenteredHeadMatExtension.names expression ∧
 77 ∉ (GeneralDeclarationPatterns.normalize pattern).variables := ⟨raw_dependency,normalized_absent⟩

open GeneralDictionaryOutputDepth252 in
/-- A source-backed, inhabited explicit body with normalized variable0. The
same-Plan instance exercises actual Inputs and Finished, not a vacuous body. -/
theorem actual_head_support : GeneralRebaseNormalizedBody263.Compatible plan plan model := by
 apply GeneralRebaseHeadSupport263.from_inputs plan plan model ⟨rfl,rfl,rfl⟩ rfl rfl rfl
 · intro index; exact GeneralDictionaryDefaultExpression209.equivalent_refl _
 · exact packet_holds.2.1
 · exact packet_holds.2.1
 · exact GeneralNominalVersionedCurrentProjection237.frame_finished plan frame

open GeneralDictionaryOutputDepth252 in
theorem normalized_variable_used : 0 ∈ (GeneralDeclarationPatterns.normalize template).variables := by decide +kernel
end Yulang.GeneralRebaseNormalizedExamples263
