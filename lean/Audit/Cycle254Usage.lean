import Yulang.GeneralNominalRawOutputBudget254
import Yulang.GeneralDictionaryOutputReadback254
import Yulang.GeneralDictionaryDefaultEvidence204Examples
import Yulang.GeneralNominalOutputReadback254
import Yulang.GeneralDictionaryOutputDepth252
namespace Cycle254Usage
open Yulang GeneralDeclarationPatterns GeneralPatternAdditiveDepth253
open GeneralDictionaryOutputDepth252

example : GeneralNominalQueryReadback254.Shaped (.node (.variant 0) [.variables [0,1]]) := by
 simp [GeneralNominalQueryReadback254.Shaped,GeneralNormalizedObservation.Shape.Canonical,GeneralNormalizedObservation.Shape.arity]
example : GeneralNominalQueryReadback254.Shaped
 (GeneralNominalInspection.translate constructors interpretation (normalize (.variant 0 (.join (.var 0) (.var 1))))) := by
 apply GeneralNominalQueryReadback254.translated_shaped
 · exact GeneralNominalRequestCanonical.normalized_tidy _
 · simp [normalize,merge,variantRow,GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,GeneralNominalHeadMatchMass.Complete]
example : covered (normalize (.variant 0 (.join (.var 0) (.var 1)))) = false := rfl
example : ∃ pattern : Pattern,
 GeneralNominalCenteredHeadMatSchemaMass.Part
   (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
   plan model 0 pattern ∧ pattern.encode.size ≤ 2 := by
 have input := GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs
   (fun index => rfl) ground source_model
 exact GeneralNominalInputReadback254.input_part frame packet_holds input 0 (by decide)

example : ∃ result : Pattern, result.variables = [] ∧
 CommonNominalFullCarrier.Equivalent (model 3).1
   (GeneralNominalCenteredHeadMatPatternSemantics.eval
     (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
     (fun _ => .bottom) result) ∧ GeneralPatternAdditiveDepth253.depth result ≤ 4 := by
 have input := GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs
   (fun index => rfl) ground source_model
 exact GeneralNominalOutputReadback254.leaf_root_readback frame packet_holds input rfl
   (coverage.1 declaration (List.mem_singleton_self _)) ⟨template,3,.actual⟩ (by change (⟨template,3,.actual⟩ : GeneralNominalMaterialization.Request) ∈ [⟨template,3,.actual⟩]; exact List.mem_singleton_self _)
end Cycle254Usage

namespace Cycle254DefaultUsage
open Yulang GeneralDeclarationPatterns GeneralPatternAdditiveDepth253
open GeneralDictionaryAllocDefaultSource202
example : ∃ result : Pattern, result.variables = [] ∧
 CommonNominalFullCarrier.Equivalent (model 1).1
   (GeneralNominalCenteredHeadMatPatternSemantics.eval
     (GeneralNominalCenteredHeadMatCompilerSemantics.algebra registry.constructors context.interpretation)
     (fun _ => .bottom) result) ∧ depth result ≤ 1 := by
 have inputs := GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs
   (fun index => rfl) ground source_model
 have body : GeneralNominalCenteredHeadMatEffects.BodyHolds plan 1 model (.default 0 0 (.var 0)) := (GeneralNominalCenteredHeadMatEffects.positional_default plan model (0 : Fin 1)).mpr
   ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
 exact GeneralNominalDefaultReadback254.default_readback inputs rfl rfl rfl body
end Cycle254DefaultUsage

namespace Cycle254BoundaryGuards
open Yulang GeneralDeclarationPatterns GeneralPatternAdditiveDepth253
example : GeneralNominalProducerRank254.rank [1,1,3] 1 = 3 := by decide +kernel
example : GeneralNominalProducerRank254.rank [1,1,3] 3 = 1 := by decide +kernel
example : GeneralNominalProducerRank254.rank [1,1,3] 4 = 0 := by decide +kernel
-- A closed raw representative may get deeper after normalization. This is
-- a syntax-only guard, not a new source-reachable counterexample.
private def row : Pattern := .join
 (.join (.variant 0 (.app 2 [])) (.variant 1 (.app 2 [])))
 (.join (.variant 2 (.app 2 [])) (.variant 3 (.app 2 [])))
example : row.variables = [] := by decide +kernel
example : depth row < depth (normalize row) := by
 simp [row,depth,depths,normalize,normalizeArgs,merge,variantRow,rowPattern,
   Variants.Merged.normalize,Variants.Merged.Raw.insert]
 simp [List.mergeSort,rowPattern,depth,depths]
example : depth row = 4 := by decide +kernel
example : depth (normalize row) = 5 := by
 simp [row,normalize,normalizeArgs,merge,variantRow,rowPattern,
   Variants.Merged.normalize,Variants.Merged.Raw.insert]
 simp [List.mergeSort,rowPattern,depth,depths]
end Cycle254BoundaryGuards

namespace Cycle254RawUsage
open Yulang GeneralDictionaryOutputDepth252
example : GeneralNominalRawOutputBudget254.budget registry context root = 2 := by decide +kernel
example : GeneralNominalRawOutputBudget254.templates registry context root =
 [.nominal 0 [.nominal 0 [.variable 0]]] := rfl
example : GeneralNominalCenteredHeadMatExpressions.Expr.nominal 0 [.nominal 0 [.variable 0]] ∈
 GeneralNominalRawOutputBudget254.templates registry context root := by
 exact GeneralNominalRawOutputBudget254.source_template
   (output := ⟨0,3⟩) (body := .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩)
   B4Target.Steps.refl frame (List.mem_singleton_self _)
   (.explicit _ (List.mem_singleton_self _) rfl) rfl
example (references : GeneralNominalMaterialization.Mode → Nat → Nat) :
 GeneralNominalExprDepth253.materializedDepth
   (GeneralNominalRebaseEffectView243.compile (fun mode name => .var (references mode name)) .actual
     (.nominal 0 [.nominal 0 [.variable 0]])) ≤ 2 := by
 exact GeneralNominalRawOutputBudget254.reference_depth
   (output := ⟨0,3⟩) (body := .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩)
   B4Target.Steps.refl frame (List.mem_singleton_self _)
   (.explicit _ (List.mem_singleton_self _) rfl) rfl references .actual
end Cycle254RawUsage
