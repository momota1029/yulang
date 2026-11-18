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
