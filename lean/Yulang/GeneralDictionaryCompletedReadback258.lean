import Yulang.GeneralDictionaryOutputPublic258
import Yulang.GeneralPatternAdditiveDepth253
namespace Yulang.GeneralDictionaryCompletedReadback258
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryOutputFrame258 (complete)
open CommonNominalFullCarrier

theorem closed : expanded.variables = [] := by decide

theorem meaning : GeneralNominalCenteredHeadMatPatternSemantics.eval
 (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
 (fun _ => .bottom) expanded = P := rfl

theorem depth : GeneralPatternAdditiveDepth253.depth expanded = 4 := rfl

/-- A single source/declaration-derived closed representative works for every
initial model AFTER explicit completion. No Evidence premise is assumed here;
the specific source's evidence and installation were constructed above. -/
theorem uniform (assignment : Assignment) (source : GeneralNominalState.Models snapshot assignment) :
 Equivalent (complete assignment 3).1
   (GeneralNominalCenteredHeadMatPatternSemantics.eval
     (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
     (fun _ => .bottom) expanded) ∧
 expanded.variables = [] ∧ GeneralPatternAdditiveDepth253.depth expanded ≤ 4 := by
 rw [meaning]
 exact ⟨GeneralDictionaryOutputDepthInstall252.output_forced _
   (GeneralDictionaryOutputCompletion258.installed_models assignment source),closed,by rw [depth]; exact Nat.le_refl _⟩

theorem not_before_completion :
 GeneralNominalVersionedJournal232.Models initial (GeneralDictionaryPendingOutput258.replace .bottom) ∧
 ¬ Equivalent (GeneralDictionaryPendingOutput258.replace .bottom 3).1
   (GeneralNominalCenteredHeadMatPatternSemantics.eval
     (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
     (fun _ => .bottom) expanded) := by
 rw [meaning]
 exact ⟨GeneralDictionaryPendingOutput258.initial_models .bottom,GeneralDictionaryOutputPremise258.bottom_not_expected⟩
end Yulang.GeneralDictionaryCompletedReadback258
