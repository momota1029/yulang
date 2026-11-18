import Yulang.GeneralDictionaryOutputDepthInstall252
import Yulang.GeneralPatternAdditiveDepth253
namespace Yulang.GeneralDictionaryOutputDepthRepair253
open GeneralDictionaryOutputDepth252
open GeneralDictionaryOutputDepthInstall252
abbrev newDepth := GeneralPatternAdditiveDepth253.depth

/-- The same operational witness that refuted max now realizes the additive
bound exactly. No different input or freely chosen output is substituted. -/
theorem sharp : newDepth expanded = newDepth template + newDepth rootPattern := rfl

theorem additive : newDepth expanded ≤ newDepth template + newDepth rootPattern :=
 GeneralPatternAdditiveDepth253.subst_depth template (fun _ => rootPattern) (newDepth rootPattern) (fun _ => Nat.le_refl _)

theorem source_reachable_additive_repair :
 GeneralDeclarations.Checked sourceRegistry ∧
 B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed ∧
 (∀ assignment, GeneralNominalVersionedJournal232.Models installed assignment → CommonNominalFullCarrier.Equivalent (assignment 3).1 P) ∧
 newDepth expanded = newDepth template + newDepth rootPattern ∧
 max (newDepth rootPattern) (newDepth template) < newDepth expanded :=
 ⟨source_checked,point_reachable,output_forced,sharp,by decide +kernel⟩
end Yulang.GeneralDictionaryOutputDepthRepair253
