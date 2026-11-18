import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralNominalSourceTemplateMenu255
import Yulang.GeneralNominalCanonicalBasis255
import Yulang.GeneralNominalNormalizedDepth255
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryTemplateMenu255
open Core.PresenceGeneration (TyTerm)
open GeneralDictionaryOutputDepth252
open GeneralDictionaryAssociatedProvenance
open GeneralNominalTemplateChoices255 (Materialized)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier

abbrev body : Body := .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩
abbrev variables : Mode → Nat → TyTerm Nat := fun _ name => .var (GeneralNominalVersionedFrame231.binder plan name)
abbrev result : Materialized := .nominal 0 [.nominal 0 [.source (.var 2)]]
abbrev basis := GeneralNominalCanonicalBasis255.basis sourceRegistry context []
abbrev policy : Mode → GeneralPresenceCheckedNormal252.Side := fun _ => .lower

theorem supplied : Supplies roles declaration 0 body := .explicit _ (List.mem_singleton_self _) rfl

theorem compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some rhs := rfl

theorem reads_exact : GeneralNominalTemplateChoices255.reads .actual rhs = [(.actual,0)] := rfl

theorem materialized : GeneralNominalRebaseEffectView243.compile variables .actual rhs = result := by
 change .nominal 0 [.nominal 0 [.source (.var (GeneralNominalVersionedFrame231.binder plan 0))]] = result
 rw [binder_exact]

theorem actual_finite_menu : result ∈ GeneralNominalSourceTemplateMenu255.menu registry context root [.var 2] := by
 rw [← materialized]
 apply GeneralNominalSourceTemplateMenu255.source_compiled (state := initial) (output := ⟨0,3⟩) .refl frame
   (List.mem_singleton_self _) supplied compiled [.var 2] variables .actual
 intro entry present
 rw [reads_exact] at present
 cases List.mem_singleton.mp present
 change TyTerm.var (GeneralNominalVersionedFrame231.binder plan 0) ∈ [TyTerm.var 2]
 rw [binder_exact]
 exact List.mem_singleton_self _

theorem normalized_reference : GeneralPresenceCheckedNormal252.normalize .lower basis (.var 2) = .var 2 := by decide +kernel

theorem supported : GeneralNominalTemplateNormal255.Supported policy basis variables .actual rhs := by
 intro entry present
 rw [reads_exact] at present
 cases List.mem_singleton.mp present
 change GeneralPresenceUnionNormal252.atoms (.var (GeneralNominalVersionedFrame231.binder plan 0)) ⊆ basis
 rw [binder_exact]
 intro atom member
 cases List.mem_singleton.mp member
 decide +kernel

theorem rewritten : GeneralNominalTemplateNormal255.rewrite policy basis variables .actual rhs = result := by
 change .nominal 0 [.nominal 0 [.source (GeneralPresenceCheckedNormal252.normalize .lower basis (.var (GeneralNominalVersionedFrame231.binder plan 0)))]] = result
 rw [binder_exact,normalized_reference]

theorem prepared : GeneralNominalTemplateNormal255.prepare policy basis variables .actual rhs = some result :=
 (GeneralNominalTemplateNormal255.prepare_exact ..).mpr ⟨supported,rewritten.symm⟩

theorem all_models_exact (assignment : GeneralNominalCommonBridge.Assignment) :
 Equivalent (GeneralNominalRebaseEffectView243.eval assignment result)
 (GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan assignment) .actual rhs) := by
 have original : GeneralNominalRebaseEffectView243.eval assignment
   (GeneralNominalRebaseEffectView243.compile variables .actual rhs) =
   GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan assignment) .actual rhs := by
   rw [GeneralNominalRebaseEffectView243.compile_exact]
   rfl
 have exactValue := (GeneralNominalTemplateNormal255.prepare_safe policy basis variables .actual rhs result prepared assignment).2
 rw [original] at exactValue
 exact exactValue

theorem raw_depth_two : GeneralNominalExprDepth253.materializedDepth result = 2 := rfl

theorem source_regression :
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial ∧
 GeneralNominalTemplateNormal255.prepare policy basis variables .actual rhs = some result ∧
 result ∈ GeneralNominalSourceTemplateMenu255.menu registry context root (GeneralNominalTemplateNormal255.leafCandidates basis) ∧
 Equivalent (GeneralNominalRebaseEffectView243.eval model result) P ∧
 GeneralNominalExprDepth253.materializedDepth result = 2 := by
 refine ⟨initial_source,prepared,?_,?_,raw_depth_two⟩
 · exact (GeneralNominalSourceTemplateMenu255.source_prepared (state := initial) (output := ⟨0,3⟩) .refl frame
     (List.mem_singleton_self _) supplied compiled policy basis variables .actual result prepared model).1
 · have exactValue := all_models_exact model
   rw [rhs_value] at exactValue
   exact exactValue
end Yulang.GeneralDictionaryTemplateMenu255
