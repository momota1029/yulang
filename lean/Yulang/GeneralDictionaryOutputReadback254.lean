import Yulang.GeneralNominalSourceOutputDepth254
import Yulang.GeneralDictionaryOutputDepthInstall252
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOutputReadback254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDictionaryOutputDepth252
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)

/-- The real cycle252 initial source has a nonvacuous current leaf certificate
in its displayed model. No termination of its source scheduler is inferred. -/
theorem evidence : GeneralNominalVersionedEvidence231.Evidence registry initial.core model root (.node 0 []) :=
 GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,
 GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm packet_holds
   GeneralDictionaryOutputDepthInstall252.ready GeneralDictionaryOutputDepthInstall252.classes⟩

theorem computed_bound :
 GeneralNominalSourceOutputDepth254.bound registry context root [rootPattern] root.identity = 4 := by
 decide +kernel

/-- The additive budget applies on every later mixed trace, in every model
with a current evidence certificate for this root. Unlike the old maximum2,
the verified bound4 accommodates the real triple-Foo output. -/
theorem all_later_readbacks
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) initial state)
 (valid : GeneralNominalVersionedJournal232.Models state assignment)
 (evidenced : GeneralNominalVersionedEvidence231.Evidence registry state.core assignment root payload) :
 ∃ result : Pattern, result.variables = [] ∧
 CommonNominalFullCarrier.Equivalent (assignment 3).1
   (eval (algebra registry.constructors context.interpretation) (fun _ => .bottom) result) ∧
 GeneralPatternAdditiveDepth253.depth result ≤ 4 := by
 have result := GeneralNominalSourceOutputDepth254.payload_depth source (fun _ => rfl) ground coverage path valid evidenced
   ⟨0,3⟩ (List.mem_singleton_self _)
 obtain ⟨value,closed,meaning,small⟩ := result
 refine ⟨value,closed,meaning,?_⟩
 change GeneralPatternAdditiveDepth253.depth value ≤ GeneralNominalSourceOutputDepth254.bound registry context root [rootPattern] root.identity at small
 rw [computed_bound] at small
 exact small


theorem initial_readback :
 ∃ result : Pattern, result.variables = [] ∧
 CommonNominalFullCarrier.Equivalent (model 3).1
   (eval (algebra registry.constructors context.interpretation) (fun _ => .bottom) result) ∧
 GeneralPatternAdditiveDepth253.depth result ≤ 4 :=
 all_later_readbacks .refl initial_model evidence

theorem root_input_bounded :
 ∃ result : Pattern,
 GeneralNominalCenteredHeadMatSchemaMass.Part (algebra registry.constructors context.interpretation) plan model 0 result ∧
 result.encode.size ≤ 2 :=
 GeneralNominalSourceReadback254.input_bound source (fun _ => rfl) ground coverage .refl initial_model frame packet_holds
   0 (by decide)

end Yulang.GeneralDictionaryOutputReadback254
