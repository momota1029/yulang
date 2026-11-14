import Yulang.GeneralNominalMixedTree198
import Yulang.GeneralNominalNonleafCurrent195

/-! The finite mixed rule really uses a recorded parent and an unrecorded child,
without modifying the state or passing a finite list of plans to synthesis. -/
namespace Yulang.GeneralNominalMixedNonleaf198
open GeneralSourceDictionaries GeneralNominalCenteredHeadStepEffects
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193
open GeneralNominalNonleafChild193
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralDeclarationExamples (roles)
open GeneralNominalMixedCompletion198
open GeneralNominalMixedJournal197 (MixedStep)
open GeneralNominalCenteredHeadWFBoundary (boundary)

theorem mixed_path : B4Target.Steps (MixedStep registry displayRoot) start finish := by
  have ordinary := GeneralNominalOrdinaryEvidence191.install_step enabled (root := displayRoot) .root novel
  exact .tail .refl ⟨ordinary.1,Or.inl ordinary.2⟩

theorem parent_recorded : GeneralDictionaryJournalTree.Recorded finish.core.erased.current
    displayRoot 1 [displayChild] :=
  ⟨packet,List.mem_cons_self ..,rfl,rfl,children_exact⟩

theorem child_not_recorded : ¬ ∃ p ∈ finish.core.erased.current.packets,
    p.site.occurrence = displayChild := by
  rintro ⟨p,member,equal⟩
  have same : p = packet := List.mem_singleton.mp member
  subst p
  have ids := congrArg Occurrence.identity equal
  contradiction

theorem completion : TotalCompletion registry finish displayRoot := by
  intro focus generated
  rcases GeneralNominalNonleafCurrent195.generated_cases generated with rfl | rfl
  · exact ⟨1,[displayChild],Or.inl parent_recorded⟩
  · exact ⟨childPlan.packet.declaration.id,childPlan.packet.children,Or.inr
      ⟨childPlan,GeneralNominalNonleafCatalogue195.reusable childPlan (List.mem_singleton_self _),rfl,rfl,rfl⟩⟩

theorem uniform_dictionary :
    ∃ tree : Dictionary roles, tree.root = displayRoot ∧ Evidence (Rule registry finish) tree ∧
      ∀ assignment, Models finish assignment →
        (boundary roles).Evidence registry finish assignment displayRoot (erase tree) :=
  GeneralNominalMixedTree198.uniform_dictionary mixed_path completion

theorem selected_sound : ∀ assignment, Models finish assignment →
    (boundary roles).Evidence registry finish assignment displayRoot (.node 1 [.node 3 []]) :=
  GeneralNominalMixedCompletion198.selected_sound mixed_path (selected_completion completion) _
    GeneralNominalNonleafFinal194.parent_classify

theorem inhabited : Models finish model ∧
    (boundary roles).Evidence registry finish model displayRoot (.node 1 [.node 3 []]) :=
  ⟨final_model,selected_sound model final_model⟩
end Yulang.GeneralNominalMixedNonleaf198
