import Yulang.GeneralDictionaryObservedInitialSelected

/-! The named-output nonterminal source performs an actual guarded first install.
This does not assert that the initial state is stable or that its child succeeds. -/
namespace Yulang.GeneralDictionaryObservedInitialInstallation
open GeneralDictionaryObservedInitialExample GeneralDictionaryObservedInitialSelected
open GeneralNominalExamples (model)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState

abbrev packet : Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,[(0,0)]⟩

theorem packet_children : packet.children = children := rfl

theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,initial],by simp,rfl,rfl,prepared,?_,?_,?_,?_,?_⟩
    · rw [packet_children]
      exact GeneralNominalFeedbackK2.selected_legacy selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member
      subst other
      exact .refl _
    · exact ⟨model,GeneralDictionaryObservedInitialExample.initial_models,every_source_model model source_models⟩
    · exact initial_joint
  · rw [packet_children]; exact selected
  · intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem children_nonempty : children ≠ [] := by
  intro empty
  have count := actual_children_count
  rw [empty] at count
  cases count

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet := by
  intro done
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil children children_nonempty
  have present : child ∈ packet.children := by rw [packet_children]; exact member
  have impossible := done.2 child present
  cases impossible

theorem guard : GeneralNominalSupportSteps.PacketGuard start packet [] :=
  ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl _ rfl⟩,decisions⟩

noncomputable abbrev installed := GeneralNominalSupportSteps.install start packet []

theorem install_at : GeneralNominalSupportSteps.At registry start root installed :=
  .install packet [] enabled novel guard

theorem install_step : GeneralNominalSupportSteps.Step registry root start installed :=
  ⟨root,.root,install_at⟩

theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry start root := by
  intro stable
  exact stable root .root installed install_at

theorem installed_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed := by
  obtain ⟨origin,initial,path⟩ := actual_reachable
  exact ⟨origin,initial,.tail path install_step⟩
end Yulang.GeneralDictionaryObservedInitialInstallation
