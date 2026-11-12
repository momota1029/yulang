import Yulang.GeneralDictionaryVariableTreeSelected

namespace Yulang.GeneralDictionaryVariableTreeInstallation
open GeneralDictionaryVariableTreeExample GeneralDictionaryVariableTreeInitialJoint
open GeneralDictionaryVariableTreeSelected GeneralDictionaryVariableTreeEvidence
open GeneralNominalBranchExample (state context root model state_models)
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
    · exact ⟨model,initial_models,
        GeneralDictionaryVariableTree.branch_models context registry root declaration checked shape model state_models⟩
    · exact initial_joint
  · rw [packet_children]; exact selected
  · intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current packet := by
  intro done
  have childPresent : child ∈ packet.children := by rw [packet_children,children_exact]; exact List.mem_singleton_self _
  have impossible := done.2 child childPresent
  cases impossible

theorem guard : GeneralNominalSupportSteps.PacketGuard start packet [] := by
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl _ rfl⟩,decisions⟩

noncomputable abbrev installed := GeneralNominalSupportSteps.install start packet []

theorem install_at : GeneralNominalSupportSteps.At registry start root installed :=
  .install packet [] enabled novel guard

theorem install_step : GeneralNominalSupportSteps.Step registry root start installed :=
  ⟨root,.root,install_at⟩

theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry start root := by
  intro stable
  exact stable root .root installed install_at
end Yulang.GeneralDictionaryVariableTreeInstallation
