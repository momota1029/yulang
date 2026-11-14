import Yulang.GeneralNominalCenteredSelectedCompletion

set_option backward.isDefEq.respectTransparency false

/-! The raw value guard is exactly a supported decision at the current frame.
Initial selections supply Joint and empty raw support without a production
premise. Their remaining obligation is centered branch consistency. -/
namespace Yulang.GeneralNominalCenteredCompletionParts
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal GeneralNominalCenteredSelectedCompletion

variable {roles : Roles.RoleDecls}

theorem frame_value_iff (frame : Frame registry state focus key children plan) (support) :
    GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ↔
      GeneralNominalValueSupport.DecisionGuard registry state.erased focus support := by
  rcases plan with ⟨⟨preg,pctx,site,declaration,checked,bounds⟩,input,inputEq⟩
  have reg : preg = registry := frame.registry_eq
  have ctx : pctx = state.erased.current.context := frame.context_eq
  have occurrence : site.occurrence = focus := frame.occurrence_eq
  subst preg; subst pctx
  constructor
  · rintro ⟨guard,grounded⟩
    exact ⟨occurrence ▸ guard.2,grounded⟩
  · rintro ⟨decision,grounded⟩
    refine ⟨⟨⟨?_,?_,?_⟩,?_⟩,grounded⟩
    · exact occurrence.symm ▸ decision.1
    · exact occurrence.symm ▸ decision.2.1
    · exact decision.2.2 declaration frame.visible frame.role_eq bounds frame.located
    · exact occurrence.symm ▸ decision

theorem initial_decision (guard : DecisionGuard registry (initial context root) root) :
    GeneralNominalValueSupport.DecisionGuard registry (initial context root).erased root [] := by
  have ready (name) (given : GeneralNominalCenteredSupport.ReadyAt
      (initial context root).erased (initial context root).sourceSites (initial context root).plans name) :
      GeneralNominalSupport.ReadyAt (initial context root).erased [] name := by
    obtain ⟨test,observation,head,_⟩ := given
    exact ⟨test,observation,head,GeneralNominalSupport.source_supported _ _ _ _ head []⟩
  refine ⟨⟨(by intro _ member; cases member),fun index => ready _ (guard.1 index),?_⟩,
    GeneralNominalValueSupport.empty_supported _ _⟩
  intro declaration member role bounds located slot visited
  exact ready _ (guard.2 declaration member role bounds located slot visited)

theorem selected_initial_value
    (selected : Local registry (initial context root) root (.selected key children))
    (frame : Frame registry (initial context root) root key children plan) :
    GeneralNominalValueSupport.PacketGuard (initial context root).erased plan.packet [] :=
  (frame_value_iff frame []).mpr (initial_decision
    (GeneralNominalCenteredInspection.selected_guards (selected_old selected)).1)

theorem frame_branch (frame : Frame registry state focus key children plan) :
    ∃ model, plan.packet.Holds model := by
  obtain ⟨_,_,_,bounds,located,_,_,model,holds⟩ := frame.prepared
  have same : bounds = plan.packet.bounds := Option.some.inj (located.symm.trans frame.located)
  subst bounds
  refine ⟨model,?_⟩
  change GeneralNominalRecursiveCandidates.BranchModels plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds model
  rw [frame.occurrence_eq]
  exact holds

theorem initial_joint (frame : Frame registry (initial context root) root key children plan) :
    GeneralNominalJointCandidates.Joint registry (initial context root).erased.current root key := by
  rcases plan with ⟨⟨preg,pctx,site,declaration,checked,bounds⟩,input,inputEq⟩
  have reg : preg = registry := frame.registry_eq
  have ctx : pctx = context := frame.context_eq
  subst preg; subst pctx
  obtain ⟨model,holds⟩ := frame_branch frame
  have branch : GeneralNominalRecursiveCandidates.BranchModels registry context root
      declaration checked bounds model := by
    have same : site.occurrence = root := frame.occurrence_eq
    exact same ▸ holds
  have result := GeneralNominalJointCandidates.initial_joint registry context root
    declaration frame.visible checked frame.role_eq bounds frame.located frame.prepared model branch
  exact frame.key_eq ▸ result

theorem initial_common_model_iff
    (frame : Frame registry (initial context root) root key children plan)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) :
    (∃ model, Models (initial context root) model ∧ plan.Holds model) ↔
      ∃ model, plan.packet.Holds model ∧ plan.Equations model := by
  constructor
  · rintro ⟨model,_,holds⟩; exact ⟨model,holds⟩
  · rintro ⟨model,holds⟩
    refine ⟨model,(point_initial_models context root point model).mpr ?_,holds⟩
    have source := (GeneralNominalRecursiveCandidates.branch_interval_sound
      plan.packet.registry plan.packet.context plan.packet.site.occurrence plan.packet.declaration
      plan.packet.checked plan.packet.bounds model holds.1).1
    rw [frame.context_eq] at source
    exact source

theorem initial_completion_iff
    (selected : Local registry (initial context root) root (.selected key children))
    (frame : Frame registry (initial context root) root key children plan)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) :
    Completion registry (initial context root) plan ↔
      ∃ model, plan.packet.Holds model ∧ plan.Equations model := by
  constructor
  · rintro ⟨_,support,_,common⟩
    exact (initial_common_model_iff frame point).mp common
  · intro common
    refine ⟨?_,[],selected_initial_value selected frame,(initial_common_model_iff frame point).mpr common⟩
    simpa only [frame.occurrence_eq,frame.key_eq] using initial_joint frame


theorem frame_context_model (frame : Frame registry state focus key children plan) :
    ∃ model, GeneralNominalState.Models state.erased.current.context.state model := by
  obtain ⟨model,branch⟩ := frame_branch frame
  have source := (GeneralNominalRecursiveCandidates.branch_interval_sound
    plan.packet.registry plan.packet.context plan.packet.site.occurrence plan.packet.declaration
    plan.packet.checked plan.packet.bounds model branch).1
  rw [frame.context_eq] at source
  exact ⟨model,source⟩

theorem common_model_iff (state : State roles) (plan : Plan roles) :
    (∃ model, Models state model ∧ plan.Holds model) ↔
      ∃ model, GeneralNominalSaturationState.Models state.erased.current model ∧
        plan.packet.Holds model ∧ (∀ site ∈ state.sites, site.Holds model) ∧
        (∀ prior ∈ state.plans, prior.Equations model) ∧ plan.Equations model := by
  constructor
  · rintro ⟨model,⟨raw,sites,prior⟩,packet,equations⟩
    exact ⟨model,raw,packet,sites,prior,equations⟩
  · rintro ⟨model,raw,packet,sites,prior,equations⟩
    exact ⟨model,⟨raw,sites,prior⟩,packet,equations⟩

theorem completion_parts_iff (frame : Frame registry state focus key children plan) :
    Completion registry state plan ↔
      GeneralNominalJointCandidates.Joint registry state.erased.current focus key ∧
      (∃ support, GeneralNominalValueSupport.DecisionGuard registry state.erased focus support) ∧
      ∃ model, Models state model ∧ plan.Holds model := by
  constructor
  · rintro ⟨joint,support,values,common⟩
    exact ⟨by simpa only [frame.occurrence_eq,frame.key_eq] using joint,
      ⟨support,(frame_value_iff frame support).mp values⟩,common⟩
  · rintro ⟨joint,⟨support,values⟩,common⟩
    exact ⟨by simpa only [frame.occurrence_eq,frame.key_eq] using joint,
      support,(frame_value_iff frame support).mpr values,common⟩

end Yulang.GeneralNominalCenteredCompletionParts
