import Yulang.GeneralNominalHeadBranchFrame187

/-! Initial point-root head preparation supplies a model of the current journal
and the candidate branch simultaneously. This removes that compatibility
premise at the initial root, not at arbitrary reachable states. Centered
inspection projection constraints remain a separate obligation. -/
namespace Yulang.GeneralNominalHeadInitialCommon188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadCandidates (HeadModels)
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

 theorem initial_models_iff (context : GeneralNominalCandidates.Context)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model := by
  rw [GeneralNominalCenteredHeadStepEffects.initial_models,GeneralNominalCenteredSteps.initial_models]
  exact ⟨And.left,fun valid => ⟨valid,point_root_holds context.state.seed root point model⟩⟩

 theorem frame_prepared_model (state : State roles) (candidate : Plan roles)
    (frame : Frame registry state.core root key candidate) :
    ∃ model, HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared candidate.packet.registry
      candidate.packet.context candidate.packet.site.occurrence candidate.packet.declaration := by
    simpa only [frame.registry_eq,frame.context_eq,frame.occurrence_eq] using frame.prepared
  obtain ⟨_,_,_,bounds,located,_,model,valid⟩ := prepared
  have expected := frame.located
  rw [← frame.occurrence_eq] at expected
  have same : bounds = candidate.packet.bounds := Option.some.inj (located.symm.trans expected)
  subst bounds
  exact ⟨model,valid⟩

 theorem initial_common_model (context : GeneralNominalCandidates.Context)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (candidate : Plan roles) (frame : Frame registry (initial context root).core root key candidate) :
    ∃ model, Models (initial context root) model ∧
      HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  obtain ⟨model,branch⟩ := frame_prepared_model (initial context root) candidate frame
  have privateModels := (GeneralNominalHeadBranchFrame187.head_models_exact candidate model).mp branch
  have source := ((GeneralNominalPacketSupport.private_exact candidate.packet model).mp privateModels.1).1
  have context_eq : candidate.packet.context = context := frame.context_eq
  rw [context_eq] at source
  exact ⟨model,(initial_models_iff context point model).mpr source,branch⟩

 theorem boundary_initial_common_model (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate) :
    ∃ model, Models state model ∧
      HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  exact initial_common_model context point candidate frame

end Yulang.GeneralNominalHeadInitialCommon188
