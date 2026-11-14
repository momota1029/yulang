import Yulang.GeneralNominalHeadInitialCommon188

/-! A real initial head survivor supplies its packet and centered Frame.
No historical installation or chosen-head model is used in this construction. -/
namespace Yulang.GeneralNominalHeadInitialFrame188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadOutputs (Frame)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem survivor_frame (context : GeneralNominalCandidates.Context)
    (survivor : Survivor registry context root key children) :
    ∃ candidate : Plan roles, Frame registry (initial context root).core root key candidate ∧
      candidate.packet.children = children := by
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,kids⟩ := survivor
  let packet : GeneralNominalSaturationState.Packet roles :=
    ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩
  let candidate : Plan roles := ⟨packet,rootSite context.state.seed root,rfl⟩
  refine ⟨candidate,?_,?_⟩
  · refine ⟨rfl,rfl,rfl,identity,?_,?_,visible,role,located,prepared⟩
    · exact List.mem_singleton_self _
    · exact List.mem_singleton_self _
  · exact kids.symm

theorem initial_frame (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (survivor : Survivor registry state.core.erased.current.context root key children) :
    ∃ candidate : Plan roles, Frame registry state.core root key candidate ∧
      candidate.packet.children = children := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  exact survivor_frame context survivor

end Yulang.GeneralNominalHeadInitialFrame188
