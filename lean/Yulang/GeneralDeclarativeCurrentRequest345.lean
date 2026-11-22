import Yulang.GeneralNominalVersionedMixedReady235
import Yulang.GeneralNominalVersionedMixedCompletionRequests235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentRequest345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps (State)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalCenteredHeadMatStepRoles (Origin Invariant alias_color color_of_origin)
open GeneralNominalSaturationState (Alias)

def Attributed (r : Registry) (seed : Nat) (root focus : Occurrence rs) (state : State rs)
    (output : GeneralSourceState.Output) : Prop :=
  ∃ (physical request : Nat) (site : GeneralNominalDemandMerging.Site rs), state.erased.current.sites[physical]? = some site ∧
    site.occurrence.demand.outputs[request]? = some output ∧
    Alias state.erased.current focus.identity site.occurrence.identity ∧
    Origin r seed root site.occurrence ∧ focus.demand.role = site.occurrence.demand.role

theorem attributed_iff {r : Registry} {root focus : Occurrence rs} {state : State rs}
    (checked : Checked r) (valid : Invariant r seed root state)
    (focusOrigin : Origin r seed root focus) :
    output ∈ requests state focus ↔ Attributed r seed root focus state output := by
  constructor
  · intro member
    obtain ⟨site,present,alias,within⟩ := mem_requests_iff.mp member
    obtain ⟨physical,siteAt⟩ := List.mem_iff_getElem?.mp present
    obtain ⟨request,outAt⟩ := List.mem_iff_getElem?.mp within
    have origin := valid.raw _ present
    have eq := alias_color valid alias
    rw [color_of_origin checked focusOrigin,color_of_origin checked origin] at eq
    exact ⟨physical,request,site,siteAt,outAt,alias,origin,eq⟩
  · rintro ⟨physical,request,site,siteAt,outAt,alias,_,_⟩
    exact mem_requests_iff.mpr ⟨site,List.mem_iff_getElem?.mpr ⟨physical,siteAt⟩,alias,
      List.mem_iff_getElem?.mpr ⟨request,outAt⟩⟩

theorem declared {r : Registry} {root focus : Occurrence rs} {state : State rs} {p : Plan rs}
    (checked : Checked r) (valid : Invariant r seed root state)
    (focusOrigin : Origin r seed root focus) (role : p.packet.declaration.role = focus.demand.role) :
    GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state focus p := by
  intro output member
  obtain ⟨_,request,site,_,outAt,_,_,same⟩ := (attributed_iff checked valid focusOrigin).mp member
  have inSite := List.mem_iff_getElem?.mpr ⟨request,outAt⟩
  rw [role,same]
  exact site.occurrence.demand.declared output inSite

end Yulang.GeneralDeclarativeCurrentRequest345
