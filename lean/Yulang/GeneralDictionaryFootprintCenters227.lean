import Yulang.GeneralDictionarySemanticTrace227
import Yulang.GeneralDictionaryBodyProvenance227

/-! Every registered actual center is retained by the semantic trace footprint.
This supplies a prior support fact, rather than assuming body-origin freshness. -/
namespace Yulang.GeneralDictionaryFootprintCenters227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralDictionaryOriginJournal227 (installDelta)
open GeneralNominalCenteredFrame179 (siteSources)
variable {roles : Roles.RoleDecls}

theorem site_center (site : Site roles) (index : Fin (roles site.occurrence.demand.role).arity) :
    site.center index ∈ siteSources site := by
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩

theorem emitted_center (plan : Plan roles) (site : Site roles) (emitted : site ∈ plan.emitted)
    (index : Fin (roles site.occurrence.demand.role).arity) :
    site.center index ∈ GeneralDictionaryReachableRest227.packetSources plan := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
  have child : (plan.childSite clause.val (plan.packet.checked.signature.2.2.2 clause.val clause.property)).center index ∈
      GeneralDictionaryDefaultPacketSupport213.childSources plan := by
    apply List.mem_flatMap.mpr
    exact ⟨clause,by simp,List.mem_append_left _ (site_center _ index)⟩
  simp [GeneralDictionaryReachableRest227.packetSources,GeneralDictionaryReachableRest227.restSources,child]

theorem centers (trace : Footprint registry context root state pool) :
    ∀ site ∈ state.core.sites, ∀ index, site.center index ∈ pool := by
  induction trace with
  | initial =>
      intro site member index
      cases List.mem_singleton.mp member
      exact List.mem_append_right _ (site_center _ index)
  | @tail before after pool delta trace event ih =>
      cases event with
      | administrative generated action =>
          cases action <;> intro site member index <;> exact List.mem_append_left [] (ih site member index)
      | refresh =>
          intro site member index
          exact List.mem_append_left [] (ih site member index)
      | install effect generated enabled novel =>
          intro site member index
          rcases List.mem_append.mp member with old | fresh
          · exact List.mem_append_left _ (ih site old index)
          · apply List.mem_append_right
            have present := emitted_center effect.plan site fresh index
            simp [installDelta,present]
      | merge first last generated one two same novel =>
          intro site member index
          exact List.mem_append_left _ (ih site member index)

/-- A registered plan's input roots cannot be newly introduced by a later
class-body read, even when a binder itself is a reused aggregate source. -/
theorem registered_input_centers (trace : Footprint registry context root state pool)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) :
    List.ofFn plan.input.center ⊆ pool := by
  intro name member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact centers trace plan.input
    (GeneralDictionaryDefault214ActualSupport.registered_input trace.path plan registered) index

/-- A prospective current frame also reads an already registered input site. -/
theorem frame_input_centers (trace : Footprint registry context root state pool)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    List.ofFn plan.input.center ⊆ pool := by
  intro name member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact centers trace plan.input frame.center_recorded index
end Yulang.GeneralDictionaryFootprintCenters227
