import Yulang.GeneralDictionaryFootprintCenters227

namespace Yulang.GeneralDictionarySiteFootprint228
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralDictionaryOriginJournal227 (installDelta)
open GeneralNominalCenteredFrame179 (siteSources)
variable {roles : Roles.RoleDecls}

/-- The entire registered site, not just actual centers, was included when
its parent installed. Raw refreshes cannot erase that retained contribution. -/
theorem emitted_sources (plan : Plan roles) (site : Site roles)
    (emitted : site ∈ plan.emitted) :
    siteSources site ⊆ GeneralDictionaryReachableRest227.packetSources plan := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
  intro name present
  have child : name ∈ GeneralDictionaryDefaultPacketSupport213.childSources plan := by
    apply List.mem_flatMap.mpr
    exact ⟨clause,by simp,List.mem_append_left _ present⟩
  simp [GeneralDictionaryReachableRest227.packetSources,GeneralDictionaryReachableRest227.restSources,child]

theorem registered_sources (trace : Footprint registry context root state pool) :
    ∀ site ∈ state.core.sites, siteSources site ⊆ pool := by
  induction trace with
  | initial =>
      intro site member name present
      cases List.mem_singleton.mp member
      exact List.mem_append_right _ present
  | @tail before after pool delta trace event ih =>
      cases event with
      | administrative generated action =>
          cases action <;> intro site member name present <;> exact List.mem_append_left [] (ih site member present)
      | refresh =>
          intro site member name present
          exact List.mem_append_left [] (ih site member present)
      | install effect generated enabled novel =>
          intro site member name present
          rcases List.mem_append.mp member with old | fresh
          · exact List.mem_append_left _ (ih site old present)
          · apply List.mem_append_right
            have packet := emitted_sources effect.plan site fresh present
            simp [installDelta,packet]
      | merge first last generated one two same novel =>
          intro site member name present
          exact List.mem_append_left _ (ih site member present)

theorem frame_sources (trace : Footprint registry context root state pool)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    siteSources plan.input ⊆ pool := registered_sources trace plan.input frame.center_recorded

end Yulang.GeneralDictionarySiteFootprint228
