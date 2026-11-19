import Yulang.GeneralRebaseCandidatePlan267

namespace Yulang.GeneralRebaseEnumeratePlans267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseCandidatePlan267 (DeclChecked Shell build build_sound build_recreates)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralNominalVersionedCandidates231 (Prepared)

/-- Enumerate the complete Plan data, not just declaration IDs. Computation
uses the actual raw/center journals and computes bounds via arguments. -/
def plans (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) : List (Plan roles) :=
 (discover state.core.erased.current root).flatMap fun focus =>
   registry.declarations.attach.flatMap fun declaration =>
     state.core.erased.current.sites.flatMap fun raw =>
       state.core.sites.filterMap fun center => build registry state checked focus declaration raw center

theorem plans_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (plan : Plan roles) :
 plan ∈ plans registry state root checked ↔ Shell registry state root plan := by
 constructor
 · intro h
   obtain ⟨focus,seen,h⟩ := List.mem_flatMap.mp h
   obtain ⟨decl,_,h⟩ := List.mem_flatMap.mp h
   obtain ⟨raw,inRaw,h⟩ := List.mem_flatMap.mp h
   obtain ⟨center,inCenter,built⟩ := List.mem_filterMap.mp h
   exact build_sound registry state checked focus decl raw center plan built
     ((discover_exact ..).mp seen) inRaw inCenter
 · intro shell
   apply List.mem_flatMap.mpr
   refine ⟨plan.packet.site.occurrence,(discover_exact ..).mpr shell.generated,?_⟩
   apply List.mem_flatMap.mpr
   refine ⟨⟨plan.packet.declaration,shell.visible⟩,List.mem_attach _ _,?_⟩
   apply List.mem_flatMap.mpr
   exact ⟨plan.packet.site,shell.raw,List.mem_filterMap.mpr
     ⟨plan.input,shell.center,build_recreates registry state checked plan shell⟩⟩

theorem frame_of_member (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (plan : Plan roles)
 (member : plan ∈ plans registry state root checked)
 (prepared : Prepared registry state.core.erased.current.context plan.packet.site.occurrence plan.packet.declaration) :
 GeneralNominalVersionedEvidence231.Frame registry state.core plan.packet.site.occurrence plan.packet.declaration.id plan := by
 have shell := (plans_exact ..).mp member
 exact ⟨shell.registry_eq,shell.context_eq,rfl,rfl,shell.raw,shell.center,shell.visible,shell.role_eq,shell.located,prepared⟩

theorem includes_frame (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (plan : Plan roles)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
   plan.packet.site.occurrence plan.packet.declaration.id plan) :
 plan ∈ plans registry state root checked :=
 (plans_exact ..).mpr ⟨frame.registry_eq,frame.context_eq,generated,frame.raw_recorded,
   frame.center_recorded,frame.visible,frame.role_eq,frame.located⟩

theorem includes_install (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (effect : Effect roles)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (guard : GeneralNominalVersionedMixedKernel234.Installable registry state effect) :
 effect.plan ∈ plans registry state root checked := by
 apply includes_frame registry state root checked effect.plan generated
 rw [←guard.registry_eq,←guard.snapshot_eq]
 exact effect.frame

end Yulang.GeneralRebaseEnumeratePlans267
