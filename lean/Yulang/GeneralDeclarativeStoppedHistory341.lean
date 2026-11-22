import Yulang.GeneralDeclarativeStoppedRetarget341
import Yulang.GeneralStoppedInstallHistory335
import Yulang.GeneralDictionaryRefinedLocations

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedHistory341
open GeneralDeclarations (Registry)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_iff)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralDeclarativeStoppedRetarget341 (fit_unique_role)
open GeneralStoppedInstallHistory335 (installed_origin)

section
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
variable {root : GeneralSourceDictionaries.Occurrence roles} {saved : Effect roles}
/-- Extract literal raw and centered site retention from a genuine
source-reachable install, not from equality of their interpreted types. -/
theorem retained_current_sites
    (path : B4TargetV8.Reachable (boundary roles) r root s) (member : saved ∈ s.effects) :
    saved.plan.packet.registry = registry r ∧
    saved.plan.packet.site ∈ s.core.erased.current.sites ∧ saved.plan.input ∈ s.core.sites := by
  obtain ⟨initial,⟨legacy,_,equal⟩,all⟩ := path
  subst initial
  obtain ⟨before,_,live,available,novel,later⟩ := installed_origin all rfl member
  have initialFrame := saved.frame
  have added : GeneralNominalVersionedMixedKernel234.Step (registry r) root before
      (GeneralNominalVersionedInstall232.install before saved) := ⟨_,live,.install saved available novel⟩
  have full := GeneralNominalVersionedMixedGrowth234.trans
    (GeneralNominalVersionedMixedGrowth234.step added) (GeneralNominalVersionedMixedGrowth234.steps later)
  rw [available.registry_eq,available.snapshot_eq] at initialFrame
  exact ⟨initialFrame.registry_eq, full.legacy.rawSites initialFrame.raw_recorded,full.legacy.sites initialFrame.center_recorded⟩

theorem initial_frame
    (path : B4TargetV8.Reachable (boundary roles) r root s) (member : saved ∈ s.effects) :
    saved.plan.packet.declaration ∈ (registry r).declarations ∧
      saved.plan.packet.declaration.role = saved.plan.packet.site.occurrence.demand.role := by
  have reg : saved.registry = registry r := saved.frame.registry_eq.symm.trans (retained_current_sites path member).1
  exact ⟨reg ▸ saved.frame.visible,saved.frame.role_eq⟩

/-- Rebuild current Frame from real historical coordinates, exact lookup
transport, and fresh reinspection of the declaration in the current
context. The historical packet itself is not a current certificate. -/
theorem retarget_frame
    (path : B4TargetV8.Reachable (boundary roles) r root s) (member : saved ∈ s.effects)
    (ref : Refines saved.plan.packet.context.state s.core.erased.current.context.state)
    (prepared : Prepared (registry r) s.core.erased.current.context
      saved.plan.packet.site.occurrence saved.plan.packet.declaration) :
    Frame (registry r) s.core saved.plan.packet.site.occurrence saved.plan.packet.declaration.id
      (retarget saved.plan ref) := by
  obtain ⟨oldReg,raw,center⟩ := retained_current_sites path member
  obtain ⟨visible,role⟩ := initial_frame path member
  refine ⟨oldReg,rfl,rfl,rfl,raw,center,visible,role,?_,prepared⟩
  exact GeneralDictionaryRefinedLocations.arguments _ _ ref _ _ saved.frame.located

abbrev Focus (saved : Effect roles) := saved.plan.packet.site.occurrence

/-- The one-key-per-role branch now constructs the actual current frame
and its feasible packet from real journal history; it does not demand
that the caller bring a current frame or packet as an assumption. -/
theorem derive_current
    (checked : (boundary roles).Checked r)
    (path : B4TargetV8.Reachable (boundary roles) r root s)
    (member : saved ∈ s.effects)
    (ref : Refines saved.plan.packet.context.state s.core.erased.current.context.state)
    (interp : s.core.erased.current.context.interpretation = saved.plan.packet.context.interpretation)
    (observed : Observed saved.plan)
    (picked : Local r s (Focus saved) (.selected key kids))
    (single : ∀ a ∈ (registry r).declarations, ∀ b ∈ (registry r).declarations, a.role = b.role → a.id = b.id)
    (m : GeneralNominalCommonBridge.Assignment) (valid : Models s m) :
    ∃ plan, Frame (registry r) s.core (Focus saved) key plan ∧ FitFrame (s := s) (Focus saved) plan := by
  obtain ⟨visible,role⟩ := initial_frame path member
  have chosen := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique (local_iff.mp picked)
  have keyEq : saved.plan.packet.declaration.id = key := by
    obtain ⟨_,d,seen,_,oldKey,tied,_,_,_,_⟩ := chosen.1
    exact (single _ visible _ seen (role.trans tied.symm)).trans oldKey
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have prepared := ((GeneralNominalVersionedMixedChoice236.prepared_iff_key compiled.1 compiled.2 _ chosen visible).mpr keyEq).2
  have frame := retarget_frame path member ref prepared
  have now := fit_unique_role saved.plan ref interp observed checked path member rfl (keyEq ▸ frame) picked single m valid
  exact ⟨retarget saved.plan ref,keyEq ▸ frame,now⟩

end
end Yulang.GeneralDeclarativeStoppedHistory341
