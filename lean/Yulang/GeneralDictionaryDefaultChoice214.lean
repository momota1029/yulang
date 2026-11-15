import Yulang.GeneralDictionaryDefaultAvailability208
import Yulang.GeneralDictionaryDefaultTrace208

set_option backward.isDefEq.respectTransparency false

/-! Exact head-only replay interface for the remaining choice guard. No total
packet/effect model, point interval, or historical center equality is required.
Current head readiness itself remains an obligation; it is not inferred here. -/
namespace Yulang.GeneralDictionaryDefaultChoice214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

theorem visible_packets
    (path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step reg root)
      (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.declaration ∈ reg.declarations := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact enabled.registry_eq ▸ effect.frame.visible
      · exact ih packet member

theorem reachable_visible
    (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.declaration ∈ (registry value).declarations := by
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  exact visible_packets path

/-- For a visible declaration under current head uniqueness, having the same
selected key is exactly current role agreement and Prepared head readiness. -/
theorem prepared_iff_key (agree : reg.roles = roles) (checked : Checked reg)
    (focus : Occurrence roles)
    (unique : Unique reg context focus key children)
    (visible : declaration ∈ reg.declarations) :
    (declaration.role = focus.demand.role ∧ Prepared reg context focus declaration) ↔
      declaration.id = key := by
  constructor
  · rintro ⟨role,prepared⟩
    obtain ⟨metadata,linked,fresh,bounds,located,finished,model,head⟩ := prepared
    let checkedDecl : DeclarationChecked reg.constructors roles declaration := agree ▸ checked.2 declaration visible
    let kids := GeneralNominalAllocation.children context.state reg (inputs focus) declaration checkedDecl
      (GeneralNominalRecursiveInspection.bindings context.state
        (GeneralNominalRecursiveCandidates.report context declaration bounds))
    have survivor : Survivor reg context focus declaration.id kids :=
      ⟨unique.1.1,declaration,visible,checkedDecl,rfl,role,bounds,located,
        ⟨metadata,linked,fresh,bounds,located,finished,model,head⟩,rfl⟩
    exact (unique.2 _ _ survivor).1
  · intro keyEq
    obtain ⟨known,chosen,present,certified,chosenKey,role,bounds,located,prepared,emitted⟩ := unique.1
    have same := GeneralDictionaryEmissionPlans.declaration_key_unique reg checked
      declaration chosen visible present (keyEq.trans chosenKey.symm)
    subst declaration
    exact ⟨role,prepared⟩

/-- This iff isolates (A) using only head reinspection of historical class
members. It does not use the stronger packet/effect joint-model conclusion. -/
theorem choice_iff_heads
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∀ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current
        packet.site.occurrence.identity prior.site.occurrence.identity →
      prior.declaration.role = packet.site.occurrence.demand.role ∧
      Prepared (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  have prior := GeneralDictionaryDefaultAvailability208.selected_prior selected
  cases prior with
  | selected safe unique clear =>
    constructor
    · intro compatible historical member alias
      exact (prepared_iff_key (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).1
        (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 _ unique (reachable_visible reachable historical member)).mpr (compatible historical member alias).symm
    · intro heads historical member alias
      exact ((prepared_iff_key (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).1
        (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 _ unique (reachable_visible reachable historical member)).mp (heads historical member alias)).symm
end Yulang.GeneralDictionaryDefaultChoice214

namespace Yulang.GeneralDictionaryDefaultChoice214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

theorem packet_sites
    (path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step reg root)
      (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets,
      packet.site ∈ state.core.erased.current.sites ∧
      packet.declaration.role = packet.site.occurrence.demand.role := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action =>
      cases action with
      | refresh | reobserve | equate => exact ih
      | enqueue linked absent =>
        intro packet member
        exact ⟨List.mem_append_left _ (ih packet member).1,(ih packet member).2⟩
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨List.mem_append_left _ (enabled.snapshot_eq ▸ effect.frame.raw_recorded),effect.frame.role_eq⟩
      · exact ⟨List.mem_append_left _ (ih packet member).1,(ih packet member).2⟩

/-- Historical alias-class declarations have the current role, even after
arbitrary corrected refresh, reobservation and merge steps. -/
theorem historical_role
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (member : prior ∈ state.core.erased.current.packets)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      focus.identity prior.site.occurrence.identity) :
    prior.declaration.role = focus.demand.role := by
  obtain ⟨plan,frame,kids⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable selected
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  have compiled := (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
  have inv := GeneralNominalCenteredHeadMatStepHistory.roles_invariant compiled
    (GeneralDictionaryDefaultTrace208.built_trace path)
  have old := packet_sites path prior member
  have currentOrigin := frame.occurrence_eq ▸ inv.raw plan.packet.site frame.raw_recorded
  have colors := GeneralNominalCenteredHeadMatStepRoles.alias_color inv alias
  rw [GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled currentOrigin,
    GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled (inv.raw _ old.1)] at colors
  exact old.2.trans colors.symm

/-- Exact (A) reduction on the full selected/reachable domain: only current
head preparedness of historical class declarations remains to be transported.
The role side condition is derived from the actual trace, not postulated. -/
theorem choice_iff_prepared
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∀ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current
        packet.site.occurrence.identity prior.site.occurrence.identity →
      Prepared (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  rw [choice_iff_heads checked reachable selected]
  constructor
  · intro heads prior member alias
    exact (heads prior member alias).2
  · intro heads prior member alias
    exact ⟨historical_role checked reachable selected member alias,heads prior member alias⟩
end Yulang.GeneralDictionaryDefaultChoice214
