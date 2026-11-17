import Yulang.GeneralNominalVersionedMixedChoiceHistory236
set_option backward.isDefEq.respectTransparency false
/-! Exact remaining historical-choice obligation on the full selected/source
reachable mixed domain. Versioned Prepared/Failed are current reinspection,
not historical snapshot validity. The equivalences do not prove their right
sides universally and therefore are not the missing general Choice bridge. -/
namespace Yulang.GeneralNominalVersionedMixedChoice236
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedCandidates231 GeneralNominalVersionedJournal232
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
variable {roles : Roles.RoleDecls}
variable {children : List (Occurrence roles)}

theorem prepared_iff_key (agree : reg.roles = roles) (checked : Checked reg)
    (focus : Occurrence roles) (unique : Unique reg context focus key children)
    (visible : declaration ∈ reg.declarations) :
    (declaration.role = focus.demand.role ∧ Prepared reg context focus declaration) ↔ declaration.id = key := by
  constructor
  · rintro ⟨role,prepared⟩
    obtain ⟨metadata,linked,bounds,located,fresh,finished,model,head⟩ := prepared
    let check : DeclarationChecked reg.constructors roles declaration := agree ▸ checked.2 declaration visible
    let kids := GeneralNominalVersionedCandidates231.children reg context focus declaration check bounds
    have survivor : Survivor reg context focus declaration.id kids :=
      ⟨unique.1.1,declaration,visible,check,rfl,role,bounds,located,
        ⟨metadata,linked,bounds,located,fresh,finished,model,head⟩,rfl⟩
    exact (unique.2 _ _ survivor).1
  · intro keyEq
    obtain ⟨known,chosen,present,certified,chosenKey,role,bounds,located,prepared,emitted⟩ := unique.1
    have same := GeneralDictionaryEmissionPlans.declaration_key_unique reg checked
      declaration chosen visible present (keyEq.trans chosenKey.symm)
    subst declaration
    exact ⟨role,prepared⟩

theorem choice_iff_prepared
    (checked : (boundary roles).Checked value)
    (path : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∀ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      Prepared (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  constructor
  · intro compatible prior member alias
    exact ((prepared_iff_key compiled.1 compiled.2 _ unique
      (GeneralNominalVersionedMixedChoiceHistory236.visible path member)).mpr (compatible prior member alias).symm).2
  · intro heads prior member alias
    exact ((prepared_iff_key compiled.1 compiled.2 _ unique
      (GeneralNominalVersionedMixedChoiceHistory236.visible path member)).mp
      ⟨GeneralNominalVersionedMixedChoiceHistory236.historical_role checked path selected member alias,
        heads prior member alias⟩).symm

theorem prepared_not_failed (ready : Prepared reg context (focus : Occurrence roles) declaration) :
    ¬ Failed reg context focus declaration := by
  rintro ⟨_,bounds,located,_,blocked,arity,conflict⟩
  obtain ⟨_,_,other,found,_,finished,model,held⟩ := ready
  have equal : bounds = other := Option.some.inj (located.symm.trans found)
  subst other
  rcases conflict with conflicts | impossible
  · exact conflicts finished.2.1
  · exact impossible ⟨model,held⟩

theorem selected_prepared_or_failed
    (selected : Local value state focus (.selected key children))
    (visible : declaration ∈ (registry value).declarations)
    (role : declaration.role = focus.demand.role) :
    Prepared (registry value) state.core.erased.current.context focus declaration ∨
      Failed (registry value) state.core.erased.current.context focus declaration := by
  classical
  have safe := GeneralNominalVersionedMixedCurrentCandidate235.selected_safe
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)
  by_cases ready : Prepared (registry value) state.core.erased.current.context focus declaration
  · exact Or.inl ready
  · apply Or.inr
    apply Classical.byContradiction
    intro failed
    exact safe.2.2.2 (Or.inl ⟨safe.1,declaration,visible,role,failed,ready⟩)

theorem historical_prepared_or_failed
    (checked : (boundary roles).Checked value)
    (path : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (member : prior ∈ state.core.erased.current.packets)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current focus.identity prior.site.occurrence.identity) :
    Prepared (registry value) state.core.erased.current.context focus prior.declaration ∨
      Failed (registry value) state.core.erased.current.context focus prior.declaration :=
  selected_prepared_or_failed selected (GeneralNominalVersionedMixedChoiceHistory236.visible path member)
    (GeneralNominalVersionedMixedChoiceHistory236.historical_role checked path selected member alias)

theorem choice_iff_no_failed
    (checked : (boundary roles).Checked value)
    (path : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∀ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity →
      ¬ Failed (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  rw [choice_iff_prepared checked path selected]
  constructor
  · intro heads prior member alias
    exact prepared_not_failed (heads prior member alias)
  · intro clear prior member alias
    exact (historical_prepared_or_failed checked path selected member alias).resolve_right (clear prior member alias)

/-- Exact classification of failure of the desired choice guard. It requires a
real reachable selected current packet, not an arbitrary hand-built journal. -/
theorem incompatible_iff_failed
    (checked : (boundary roles).Checked value)
    (path : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    ¬ GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∃ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current packet.site.occurrence.identity prior.site.occurrence.identity ∧
      Failed (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  classical
  rw [choice_iff_no_failed checked path selected]
  simp only [Classical.not_forall,Classical.not_not,exists_prop]

/-- Genuine positive subclass, explicitly restricted to one key per role. -/
theorem choice_of_role_unique
    (checked : (boundary roles).Checked value)
    (path : B4TargetV8.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children))
    (visible : packet.declaration ∈ (registry value).declarations)
    (role : packet.declaration.role = packet.site.occurrence.demand.role)
    (uniqueRole : ∀ a ∈ (registry value).declarations, ∀ b ∈ (registry value).declarations, a.role = b.role → a.id = b.id) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet := by
  intro prior member alias
  exact uniqueRole packet.declaration visible prior.declaration
    (GeneralNominalVersionedMixedChoiceHistory236.visible path member)
    (role.trans (GeneralNominalVersionedMixedChoiceHistory236.historical_role checked path selected member alias).symm)
end Yulang.GeneralNominalVersionedMixedChoice236
