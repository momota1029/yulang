import Yulang.GeneralDictionaryDefaultChoice214

/-! Selection excludes unfinished alternatives, not just alternative survivors.
Thus the remaining historical choice obstruction is precisely current Failed;
no impossibility of that failure is assumed or claimed. -/
namespace Yulang.GeneralDictionaryDefaultChoiceObstruction215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls}

theorem prepared_not_failed (ready : Prepared reg context (focus : Occurrence roles) declaration) :
    ¬ Failed reg context focus declaration := by
  rintro ⟨_,_,bounds,located,blocked,arity,conflict⟩
  obtain ⟨_,_,_,other,found,finished,model,held⟩ := ready
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
  have prior := GeneralDictionaryDefaultAvailability208.selected_prior selected
  cases prior with
  | selected safe unique clear =>
      by_cases ready : Prepared (registry value) state.core.erased.current.context focus declaration
      · exact Or.inl ready
      · apply Or.inr
        apply Classical.byContradiction
        intro failed
        exact safe.2.2.2 (Or.inl ⟨safe.1,declaration,visible,role,failed,ready⟩)

theorem historical_prepared_or_failed
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (member : prior ∈ state.core.erased.current.packets)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      focus.identity prior.site.occurrence.identity) :
    Prepared (registry value) state.core.erased.current.context focus prior.declaration ∨
      Failed (registry value) state.core.erased.current.context focus prior.declaration :=
  selected_prepared_or_failed selected
    (GeneralDictionaryDefaultChoice214.reachable_visible reachable prior member)
    (GeneralDictionaryDefaultChoice214.historical_role checked reachable selected member alias)

theorem choice_iff_no_failed
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state packet.site.occurrence (.selected packet.declaration.id children)) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current packet ↔
    ∀ prior ∈ state.core.erased.current.packets,
      GeneralNominalSaturationState.Alias state.core.erased.current
        packet.site.occurrence.identity prior.site.occurrence.identity →
      ¬ Failed (registry value) state.core.erased.current.context packet.site.occurrence prior.declaration := by
  rw [GeneralDictionaryDefaultChoice214.choice_iff_prepared checked reachable selected]
  constructor
  · intro heads prior member alias
    exact prepared_not_failed (heads prior member alias)
  · intro clear prior member alias
    exact (historical_prepared_or_failed checked reachable selected member alias).resolve_right
      (clear prior member alias)
end Yulang.GeneralDictionaryDefaultChoiceObstruction215
