import Yulang.GeneralDictionaryCompoundSnapshot239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundRefresh239
open GeneralDictionaryJournalRefinement228Source GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundBase239 GeneralDictionaryCompoundSnapshot239
open GeneralNominalVersionedSupport233 GeneralNominalVersionedMixedObservations233
open GeneralSourceState (equationAtoms)

theorem supported (slot : Fin 7) (high : 5 ≤ slot.val) : source slot ∈ GeneralNominalState.sources point.core.erased.current.context.state := by
  have size := slot.isLt
  have casesSlot : slot = 5 ∨ slot = 6 := by omega
  rcases casesSlot with rfl | rfl <;> decide +kernel

noncomputable def certificate : Refresh point extendedContext where
  refines := refines
  interpretation := rfl
  support := by
    intro identity member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append] using supported slot (by omega)
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append] using supported slot (by omega)
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary
  constraints := by
    intro m valid
    have facts := trusted_models GeneralDictionaryCompoundTrust239.trusted valid
    have low := GeneralDictionaryCompoundTrust239.lower m facts
    have high := GeneralDictionaryCompoundTrust239.upper m facts
    have transport := assignment_transport m
    refine ⟨⟨?_,?_,?_⟩,valid.1.1.2.2⟩
    · apply (PresenceNormalForm.all_append ..).mpr
      constructor
      · rw [PresenceNormalForm.all_rename,transport]
        exact valid.1.1.1.1
      · apply (PresenceNormalForm.all_append ..).mpr
        constructor
        · intro atom member
          simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact low.1
          · exact low.2
        · intro atom member
          simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact high.1
          · exact high.2
    · intro slot term found
      change Fin 7 at slot
      change (heads slot).equation = some term at found
      by_cases two : slot = 2
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact valid.1.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases five : slot = 5
        · subst slot
          have same : term = .variant 0 (.var 4) := Option.some.inj found.symm
          subst term
          exact low
        · by_cases six : slot = 6
          · subst slot
            have same : term = .variant 0 (.var 2) := Option.some.inj found.symm
            subst term
            exact high
          · simp [heads,two,five,six,GeneralSourceState.Head.equation] at found
    · intro pair member; cases member
  cache := by
    intro observation recorded
    cases recorded with
    | scalar slot scalar found =>
      change (viewHeads slot) = .scalar scalar at found
      unfold viewHeads at found
      split at found <;> (try split at found) <;> (try split at found) <;> cases found
    | structural slot kind children found =>
      change (viewHeads slot) = .structural kind children at found
      by_cases two : slot = 2
      · subst slot
        have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 0 Fin.elim0 = .structural kind children := found
        cases same
        exact ⟨[],[],.source,.source,fun m old _ => old.1.1.2.1 (2 : Fin 5) .emptyRecord rfl⟩
      · by_cases five : slot = 5
        · subst slot
          have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 1 (fun _ => (4 : Fin 7)) = .structural kind children := found
          cases same
          exact ⟨[],[.input GeneralDictionaryCompoundObstruction238.oldPlan],.source,
            GeneralDictionaryCompoundTrust239.trusted,fun m _ facts => GeneralDictionaryCompoundTrust239.lower m facts⟩
        · by_cases six : slot = 6
          · subst slot
            have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 1 (fun _ => (2 : Fin 7)) = .structural kind children := found
            cases same
            exact ⟨[],[.input GeneralDictionaryCompoundObstruction238.oldPlan],.source,
              GeneralDictionaryCompoundTrust239.trusted,fun m _ facts => GeneralDictionaryCompoundTrust239.upper m facts⟩
          · simp [viewHeads,two,five,six] at found
    | nominal slot d found =>
      refine ⟨[],[],.source,.source,?_⟩
      intro m _ valid
      have point := (point_models_iff m).mpr valid.1
      change (if slot = 0 ∨ slot = 1 then some pointDesc else none) = some d at found
      split at found
      · rename_i either
        cases Option.some.inj found
        have move (values) (fits : GeneralNominalState.FitsAll base m exactCopy.arguments values) :
            GeneralNominalState.FitsAll extendedBase m pointDesc.arguments values := by
          change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] values at fits
          have moveOne (a) (fit : GeneralNominalState.Fits base m (.type (2,2)) a) :
              GeneralNominalState.Fits extendedBase m
                (GeneralNominalRefinements.renameParameter embed (.type (2,2))) a := by
            cases a with
            | inl ty =>
              change CommonNominalFullCarrier.Subtype (m 2).1 ty ∧ CommonNominalFullCarrier.Subtype ty (m 2).1 at fit ⊢
              exact fit
            | inr => cases fit
          cases fits with
          | cons first tail => cases tail with
            | cons second tail => cases tail; exact .cons (moveOne _ first) (.cons (moveOne _ second) .nil)
        rcases either with rfl | rfl
        · obtain ⟨values,fits,equal⟩ := point.2.1 (0 : Fin 5) exactCopy rfl
          exact ⟨values,move values fits,equal⟩
        · obtain ⟨values,fits,equal⟩ := point.2.1 (1 : Fin 5) exactCopy rfl
          exact ⟨values,move values fits,equal⟩
      · cases found

noncomputable def refreshed := GeneralNominalVersionedRefresh232.refresh point extendedContext

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedJournal232.Models refreshed model ↔ GeneralNominalVersionedJournal232.Models point model :=
  GeneralNominalVersionedMixedObservations233.refresh_models certificate

end Yulang.GeneralDictionaryCompoundRefresh239
