import Yulang.GeneralDictionaryUpper230Snapshot
import Yulang.GeneralDictionaryOptionalOpenRefresh229
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Refresh
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryOptionalStage229
open GeneralDictionaryUpper230Base GeneralDictionaryUpper230Snapshot
open GeneralNominalCenteredHeadMatStepSupport GeneralNominalCenteredHeadMatStepObservations
open GeneralSourceState (equationAtoms)

noncomputable def certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh stage extendedContext where
  refines := refines
  interpretation := rfl
  support := by
    intro identity member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append,source,old,ite_false] using GeneralDictionaryOptionalOpenRefresh229.upper_supported
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append,source,old,ite_false] using GeneralDictionaryOptionalOpenRefresh229.upper_supported
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary
  constraints := by
    intro m valid
    have upper := justifies_sound GeneralDictionaryOptionalOpenRefresh229.upper_justified valid
    have transport := assignment_transport m
    refine ⟨⟨?_,?_,?_⟩,valid.1.2.2⟩
    · apply (PresenceNormalForm.all_append ..).mpr
      constructor
      · rw [PresenceNormalForm.all_rename,transport]
        exact valid.1.1.1
      · intro atom member
        simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact upper.1
        · exact upper.2
    · intro slot term found
      change Fin 6 at slot
      change (heads slot).equation = some term at found
      by_cases two : slot = 2
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases five : slot = 5
        · subst slot
          have same : term = .emptyRecord := Option.some.inj found.symm
          subst term
          exact upper
        · simp [heads,two,five,GeneralSourceState.Head.equation] at found
    · intro pair member; cases member
  cache := by
    intro observation recorded
    cases recorded with
    | scalar slot scalar found =>
      simp only [extendedSnapshot,extendedView,viewHeads] at found
      split at found <;> cases found
    | structural slot kind children found =>
      change (viewHeads slot) = .structural kind children at found
      by_cases two : slot = 2
      · subst slot
        have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 0 Fin.elim0 =
            .structural kind children := by simpa [viewHeads] using found
        cases same
        refine ⟨[],.source,?_⟩
        intro m valid
        exact valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases five : slot = 5
        · subst slot
          have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 0 Fin.elim0 =
              .structural kind children := by simpa [viewHeads] using found
          cases same
          exact GeneralDictionaryOptionalOpenRefresh229.upper_justified
        · simp [viewHeads,two,five] at found
    | nominal slot d found =>
      refine ⟨[],.source,?_⟩
      intro m valid
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

end Yulang.GeneralDictionaryUpper230Refresh
