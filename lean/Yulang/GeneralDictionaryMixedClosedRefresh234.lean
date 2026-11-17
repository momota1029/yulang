import Yulang.GeneralDictionaryMixedClosedSnapshot234
import Yulang.GeneralDictionaryMixedClosedTrust234
set_option backward.isDefEq.respectTransparency false
/-! A concrete mixed-trusted refresh certificate making all three width-record
aggregates known in an eight-slot context. This is auxiliary certificate availability, not a Kernel232 Step.
The existing legacy-cache Stable theorem is not changed or contradicted. -/
namespace Yulang.GeneralDictionaryMixedClosedRefresh234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryMixedClosedBase234 GeneralDictionaryMixedClosedSnapshot234
open GeneralNominalVersionedSupport233 GeneralNominalVersionedMixedObservations233
open GeneralDictionaryMixedClosedTrust234
open GeneralSourceState (equationAtoms)

noncomputable def certificate : GeneralNominalVersionedMixedObservations233.Refresh installed extendedContext where
  refines := refines
  interpretation := rfl
  support := by
    intro identity member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append,source,old,ite_false] using supported slot
    · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
      by_cases old : slot.val < 5
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,by change slot.val = source slot; simp [source,old]⟩)))
      · simpa only [GeneralNominalState.sources,List.mem_append,source,old,ite_false] using supported slot
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary
  constraints := by
    intro m valid
    have upper (slot : Fin 8) (high : 5 ≤ slot.val) :
        CommonNominalFullCarrier.Equivalent (m (source slot)).1 .emptyRecord := by
      obtain ⟨facts,trusted,sound⟩ := justified slot high
      exact sound m (trusted_models trusted valid)
    have transport := assignment_transport m
    refine ⟨⟨?_,?_,?_⟩,valid.1.1.2.2⟩
    · apply (PresenceNormalForm.all_append ..).mpr
      constructor
      · rw [PresenceNormalForm.all_rename,transport]
        exact valid.1.1.1.1
      · apply (PresenceNormalForm.all_append ..).mpr
        refine ⟨(PresenceNormalForm.all_append ..).mpr ⟨?_,?_⟩,?_⟩
        · intro atom member
          simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact (upper 5 (by decide)).1
          · exact (upper 5 (by decide)).2
        · intro atom member
          simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact (upper 6 (by decide)).1
          · exact (upper 6 (by decide)).2
        · intro atom member
          simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact (upper 7 (by decide)).1
          · exact (upper 7 (by decide)).2
    · intro slot term found
      change Fin 8 at slot
      change (heads slot).equation = some term at found
      by_cases two : slot = 2
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact valid.1.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases five : 5 ≤ slot.val
        · have same : term = .emptyRecord := by
            simpa [heads,shapes,two,five,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using found.symm
          subst term
          exact upper slot five
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
        refine ⟨[],[],.source,.source,?_⟩
        intro m _ valid
        exact valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases five : 5 ≤ slot.val
        · have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 0 Fin.elim0 =
              .structural kind children := by simpa [viewHeads,two,five] using found
          cases same
          obtain ⟨facts,trusted,sound⟩ := justified slot five
          exact ⟨[],facts,.source,trusted,fun m _ valid => sound m valid⟩
        · simp [viewHeads,two,five] at found
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

theorem model_preserved (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedJournal232.Models
      (GeneralNominalVersionedRefresh232.refresh installed extendedContext) model ↔
      GeneralNominalVersionedJournal232.Models installed model :=
  GeneralNominalVersionedMixedObservations233.refresh_models certificate

end Yulang.GeneralDictionaryMixedClosedRefresh234
