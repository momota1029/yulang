import Yulang.GeneralDictionaryJournalRefinement229Snapshot
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement229Refresh
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralDictionaryJournalRefinement229Snapshot
open GeneralNominalCenteredHeadMatStepSupport
open GeneralNominalCenteredHeadMatStepObservations
open CommonNominalFullCarrier

noncomputable def refines : GeneralNominalRefinements.Refines stage.core.erased.current.context.state refreshedSnapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨id,(by intro _; rfl),(by intro _; rfl),?_,?_,?_⟩
    · intro atom member
      exact List.mem_append_left _ ((GeneralNominalRefinements.refl stage.core.erased.current.context.state).base.ordinary atom member)
    · intro slot known
      change Fin 5 at slot
      change (base.heads slot).node ≠ _ at known
      by_cases two : slot = 2
      · subst slot; decide +kernel
      · exact False.elim (known (by simp [base,two,GeneralSourceState.Head.node]))
    · intro pair member; cases member
  · intro slot term recorded
    change Fin 5 at slot
    change (base.heads slot).equation = some term at recorded
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj recorded.symm
      subst term
      exact .head rfl
    · simp [base,two,GeneralSourceState.Head.equation] at recorded
  · intro slot d recorded
    exact (GeneralNominalRefinements.refl stage.core.erased.current.context.state).nominals slot d recorded
  · intro atom member; exact member
  · intro source known
    obtain ⟨slot,same,head | nominal⟩ := known
    · change Fin 5 at slot
      change (view.heads slot).node ≠ _ at head
      refine ⟨slot,same,Or.inl ?_⟩
      by_cases two : slot = 2
      · subst slot; decide +kernel
      · exact False.elim (head (by simp [two,GeneralNormalizedObservation.Head.node]))
    · exact ⟨slot,same,Or.inr nominal⟩
  · intro source member; exact member
  · intro key member; exact member

theorem trusted_output : Trusted stage [.output effect,.input plan] := by
  have input : Trusted stage [.input plan] :=
    .input plan .source (List.mem_cons_self ..) GeneralDictionaryJournalRefinement228Trusted.readback
  exact .output effect input (List.mem_cons_self ..) (List.mem_cons_self ..)
    (List.mem_singleton_self _) GeneralDictionaryJournalRefinement228Trusted.class_readback
    (by
      refine ⟨?_,?_⟩
      · exact List.mem_cons_self ..
      · intro child member
        change child ∈ packet.children at member
        rw [children_empty] at member
        cases member)

theorem output_justified : Justifies stage (fun m => Equivalent (m 4).1 .exactEmpty) := by
  refine ⟨[.output effect,.input plan],trusted_output,?_⟩
  intro m valid
  have output := (valid.2.2 (.output effect) (List.mem_cons_self ..)).1
  change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (GeneralNominalCenteredHeadMatEffects.variables plan m) m at output
  rw [emitted_schema] at output
  exact output ⟨4,.actual,.primitive .exactEmpty []⟩ (List.mem_singleton_self _)

noncomputable def certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh stage refreshedContext where
  refines := refines
  interpretation := rfl
  support := fun _ member => member
  constraints := by
    intro m valid
    have out := justifies_sound output_justified valid
    refine ⟨⟨?_,?_,?_⟩,valid.1.2.2⟩
    · apply (PresenceNormalForm.all_append ..).mpr
      refine ⟨valid.1.1.1,?_⟩
      intro atom member
      simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact out.1
      · exact out.2
    · intro slot term found
      change Fin 5 at slot
      change (heads slot).equation = some term at found
      by_cases two : slot = 2
      · subst slot
        have equal : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases four : slot = 4
        · subst slot
          have equal : term = .exactEmpty := Option.some.inj found.symm
          subst term
          exact out
        · simp [heads,two,four,GeneralSourceState.Head.equation] at found
    · intro pair member; cases member
  cache := by
    intro observation recorded
    cases recorded with
    | scalar slot scalar found =>
      by_cases two : slot = 2 <;> by_cases four : slot = 4 <;>
        simp [refreshedSnapshot,refreshedView,viewHeads,two,four] at found
    | structural slot kind children found =>
      by_cases two : slot = 2
      · subst slot
        have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 0 Fin.elim0 =
            .structural kind children := by simpa only [viewHeads,ite_true] using found
        cases same
        refine ⟨[],.source,?_⟩
        intro m valid
        exact valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
      · by_cases four : slot = 4
        · subst slot
          have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 1 Fin.elim0 =
              .structural kind children := by simpa [viewHeads] using found
          cases same
          exact output_justified
        · simp [refreshedSnapshot,refreshedView,viewHeads,two,four] at found
    | nominal slot descriptor found =>
      refine ⟨[],.source,?_⟩
      intro m valid
      have point := (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mpr valid.1
      obtain ⟨values,fits,equal⟩ := point.2.1 slot descriptor found
      have transport : ∀ parameters values, GeneralNominalState.FitsAll base m parameters values →
          GeneralNominalState.FitsAll refreshedBase m parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values one tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> exact one
      exact ⟨values,transport _ _ fits,equal⟩

noncomputable abbrev after := GeneralNominalCenteredHeadMatStepJournal.refresh stage refreshedContext

theorem unknown : ¬ GeneralNominalState.Known stage.core.erased.current.context.state 4 := by
  rintro ⟨slot,same,head | ⟨descriptor,found⟩⟩
  · have equal : slot = (4 : Fin 5) := Fin.ext same
    subst slot
    exact head rfl
  · have equal : slot = (4 : Fin 5) := Fin.ext same
    subst slot
    cases found

theorem known : GeneralNominalState.Known refreshedSnapshot 4 :=
  ⟨(4 : Fin 5),rfl,Or.inl (by decide +kernel)⟩

theorem step : GeneralDictionaryDefaultKernel208.Step registry root stage after := by
  refine ⟨root,.root,.refresh root refreshedContext certificate 4 ?_ unknown known⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_ofFn.mpr ⟨(4 : Fin 5),rfl⟩)))

theorem not_stable : ¬ GeneralDictionaryDefaultKernel208.Stable registry stage root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := step
  exact stable focus generated after action

end Yulang.GeneralDictionaryJournalRefinement229Refresh
