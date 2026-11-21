import Yulang.GeneralMixedCompoundPointView308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 17500000
namespace Yulang.GeneralMixedCompoundPointViewTrust308
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot width_two)
open GeneralDictionaryJournalRefinement228Reobserve (exactCopy)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundPointFirstPlan308 (plan pointFirst)
open GeneralMixedCompoundPointPorts308 (afterSnap ports current_pair)
open GeneralMixedCompoundPointViewBase308 (base viewHeads upper)
open GeneralMixedCompoundPointView308 (snap context refines support seen_lo previously_unknown)
open GeneralMixedCompoundUpperSnapshot307 (desc)
open GeneralMixedCompoundPointFeedback308 (port_sources)
open GeneralNominalVersionedMixedObservations233 (CacheSound Refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedSupport233
open GeneralNominalVersionedPlans231 (Inputs)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedFrame231 (capture)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralRebaseCompoundOwnerCapture273 (low high read_pair)

theorem retained : plan ∈ pointFirst.plans := List.mem_singleton_self _

theorem trusted : Trusted pointFirst [.input plan] := by
  refine .input plan .source retained ?_
  intro slot visited test observation head m valid
  have old := (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mpr valid.1
  exact GeneralCanonicalObservations.recorded_sound plan.packet.context.state m
    ⟨old.1,old.2.1,fun _ absent => nomatch absent⟩ (GeneralNominalSupport.head_recorded head)

theorem slice_input (m : Assignment) (h : SliceModels pointFirst [.input plan] m) :
    Inputs plan m := h.2.2 _ (List.mem_singleton_self _)

theorem aggregate (m : Assignment) (input : Inputs plan m) (old : GeneralNominalState.Models snapshot m) :
    Equivalent (m upper).1 .emptyRecord := by
  have paireq := (read_pair m _ _ _ _ (current_pair m input)).2
  have aligned := GeneralDictionaryCompoundPointHead238.capture_exact [] [] []
  have capture_h : high plan = upper := congrArg Prod.snd aligned
  rw [capture_h] at paireq
  exact equivalent_trans paireq (width_two m old)

theorem assign (m : Assignment) :
    GeneralNominalCommonBridge.assignment base m ∘ GeneralMixedCompoundBatchBase307.embed =
      GeneralNominalCommonBridge.assignment afterSnap.base m :=
  GeneralNominalRefinements.assignment_transport refines m

theorem constraints (m : Assignment) (h : Models pointFirst m) :
    GeneralNominalCenteredHeadMatStepRefresh.Constraints snap m := by
  have facts := trusted_models trusted h
  have input := slice_input m facts
  have ends := ports m input
  have agg := aggregate m input facts.1
  let a := GeneralNominalCommonBridge.assignment base m
  have laws (i : Fin 8) (term : Core.PresenceGeneration.TyTerm (Fin 8))
      (yes : Equivalent (a i).1 (term.eval CommonNominalFullCarrier.model a)) :
      PresenceNormalForm.All CommonNominalFullCarrier.model a (GeneralSourceState.equationAtoms i term) := by
    intro atom one
    simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at one
    rcases one with rfl|rfl
    · exact yes.1
    · exact yes.2
  refine ⟨⟨?_,?_,fun _ absent => nomatch absent⟩,h.1.1.2.2⟩
  · apply (PresenceNormalForm.all_append ..).mpr
    constructor
    · rw [PresenceNormalForm.all_rename]
      change PresenceNormalForm.All CommonNominalFullCarrier.model
        (GeneralNominalCommonBridge.assignment base m ∘ GeneralMixedCompoundBatchBase307.embed) _
      rw [assign]
      exact h.1.1.1.1
    · exact (PresenceNormalForm.all_append ..).mpr
        ⟨(PresenceNormalForm.all_append ..).mpr
          ⟨laws 5 (.variant 0 (.var 2)) ends.1,
           laws 6 (.variant 0 (.var 2)) ends.2⟩,
         laws 7 .emptyRecord agg⟩
  · intro i term found
    change Fin 8 at i
    change (GeneralMixedCompoundPointViewBase308.heads i).equation = some term at found
    by_cases two : i = 2
    · subst i
      have eq : term = .emptyRecord := Option.some.inj found.symm
      subst term; exact width_two m facts.1
    · by_cases seven : i = 7
      · subst i
        have eq : term = .emptyRecord := Option.some.inj found.symm
        subst term; exact agg
      · by_cases five : i = 5
        · subst i
          have eq : term = .variant 0 (.var 2) := Option.some.inj found.symm
          subst term; exact ends.1
        · by_cases six : i = 6
          · subst i
            have eq : term = .variant 0 (.var 2) := Option.some.inj found.symm
            subst term; exact ends.2
          · simp [GeneralMixedCompoundPointViewBase308.heads,two,seven,five,six,GeneralSourceState.Head.equation] at found

theorem nominal (m : Assignment) (old : GeneralNominalState.Models snapshot m) (slot : Fin 5)
    (whereAt : slot = 0 ∨ slot = 1) :
    ∃ args, GeneralNominalState.FitsAll base m desc.arguments args ∧
        Equivalent (m slot.val).1 (CommonNominalFullCarrier.nominal desc.constructor args) := by
  have observed := (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mpr old
  have h := observed.2.1 slot exactCopy (by simp [GeneralDictionaryJournalRefinement228Reobserve.pointSnapshot,whereAt])
  obtain ⟨args,fit,eq⟩ := h
  refine ⟨args,?_,eq⟩
  change GeneralNominalState.FitsAll GeneralDictionaryJournalRefinement228Source.base m
    [.type ((2 : Fin 5),2),.type (2,2)] args at fit
  change GeneralNominalState.FitsAll base m [.type ((2 : Fin 8),2),.type (2,2)] args
  have one (v) (h : GeneralNominalState.Fits GeneralDictionaryJournalRefinement228Source.base m
      (.type ((2 : Fin 5),2)) v) :
      GeneralNominalState.Fits base m (.type ((2 : Fin 8),2)) v := by
    cases v with
    | inl t => exact h
    | inr row => cases h
  cases fit with
  | cons x xs => cases xs with
    | cons y ys => cases ys; exact .cons (one _ x) (.cons (one _ y) .nil)

theorem cache : CacheSound pointFirst snap := by
  intro observation recorded
  cases recorded with
  | scalar slot n found =>
    change viewHeads slot = .scalar n at found
    simp [viewHeads] at found
    split at found <;> (try split at found) <;> (try split at found) <;> cases found
  | structural slot kind children found =>
    change viewHeads slot = .structural kind children at found
    by_cases empty : slot = 2 ∨ slot = 7
    · rcases empty with rfl|rfl
      · have eq : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            0 Fin.elim0 = .structural kind children := found
        cases eq
        exact ⟨[],[],.source,.source,fun m _ facts => width_two m facts.1⟩
      · have eq : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            0 Fin.elim0 = .structural kind children := found
        cases eq
        exact ⟨[],[.input plan],.source,trusted,fun m _ facts => aggregate m (slice_input m facts) facts.1⟩
    · by_cases five : slot = 5
      · subst slot
        have eq : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            1 (fun _ => (2 : Fin 8)) = .structural kind children := found
        cases eq
        exact ⟨[],[.input plan],.source,trusted,fun m _ facts => (ports m (slice_input m facts)).1⟩
      · by_cases six : slot = 6
        · subst slot
          have eq : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
              1 (fun _ => (2 : Fin 8)) = .structural kind children := found
          cases eq
          exact ⟨[],[.input plan],.source,trusted,fun m _ facts => (ports m (slice_input m facts)).2⟩
        · simp [viewHeads,empty,five,six] at found
  | nominal slot d found =>
    change (if slot = 0 ∨ slot = 1 then some desc else none) = some d at found
    split at found
    · rename_i either
      cases Option.some.inj found
      rcases either with rfl|rfl
      · exact ⟨[],[],.source,.source,fun m _ facts => nominal m facts.1 0 (Or.inl rfl)⟩
      · exact ⟨[],[],.source,.source,fun m _ facts => nominal m facts.1 1 (Or.inr rfl)⟩
    · cases found

noncomputable def cert : Refresh pointFirst context :=
  ⟨refines,rfl,support,constraints,cache⟩

noncomputable abbrev observed := GeneralNominalVersionedRefresh232.refresh pointFirst context

theorem step : Step registry root pointFirst observed :=
  ⟨root,.root,.refresh root context cert lo port_sources.1 previously_unknown seen_lo⟩

theorem models (m : Assignment) : Models observed m ↔ Models pointFirst m :=
  GeneralNominalVersionedMixedObservations233.refresh_models cert

end Yulang.GeneralMixedCompoundPointViewTrust308
