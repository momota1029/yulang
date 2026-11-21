import Yulang.GeneralMixedCompoundUpperTrust307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralMixedCompoundUpperRefresh307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundBase239 (extendedBase extendedView)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot pointDesc)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperBase307 (base view embed source source_old source_new upper heads viewHeads)
open GeneralMixedCompoundUpperSnapshot307 (desc snap context refineRaw base_transport nominals upper_supported upper_unknown upper_known support)
open GeneralMixedCompoundUpperTrust307 (input_trusted aggregate ports)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedSupport233 (trusted_models)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

theorem assignment (m : Assignment) :
    GeneralNominalCommonBridge.assignment base m ∘ embed = GeneralNominalCommonBridge.assignment extendedBase m :=
  GeneralNominalRefinements.assignment_transport refineRaw m

theorem read_base (m : Assignment) (valid : Models refreshed m) :
    GeneralNominalCommonBridge.Models base m := by
  have old : GeneralNominalCommonBridge.Models extendedBase m := valid.1.1.1
  have new := aggregate m (trusted_models input_trusted valid)
  refine ⟨?_,?_,fun _ h => nomatch h⟩
  · apply (PresenceNormalForm.all_append ..).mpr
    constructor
    · rw [PresenceNormalForm.all_rename,assignment]
      exact old.1
    · intro atom member
      simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact new.1
      · exact new.2
  · intro i term found
    revert found
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro found
      have eq : term = .emptyRecord := Option.some.inj found.symm
      subst term; exact new
    · rw [base_transport]
      intro found
      obtain ⟨expr,recorded,renamed⟩ := Option.map_eq_some_iff.mp found
      subst term
      have same := old.2.1 j expr recorded
      change Equivalent (m (source (embed j))).1
        ((expr.rename embed).eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base m))
      rw [source_old,TyTerm.eval_rename,assignment]
      exact same

theorem cache : CacheSound refreshed snap := by
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
      · have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            0 Fin.elim0 = .structural kind children := found
        cases same
        exact ⟨[],[],.source,.source,fun m old _ =>
          old.1.1.2.1 (2 : Fin 5) .emptyRecord rfl⟩
      · have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            0 Fin.elim0 = .structural kind children := found
        cases same
        exact ⟨[],[.input oldPlan],.source,input_trusted,fun m _ facts => aggregate m facts⟩
    · by_cases five : slot = 5
      · subst slot
        have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            1 (fun _ => (4 : Fin 8)) = .structural kind children := found
        cases same
        exact ⟨[],[.input oldPlan],.source,input_trusted,fun m _ facts => (ports m facts).1⟩
      · by_cases six : slot = 6
        · subst slot
          have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
              1 (fun _ => (2 : Fin 8)) = .structural kind children := found
          cases same
          exact ⟨[],[.input oldPlan],.source,input_trusted,fun m _ facts => (ports m facts).2⟩
        · simp [viewHeads,empty,five,six] at found
  | nominal slot d found =>
    change (if slot = 0 ∨ slot = 1 then some desc else none) = some d at found
    split at found
    · rename_i either
      cases Option.some.inj found
      refine ⟨[],[],.source,.source,?_⟩
      intro m _ valid
      have point := (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mpr valid.1
      have move (vs)
          (fits : GeneralNominalState.FitsAll GeneralDictionaryJournalRefinement228Source.base m
            GeneralDictionaryJournalRefinement228Reobserve.exactCopy.arguments vs) :
          GeneralNominalState.FitsAll base m desc.arguments vs := by
        change GeneralNominalState.FitsAll GeneralDictionaryJournalRefinement228Source.base m [.type ((2 : Fin 5),2),.type (2,2)] vs at fits
        change GeneralNominalState.FitsAll base m [.type ((2 : Fin 8),2),.type (2,2)] vs
        have one (v) (h : GeneralNominalState.Fits GeneralDictionaryJournalRefinement228Source.base m
            (.type ((2 : Fin 5),2)) v) :
            GeneralNominalState.Fits base m (.type ((2 : Fin 8),2)) v := by
          cases v with
          | inl t => exact h
          | inr r => cases h
        cases fits with
        | cons x xs => cases xs with
          | cons y ys => cases ys; exact .cons (one _ x) (.cons (one _ y) .nil)
      rcases either with rfl|rfl
      · obtain ⟨values,fits,equal⟩ := point.2.1 (0 : Fin 5) _ rfl
        exact ⟨values,move values fits,equal⟩
      · obtain ⟨values,fits,equal⟩ := point.2.1 (1 : Fin 5) _ rfl
        exact ⟨values,move values fits,equal⟩
    · cases found

noncomputable def cert : Refresh refreshed context :=
  ⟨refineRaw,rfl,support,fun m h => ⟨read_base m h,h.1.1.2.2⟩,cache⟩

noncomputable abbrev upperState := GeneralNominalVersionedRefresh232.refresh refreshed context

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root refreshed upperState :=
  ⟨root,.root,.refresh root context cert upper upper_supported upper_unknown upper_known⟩

theorem models_iff (m : Assignment) : Models upperState m ↔ Models refreshed m :=
  GeneralNominalVersionedMixedObservations233.refresh_models cert

end Yulang.GeneralMixedCompoundUpperRefresh307
