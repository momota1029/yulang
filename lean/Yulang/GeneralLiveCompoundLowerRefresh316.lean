import Yulang.GeneralLiveCompoundLowerSnapshot316
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLiveCompoundLowerRefresh316
open GeneralDictionaryJournalRefinement228Source GeneralDictionaryJournalRefinement228Reobserve
open GeneralLiveCompoundPoint316 (point point_models point_reachable)
open GeneralDictionaryCompoundBase239 GeneralLiveCompoundLowerSnapshot316
open GeneralNominalVersionedSupport233 GeneralNominalVersionedMixedObservations233
open GeneralSourceState (equationAtoms)

open GeneralLiveCompoundRoot316 (plan)
open GeneralLiveCompoundInstall316 (inputs_iff)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry)
open GeneralNominalCommonBridge (Assignment)

theorem trusted : Trusted point [.input plan] := by
  refine .input plan .source (List.mem_cons_self ..) ?_
  intro slot visited test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound snapshot model valid.1
    (GeneralNominalSupport.head_recorded head)

theorem slice (m : Assignment) (facts : SliceModels point [.input plan] m) :
    SliceModels GeneralDictionaryCompoundPoint238.point [.input GeneralDictionaryCompoundObstruction238.oldPlan] m := by
  refine ⟨facts.1,facts.2.1,?_⟩
  intro fact member
  cases List.mem_singleton.mp member
  exact (inputs_iff m).mp (facts.2.2 _ (List.mem_singleton_self _))

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
  constraints := fun m valid => (GeneralDictionaryCompoundRefresh239.certificate.constraints m ((point_models m).mp valid))
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
          exact ⟨[],[.input plan],.source,
            trusted,fun m _ facts => GeneralDictionaryCompoundTrust239.lower m (slice m facts)⟩
        · by_cases six : slot = 6
          · subst slot
            have same : GeneralNormalizedObservation.Head.structural (shapes := viewShapes) 1 (fun _ => (2 : Fin 7)) = .structural kind children := found
            cases same
            exact ⟨[],[.input plan],.source,
              trusted,fun m _ facts => GeneralDictionaryCompoundTrust239.upper m (slice m facts)⟩
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

theorem lower_unknown : ¬ GeneralNominalState.Known point.core.erased.current.context.state lo := by
  rintro ⟨slot,same,_⟩
  have small := slot.isLt
  change slot.val < 5 at small
  change slot.val = lo at same
  have high : 4 < lo := GeneralNominalIdentities.source_above_seed snapshot.seed _
  omega

theorem lower_known : GeneralNominalState.Known extendedSnapshot lo :=
  ⟨(5 : Fin 7),rfl,Or.inl (by intro h; cases h)⟩

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root point refreshed :=
  ⟨root,.root,.refresh root extendedContext certificate lo (supported 5 (by decide)) lower_unknown lower_known⟩

theorem lower_reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root refreshed := by
  obtain ⟨first,initial,path⟩ := point_reachable
  exact ⟨first,initial,.tail path step⟩


end Yulang.GeneralLiveCompoundLowerRefresh316
