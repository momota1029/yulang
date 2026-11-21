import Yulang.GeneralLiveCompoundUpperSnapshot316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralLiveCompoundUpperRefresh316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry)
open GeneralLiveCompoundRoot316 (plan)
open GeneralDictionaryCompoundBase239 (extendedBase extendedView)
open GeneralLiveCompoundLowerSnapshot316 (extendedSnapshot pointDesc)
open GeneralLiveCompoundLowerRefresh316 (refreshed lower_reachable slice)
open GeneralMixedCompoundUpperBase307 (base view embed source source_old source_new upper heads viewHeads)
open GeneralLiveCompoundUpperSnapshot316 (desc snap context refineRaw base_transport nominals upper_supported upper_unknown upper_known support)

open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedSupport233 (trusted_models)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

theorem read_old (m : Assignment) (h : Models refreshed m) :
    Models GeneralDictionaryCompoundRefresh239.refreshed m :=
  (GeneralDictionaryCompoundRefresh239.models_iff m).mpr
    ((GeneralLiveCompoundPoint316.point_models m).mp ((GeneralLiveCompoundLowerRefresh316.models_iff m).mp h))

theorem input_trusted : GeneralNominalVersionedSupport233.Trusted refreshed [.input plan] := by
  refine .input plan .source (List.mem_cons_self ..) ?_
  intro slot visited test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound snapshot model valid.1
    (GeneralNominalSupport.head_recorded head)

theorem aggregate (m : Assignment) (facts : GeneralNominalVersionedSupport233.SliceModels refreshed [.input plan] m) :
    Equivalent (m upper).1 .emptyRecord :=
  GeneralMixedCompoundUpperTrust307.aggregate m (slice m facts)

theorem ports (m : Assignment) (facts : GeneralNominalVersionedSupport233.SliceModels refreshed [.input plan] m) :
    Equivalent (m GeneralDictionaryCompoundBase239.lo).1 (variant 0 (m 4).1) ∧
    Equivalent (m GeneralDictionaryCompoundBase239.hi).1 (variant 0 (m 2).1) :=
  GeneralMixedCompoundUpperTrust307.ports m (slice m facts)

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
        exact ⟨[],[.input plan],.source,input_trusted,fun m _ facts => aggregate m facts⟩
    · by_cases five : slot = 5
      · subst slot
        have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
            1 (fun _ => (4 : Fin 8)) = .structural kind children := found
        cases same
        exact ⟨[],[.input plan],.source,input_trusted,fun m _ facts => (ports m facts).1⟩
      · by_cases six : slot = 6
        · subst slot
          have same : GeneralNormalizedObservation.Head.structural (shapes := GeneralDictionaryCompoundBase239.viewShapes)
              1 (fun _ => (2 : Fin 8)) = .structural kind children := found
          cases same
          exact ⟨[],[.input plan],.source,input_trusted,fun m _ facts => (ports m facts).2⟩
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
  ⟨refineRaw,rfl,support,fun m h => GeneralMixedCompoundUpperRefresh307.cert.constraints m (read_old m h),cache⟩

noncomputable abbrev upperState := GeneralNominalVersionedRefresh232.refresh refreshed context

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root refreshed upperState :=
  ⟨root,.root,.refresh root context cert upper upper_supported upper_unknown upper_known⟩

theorem models_iff (m : Assignment) : Models upperState m ↔ Models refreshed m :=
  GeneralNominalVersionedMixedObservations233.refresh_models cert

theorem upper_reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root upperState := by
  obtain ⟨start,initial,path⟩ := lower_reachable
  exact ⟨start,initial,.tail path step⟩

theorem old_models (m : Assignment) :
    Models upperState m ↔ Models GeneralMixedCompoundUpperRefresh307.upperState m := by
  rw [GeneralMixedCompoundUpperRefresh307.models_iff m,models_iff m,GeneralLiveCompoundLowerRefresh316.models_iff m,
    GeneralDictionaryCompoundRefresh239.models_iff m,GeneralLiveCompoundPoint316.point_models m]

end Yulang.GeneralLiveCompoundUpperRefresh316
