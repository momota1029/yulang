import Yulang.GeneralMixedCompoundTail307
import Yulang.GeneralMixedCompoundUpperOutcome307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundTailChildOutcome307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedContext extendedSnapshot)
open GeneralDictionaryCompoundBase239 (lo)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperHalt307 (centers)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralMixedCompoundTail307 (no_merge anchor_models reached_tail)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalVersionedCandidates231 (Survivor InspectionPending)
open GeneralNominalState (Known RootPending)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalSaturationState (Generated)
open GeneralSourceDictionaries (Occurrence)
open CommonRoleOutermostResolver

theorem chosen_child {s : State roles} (equal : Models s = Models upperState)
    (centers : s.core.sites = [GeneralNominalCenters.rootSite snapshot.seed root,childSite]) :
    AdministrativeReady s childSite.occurrence := by
  refine ⟨⟨childSite,centers ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩,?_⟩
  intro a one _ b two same
  exact no_merge equal centers one two same

private theorem rejection {s : State roles} (known : ¬ RootPending s.core.erased.current.context.state childSite.occurrence.demand)
    (rawClear : ¬ InspectionPending registry s.core.erased.current.context childSite.occurrence)
    (admin : AdministrativeReady s childSite.occurrence)
    (noSurvivor : ∀ key kids, ¬ Survivor registry s.core.erased.current.context childSite.occurrence key kids) :
    B4TargetV8.Local (boundary roles) registry s childSite.occurrence .rejected := by
  have noSharing : ¬ (boundary roles).SharingConflict registry s childSite.occurrence := by
    rintro ⟨key,kids,unique,_⟩
    exact noSurvivor key kids unique.1
  apply B4TargetV8.Local.ordinary noSharing
  classical
  by_cases merge : (boundary roles).toV7.MergedOutputConflict registry s childSite.occurrence
  · apply B4TargetV7.Local.mergedRejected merge
    rintro ⟨_,key,kids,_,_,one,_,_⟩
    exact noSurvivor key kids one
  · apply B4TargetV7.Local.ordinary merge
    apply B4TargetV6.Local.rejected
    refine ⟨known,Or.inr (Or.inr ⟨?_,Or.inl noSurvivor⟩)⟩
    rintro (pending|absent)
    · exact rawClear pending
    · exact absent admin

theorem at_anchor : B4TargetV8.Local (boundary roles) registry refreshed childSite.occurrence .rejected :=
  rejection GeneralDictionaryCompoundFailure239.known GeneralDictionaryCompoundFailure239.no_inspection_pending
    (chosen_child anchor_models centers) GeneralDictionaryCompoundChild239.no_survivor

theorem at_refresh (ctx : Context) (cert : Refresh refreshed ctx) :
    B4TargetV8.Local (boundary roles) registry (refresh refreshed ctx) childSite.occurrence .rejected := by
  apply rejection
  · exact fun pending => GeneralDictionaryCompoundFailure239.known
      (GeneralNominalRefinements.pending_backwards cert.refines _ pending)
  · rintro ⟨_,d,visible,_,bad,_⟩
    cases List.mem_singleton.mp visible
    exact bad (GeneralMixedCompoundAnyChild307.failed ctx cert)
  · apply chosen_child (funext (fun m => propext ((refresh_models cert).trans (models_iff m).symm))) centers
  · intro key kids
    rintro ⟨_,d,visible,_,_,_,_,_,prepared,_⟩
    cases List.mem_singleton.mp visible
    exact GeneralMixedCompoundAnyChild307.no_prepared ctx cert prepared

theorem unchanged (ctx : Context) (cert : Refresh refreshed ctx)
    (status : Frontier (Occurrence roles)) :
    B4TargetV8.Local (boundary roles) registry refreshed childSite.occurrence status ↔
    B4TargetV8.Local (boundary roles) registry (refresh refreshed ctx) childSite.occurrence status := by
  constructor
  · intro same
    rw [B4TargetV8.local_functional same at_anchor]
    exact at_refresh ctx cert
  · intro same
    rw [B4TargetV8.local_functional same (at_refresh ctx cert)]
    exact at_anchor

/-- The output-bearing root's actual child has the same exact V8 verdict
through every immediate successor. Nevertheless the anchor can take a step
while no successor can. A child observer preserving only this verdict is
therefore not an exact raw control observer. -/
theorem silent_but_operationally_strict :
    B4TargetV8.Local (boundary roles) registry refreshed childSite.occurrence .rejected ∧
    B4TargetV8.Local (boundary roles) registry upperState childSite.occurrence .rejected ∧
    (∃ t, GeneralNominalVersionedMixedKernel234.Step registry root refreshed t) ∧
    (∀ t, ¬ GeneralNominalVersionedMixedKernel234.Step registry root upperState t) :=
  ⟨at_anchor,GeneralMixedCompoundUpperOutcome307.rejected_child,
    ⟨upperState,GeneralMixedCompoundUpperRefresh307.step⟩,GeneralMixedCompoundUpperHalt307.halted⟩

end Yulang.GeneralMixedCompoundTailChildOutcome307
