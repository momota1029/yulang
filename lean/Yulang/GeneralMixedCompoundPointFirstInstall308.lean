import Yulang.GeneralMixedCompoundPointFirstSafety308
import Yulang.GeneralDictionaryCompoundVacuity238

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralMixedCompoundPointFirstInstall308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry checked)
open GeneralDictionaryCompoundFrame238 (before)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundSourcePrefix308 (pointBefore early_reobservation)
open GeneralMixedCompoundPointFirstPlan308 (ctx plan pointFirst effect candidateModel same_plan held model class_effects)
open GeneralMixedCompoundPointFirstSafety308 (safe positions alternatives)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Step Installable Committed)
open GeneralNominalVersionedInstall232 (InstallationModels install_models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

theorem before_reachable : B4TargetV8.Reachable (boundary roles) sourceRegistry root pointBefore := by
  obtain ⟨start,initial,path⟩ := GeneralDictionaryCompoundStep238.initial_reachable
  exact ⟨start,initial,.tail path early_reobservation⟩

theorem emission : (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false := by
  rw [← GeneralDeferredLadderTransport302.emitted_eq same_plan,
    GeneralRebaseCompoundReplacement273.emitted_same,
    GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema]

theorem actual_children : GeneralNominalVersionedFrame231.children plan.packet = [childSite.occurrence] :=
  (GeneralDeferredLadderTransport302.children_eq same_plan).symm.trans
    GeneralDictionaryCompoundVacuity238.current_children

theorem uncommitted : ¬ Committed pointBefore plan := by
  intro previously
  have one := previously.2 childSite.occurrence (actual_children ▸ List.mem_singleton_self _)
  cases one

theorem installation : InstallationModels pointBefore effect candidateModel :=
  (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ before_reachable rfl rfl).mpr
    ⟨model,held,class_effects⟩

theorem installable : Installable registry pointBefore effect :=
  ⟨rfl,rfl,safe,GeneralNominalVersionedMixedObservations233.legacy_cache
    (GeneralDictionaryJournalRefinement228Reobserve.source_cache pointBefore.legacy rfl [] [] []),
    emission,(by intro prior member; cases member),positions,alternatives,candidateModel,installation⟩

theorem step : Step registry root pointBefore pointFirst :=
  ⟨root,.root,.install effect installable uncommitted⟩

theorem point_first_held : Models pointFirst candidateModel :=
  (install_models rfl).mpr installation

theorem reachable : B4TargetV8.Reachable (boundary roles) sourceRegistry root pointFirst := by
  obtain ⟨start,initial,path⟩ := before_reachable
  exact ⟨start,initial,.tail path step⟩

theorem generated_child : GeneralNominalSaturationState.Generated pointFirst.core.erased.current root childSite.occurrence :=
  .child .root (GeneralNominalVersionedInstall232.installed_child (effect := effect)
    (actual_children ▸ List.mem_singleton_self _))

theorem two_step : B4Target.Steps (Step registry root) before pointFirst :=
  .tail (.tail .refl early_reobservation) step

end Yulang.GeneralMixedCompoundPointFirstInstall308
