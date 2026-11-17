import Yulang.GeneralDictionaryVersionedPointFrame233
import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.GeneralNominalVersionedBoundary232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedPointInstalledSelected233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPoint233
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedInstallation231
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {state : State roles} {effect : Effect roles} {model : Assignment}
variable (allocated reserved ordinary)

theorem unique
    (registryEq : effect.registry = registry)
    (planEq : effect.plan = plan allocated reserved ordinary)
    (snapshot : effect.snapshot = state.core)
    (valid : Models (install state effect) model) :
    GeneralNominalVersionedCandidates231.Unique registry (install state effect).core.erased.current.context root declaration.id [] := by
  have framed := GeneralNominalVersionedInstalledEvidence233.frame snapshot valid
  rw [registryEq,planEq] at framed
  have contextEq : (install state effect).core.erased.current.context = (replayPlan (plan allocated reserved ordinary)).packet.context := congrArg (fun p => (replayPlan p).packet.context) planEq
  have prepared := framed.prepared
  rw [contextEq] at prepared
  rw [contextEq]
  have known : ¬ GeneralNominalState.RootPending (replayPlan (plan allocated reserved ordinary)).packet.context.state
      (GeneralNominalVersionedCandidates231.inputs root).demand := by
    exact GeneralDictionaryVersionedPointFrame233.known allocated reserved ordinary
  have survivor : GeneralNominalVersionedCandidates231.Survivor registry
      (replayPlan (plan allocated reserved ordinary)).packet.context root declaration.id [] := by
    refine ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,(replayPlan (plan allocated reserved ordinary)).packet.bounds,?_,prepared,?_⟩
    · rfl
    · unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
        GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
      simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
      rfl
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,identity,_⟩ := other
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem equal_outputs
    (raw : state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (planEq : effect.plan = plan allocated reserved ordinary) (focus) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs (install state effect).core focus model := by
  have terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [] := by
    rw [planEq]; exact children_empty allocated reserved ordinary
  have sites : (install state effect).core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
    (GeneralNominalVersionedTerminal232.raw_eq terminal).trans raw
  intro first one last two _
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp one
  rw [sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp two
  rw [sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem selected
    (registryEq : effect.registry = registry)
    (planEq : effect.plan = plan allocated reserved ordinary)
    (snapshot : effect.snapshot = state.core)
    (raw : state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry (install state effect) root)
    (valid : Models (install state effect) model) :
    GeneralNominalVersionedBoundary232.Local registry (install state effect) root (.selected declaration.id []) := by
  have terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [] := by
    rw [planEq]; exact children_empty allocated reserved ordinary
  have framed := GeneralNominalVersionedInstalledEvidence233.frame snapshot valid
  have ready := GeneralNominalVersionedInstalledEvidence233.ready snapshot terminal
  have packet := GeneralNominalVersionedInstalledEvidence233.replay_holds valid
  have effects := GeneralNominalVersionedInstalledEvidence233.class_effects valid
  rw [registryEq,planEq] at framed
  rw [planEq] at ready packet effects
  apply GeneralNominalVersionedBoundary232.local_iff.mpr
  apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe
    (unique allocated reserved ordinary registryEq planEq snapshot valid) valid framed ready packet effects
  exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict valid
    (fun focus _ => equal_outputs allocated reserved ordinary raw planEq focus)
    (equal_outputs allocated reserved ordinary raw planEq root)

end Yulang.GeneralDictionaryVersionedPointInstalledSelected233
