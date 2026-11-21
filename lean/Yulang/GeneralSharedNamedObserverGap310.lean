import Yulang.GeneralSharedNamedCompiler310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23500
set_option maxHeartbeats 12500000
/-! Real merge changes a generated child's readiness even if all models,
ordinary input observations, occurrence lists and packet ledger agree.
This is a readback-separation, not a termination or halt claim. -/
namespace Yulang.GeneralSharedNamedObserverGap310
open GeneralSharedNamedSource310 (root registry compiled)
open GeneralSharedNamedPlan310 (loSite hiSite)
open GeneralSharedNamedInstall310 (after)
open GeneralSharedNamedMerge310 (merged same_inputs)
open GeneralSharedNamedEvidence310 (siblings_different alias_identity)
open GeneralSharedNamedNodes310 (focus Node)
open GeneralSharedNamedSelection310 (actual_pick)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Site Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Packet)

theorem not_ready_before : ¬ AdministrativeReady after loSite.occurrence := by
  intro old
  have one : loSite ∈ after.core.sites := GeneralSharedNamedInstall310.centers ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have two : hiSite ∈ after.core.sites := GeneralSharedNamedInstall310.centers ▸
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact siblings_different (alias_identity (old.2 loSite one rfl hiSite two same_inputs))

theorem not_selected_before : ¬ Local registry after loSite.occurrence (.selected 2 []) := by
  intro old
  apply not_ready_before
  exact GeneralNominalVersionedMixedSelectedFrame235.administrative_ready
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp old)

theorem selected_after : Local registry merged loSite.occurrence (.selected 2 []) :=
  actual_pick .low

structure BlindView where
  models : Assignment → Prop
  sites : List (Site roles)
  raw : List (GeneralNominalDemandMerging.Site roles)
  edges : List (Occurrence roles × Occurrence roles)
  ledger : List (Plan roles)
  packets : List (Packet roles)

def observe (s : State roles) : BlindView :=
  ⟨Models s,s.core.sites,s.core.erased.current.sites,s.core.erased.current.edges,s.plans,s.core.erased.current.packets⟩

theorem indistinguishable : observe after = observe merged := by
  have same : Models after = Models merged := funext fun m =>
    propext (GeneralSharedNamedMerge310.models m).symm
  unfold observe
  rw [same]
  rfl

theorem no_blind_selected (read : BlindView → Prop)
    (exact : ∀ s : State roles, read (observe s) ↔ Local registry s loSite.occurrence (.selected 2 [])) :
    False := by
  have accepted := (exact merged).mpr selected_after
  rw [← indistinguishable] at accepted
  exact not_selected_before ((exact after).mp accepted)

theorem anchored_separation :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root after ∧
    GeneralNominalVersionedMixedKernel234.Step compiled root after merged ∧
    observe after = observe merged ∧
    ¬ Local registry after loSite.occurrence (.selected 2 []) ∧
    Local registry merged loSite.occurrence (.selected 2 []) :=
  ⟨GeneralSharedNamedInstall310.reachable,GeneralSharedNamedMerge310.step,indistinguishable,
    not_selected_before,selected_after⟩

end Yulang.GeneralSharedNamedObserverGap310
