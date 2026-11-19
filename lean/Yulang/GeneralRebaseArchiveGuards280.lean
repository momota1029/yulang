import Yulang.GeneralRebaseArchiveTrust280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseArchiveGuards280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseArchiveTrust280
open GeneralRebaseEffectSnapshot280 (EffectRelated)
open GeneralNominalVersionedDiagnostic232 (boundary AdministrativeReady)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle CandidateCycle Safe)
open GeneralNominalVersionedInstall232 (InstallationModels installCore install)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe Committed)

variable {roles : Roles.RoleDecls} {s : State roles} {ys : List (Effect roles)}

theorem models (pair : Correspond s.effects ys) :
    Models s = Models (changeEffects s ys) :=
  funext fun m => propext ((archive s pair).models m)

theorem cyclic (pair : Correspond s.effects ys) (origin : GeneralNominalRecursiveInspection.Origin) :
    Cyclic s origin ↔ Cyclic (changeEffects s ys) origin :=
  GeneralNominalVersionedCycles232.full_models_only (models pair)

theorem root_cycle (pair : Correspond s.effects ys) (root : Occurrence roles) :
    RootCycle s root ↔ RootCycle (changeEffects s ys) root := by
  unfold RootCycle
  simp only [cyclic pair]
  rfl

theorem candidate_cycle (pair : Correspond s.effects ys) (r : Registry) (root : Occurrence roles) :
    CandidateCycle r s root ↔ CandidateCycle r (changeEffects s ys) root := by
  unfold CandidateCycle
  simp only [cyclic pair]
  rfl

theorem admin_ready (pair : Correspond s.effects ys) (root : Occurrence roles) :
    AdministrativeReady s root ↔ AdministrativeReady (changeEffects s ys) root := by
  unfold AdministrativeReady
  simp only [models pair]
  rfl

theorem root_k2 (pair : Correspond s.effects ys) (r : Registry) (root : Occurrence roles) :
    (boundary roles).RootK2 r s root ↔ (boundary roles).RootK2 r (changeEffects s ys) root := by
  change (_ ∨ RootCycle s root) ↔ (_ ∨ RootCycle (changeEffects s ys) root)
  rw [root_cycle pair]
  rfl

theorem candidate_k2 (pair : Correspond s.effects ys) (r : Registry) (root : Occurrence roles) :
    (boundary roles).CandidateK2 r s root ↔ (boundary roles).CandidateK2 r (changeEffects s ys) root := by
  change (_ ∨ CandidateCycle r s root) ↔ (_ ∨ CandidateCycle r (changeEffects s ys) root)
  rw [candidate_cycle pair]
  rfl

theorem pending (pair : Correspond s.effects ys) (r : Registry) (root : Occurrence roles) :
    (boundary roles).InspectionPending r s root ↔
      (boundary roles).InspectionPending r (changeEffects s ys) root := by
  change (_ ∨ ¬ AdministrativeReady s root) ↔ (_ ∨ ¬ AdministrativeReady (changeEffects s ys) root)
  rw [admin_ready pair]
  rfl

theorem safe_known (pair : Correspond s.effects ys) (r : Registry) (root : Occurrence roles) :
    B4TargetV8.SafeKnown (boundary roles) r s root ↔
    B4TargetV8.SafeKnown (boundary roles) r (changeEffects s ys) root := by
  unfold B4TargetV8.SafeKnown B4TargetV7.SafeKnown B4TargetV6.SafeKnown B4Target.SafeKnown
  simp only [root_k2 pair,candidate_k2 pair,pending pair]
  rfl

theorem safe (pair : Correspond s.effects ys) (p : Plan roles) :
    Safe s p ↔ Safe (changeEffects s ys) p := by
  unfold Safe
  simp only [cyclic pair]

theorem alternatives (pair : Correspond s.effects ys) (r : Registry) (input : Site roles) :
    AlternativesSafe r s input ↔ AlternativesSafe r (changeEffects s ys) input := by
  unfold AlternativesSafe
  simp only [safe pair]
  rfl

theorem old_live (pair : Correspond s.effects ys) (core : GeneralNominalCenteredSteps.State roles)
    (m : Assignment) :
    (∀ e ∈ s.effects, e.Live core m) ↔ (∀ f ∈ ys, f.Live core m) := by
  constructor
  · intro had f contains
    obtain ⟨e,member,same⟩ := pair.2 f contains
    exact (same.live core m).mp (had e member)
  · intro has e contains
    obtain ⟨f,member,same⟩ := pair.1 e contains
    exact (same.live core m).mpr (has f member)

theorem witnesses (pair : Correspond s.effects ys) (effect : Effect roles) (m : Assignment) :
    InstallationModels s effect m ↔ InstallationModels (changeEffects s ys) effect m := by
  unfold InstallationModels
  rw [models pair]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (old_live pair (installCore s.core effect.plan) m)))))

theorem enabled (pair : Correspond s.effects ys) (r : Registry) (effect : Effect roles) :
    Installable r s effect ↔ Installable r (changeEffects s ys) effect := by
  constructor <;> intro h
  · exact ⟨h.registry_eq,h.snapshot_eq,(safe_known pair _ _).mp h.safe,(cache_iff pair _).mp h.cache,
      h.materialized,h.choice,(safe pair _).mp h.positions,(alternatives pair _ _).mp h.alternatives,
      Exists.imp (fun m cert => (witnesses pair effect m).mp cert) h.common⟩
  · exact ⟨h.registry_eq,h.snapshot_eq,(safe_known pair _ _).mpr h.safe,(cache_iff pair _).mpr h.cache,
      h.materialized,h.choice,(safe pair _).mpr h.positions,(alternatives pair _ _).mpr h.alternatives,
      Exists.imp (fun m cert => (witnesses pair effect m).mpr cert) h.common⟩

theorem committed (pair : Correspond s.effects ys) (p : Plan roles) :
    Committed s p ↔ Committed (changeEffects s ys) p := by
  unfold Committed GeneralNominalVersionedInstallStep232.Committed
  rw [models pair]
  rfl

end Yulang.GeneralRebaseArchiveGuards280
