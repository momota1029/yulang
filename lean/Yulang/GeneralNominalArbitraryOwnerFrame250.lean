import Yulang.GeneralNominalJournalViewCongruence250
import Yulang.GeneralNominalSnapshotOwner250
/-! Semantic recovery and owner rebase for arbitrary finite journal metadata.
Unlike Formed249, no compile/substitution provenance premise is required. -/
namespace Yulang.GeneralNominalArbitraryOwnerFrame250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247
open GeneralPresenceOrderedDependence247
open GeneralNominalMaterializedOwnerFrame249
open GeneralNominalMaterializedSequenceModels249 (PublicModels same_domain_protected subset_private)
open CommonNominalFullCarrier GeneralPresenceCommonLaws245

theorem recovered (journal : Journal) (old : List (Entry Nat)) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 journal.Models (solve model old assignment) ↔ journal.Models assignment :=
 GeneralNominalJournalViewCongruence250.models_iff
   (GeneralPresenceOrderedRecovery247.solve_compatible model common_laws old assignment valid) journal

theorem models_forward (frame : Frame) (fresh : List (Entry Nat)) (safe : SafeOrder fresh)
 (protectedReads : Protected frame fresh) (assignment : Assignment) (valid : Models frame assignment) :
 Models (rebase frame fresh) (solve model fresh assignment) := by
 constructor
 · apply (GeneralNominalOrderedJournalExpansion249.journal_preserved
     (rebase frame fresh).metadata fresh assignment protectedReads.1).mpr
   apply (GeneralNominalJournalSubst249.ordered_exact frame.definitions assignment frame.metadata).mpr
   exact (recovered frame.metadata frame.definitions assignment
     ((all_append model assignment _ _).mp valid.2).2).mpr valid.1
 · exact GeneralPresenceOrderedExpansion249.models_forward model common_laws frame.definitions fresh safe
     frame.consumers protectedReads.2 assignment valid.2

theorem public_models_iff (frame : Frame) (oldSafe : SafeOrder frame.definitions)
 (fresh : List (Entry Nat)) (safe : SafeOrder fresh) (protectedReads : Protected frame fresh)
 (shared : Nat → Prop)
 (oldPrivate : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (freshPrivate : ∀ name, shared name → ∀ entry ∈ fresh, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels frame shared boundary ↔ PublicModels (rebase frame fresh) shared boundary := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model fresh assignment,models_forward frame fresh safe protectedReads assignment valid,?_⟩
   intro name sharedName
   rw [solve_outside model fresh assignment name (freshPrivate name sharedName)]
   exact agree name sharedName
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model frame.definitions assignment,
     GeneralNominalMaterializedOwnerFrame249.models_backward frame oldSafe fresh assignment valid,?_⟩
   intro name sharedName
   rw [solve_outside model frame.definitions assignment name (oldPrivate name sharedName)]
   exact agree name sharedName

theorem snapshot_public_models_iff (frame : Frame) (oldSafe : SafeOrder frame.definitions)
 (raw : List (Entry Nat)) (within : TargetsWithin raw frame.definitions)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 PublicModels frame shared boundary ↔ PublicModels (GeneralNominalSnapshotOwner250.update frame raw) shared boundary :=
 public_models_iff frame oldSafe _ (GeneralPresenceSnapshotBlock250.refresh_safe _ _ oldSafe within)
   (same_domain_protected frame _ oldSafe (GeneralPresenceSnapshotBlock250.refresh_within _ _ within))
   shared privateNames (subset_private _ _ (GeneralPresenceSnapshotBlock250.refresh_within _ _ within) shared privateNames) boundary
end Yulang.GeneralNominalArbitraryOwnerFrame250
