import Yulang.GeneralNominalMaterializedSequence249
import Yulang.GeneralNominalJournalSubstSupport249
/-! Fixed-domain finite refresh sequences preserve public models. Every supplied
block is safe; no new metadata is inserted. This is not an infinite-run bound. -/
namespace Yulang.GeneralNominalMaterializedSequenceModels249
open GeneralNominalMaterializedOwnerFrame249 GeneralNominalMaterializedSequence249
open GeneralNominalMaterializedDomain249
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRebase247
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def PublicModels (frame : Frame) (shared : Nat → Prop) (boundary : Assignment) : Prop :=
 ∃ assignment, Models frame assignment ∧ Agrees model shared assignment boundary

theorem subset_private (old fresh : Block) (within : TargetsWithin fresh old) (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ old, entry.1 ≠ name) :
 ∀ name, shared name → ∀ entry ∈ fresh, entry.1 ≠ name := by
 intro name sharedName entry member
 obtain ⟨original,present,equal⟩ := within entry member
 rw [← equal]
 exact privateNames name sharedName original present

theorem same_domain_protected (frame : Frame) (fresh : Block)
 (safe : SafeOrder frame.definitions) (within : TargetsWithin fresh frame.definitions) : Protected frame fresh :=
 ⟨GeneralNominalJournalSubstSupport249.within_protected frame.definitions safe fresh within frame.metadata,
 GeneralPresenceOrderedExpansion249.protected_of_within frame.definitions fresh safe within frame.consumers⟩

theorem canonical_protected (frame : Frame) (current fresh : Block)
 (safe : SafeOrder frame.definitions) (withinCurrent : TargetsWithin current frame.definitions)
 (withinFresh : TargetsWithin fresh frame.definitions) : Protected (canonical frame current) fresh := by
 constructor
 · change GeneralPresenceProtectionCheck249.Protected
     (GeneralNominalJournalSupport249.support (rebase (canonical frame current) fresh).metadata) fresh
   rw [rebase_canonical frame current fresh safe withinCurrent]
   exact GeneralNominalJournalSubstSupport249.within_protected frame.definitions safe fresh withinFresh frame.metadata
 · change ∀ name ∈ GeneralPresenceConsumerSupport246.listTypedReads
     (rewrite current (rewrite frame.definitions frame.consumers)), ∀ entry ∈ fresh, entry.1 ≠ name
   rw [GeneralPresenceOrderedSyntax247.rewrite_absorbs frame.definitions current safe withinCurrent]
   exact GeneralPresenceOrderedExpansion249.protected_of_within frame.definitions fresh safe withinFresh frame.consumers

theorem canonical_models_iff (frame : Frame) (formed : Formed frame) (current fresh : Block)
 (safeCurrent : SafeOrder current) (safeFresh : SafeOrder fresh)
 (withinCurrent : TargetsWithin current frame.definitions) (withinFresh : TargetsWithin fresh frame.definitions)
 (shared : Nat → Prop) (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels (canonical frame current) shared boundary ↔ PublicModels (canonical frame fresh) shared boundary := by
 have result := GeneralNominalMaterializedOwnerFrame249.public_models_iff (canonical frame current)
   ⟨Materialized.substituted formed.1 (mapping frame.definitions),safeCurrent⟩ fresh safeFresh
   (canonical_protected frame current fresh formed.2 withinCurrent withinFresh) shared
   (subset_private frame.definitions current withinCurrent shared privateNames)
   (subset_private frame.definitions fresh withinFresh shared privateNames) boundary
 rw [rebase_canonical frame current fresh formed.2 withinCurrent] at result
 exact result

theorem canonical_run_models_iff (frame : Frame) (formed : Formed frame) (current : Block) (blocks : List Block)
 (safeCurrent : SafeOrder current) (withinCurrent : TargetsWithin current frame.definitions)
 (safeBlocks : ∀ block ∈ blocks, SafeOrder block)
 (withinBlocks : ∀ block ∈ blocks, TargetsWithin block frame.definitions)
 (shared : Nat → Prop) (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels (canonical frame current) shared boundary ↔ PublicModels (run (canonical frame current) blocks) shared boundary := by
 induction blocks generalizing current with
 | nil => exact Iff.rfl
 | cons next rest ih =>
   rw [run,rebase_canonical frame current next formed.2 withinCurrent]
   exact (canonical_models_iff frame formed current next safeCurrent (safeBlocks next (by simp))
     withinCurrent (withinBlocks next (by simp)) shared privateNames boundary).trans
     (ih next (safeBlocks next (by simp)) (withinBlocks next (by simp))
       (fun block member => safeBlocks block (by simp [member]))
       (fun block member => withinBlocks block (by simp [member])))

theorem run_models_iff (frame : Frame) (formed : Formed frame) (blocks : List Block)
 (safeBlocks : ∀ block ∈ blocks, SafeOrder block)
 (withinBlocks : ∀ block ∈ blocks, TargetsWithin block frame.definitions)
 (shared : Nat → Prop) (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels frame shared boundary ↔ PublicModels (run frame blocks) shared boundary := by
 cases blocks with
 | nil => exact Iff.rfl
 | cons next rest =>
   exact (GeneralNominalMaterializedOwnerFrame249.public_models_iff frame formed next (safeBlocks next (by simp))
     (same_domain_protected frame next formed.2 (withinBlocks next (by simp))) shared privateNames
     (subset_private frame.definitions next (withinBlocks next (by simp)) shared privateNames) boundary).trans
     (canonical_run_models_iff frame formed next rest (safeBlocks next (by simp)) (withinBlocks next (by simp))
       (fun block member => safeBlocks block (by simp [member]))
       (fun block member => withinBlocks block (by simp [member])) shared privateNames boundary)
end Yulang.GeneralNominalMaterializedSequenceModels249
