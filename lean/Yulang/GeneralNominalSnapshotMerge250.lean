import Yulang.GeneralNominalSnapshotOwner250
import Yulang.GeneralNominalRebaseDefinitions241
/-! Actual lower/upper capture formulas feed the finite snapshot update.
Coherence is produced from the concrete owner keys, not assumed. This does not
assert that every next capture targets an already reserved slot. -/
namespace Yulang.GeneralNominalSnapshotMerge250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralNominalMaterializedOwnerFrame249 (Frame Formed Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalAllocation (Bindings)
open GeneralNominalRebaseDefinitions241 (entries)
open GeneralNominalSnapshotOwner250
open CommonNominalFullCarrier

def updateMerge (frame : Frame) (seed root declaration : Nat) (bindings : Bindings) (names : List Nat) : Frame :=
 update frame (entries seed root declaration bindings names)

theorem merge_formed (frame : Frame) (formed : Formed frame)
 (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (within : TargetsWithin (entries seed root declaration bindings names) frame.definitions) :
 Formed (updateMerge frame seed root declaration bindings names) := update_formed frame formed _ within

theorem merge_public_models_iff (frame : Frame) (formed : Formed frame)
 (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (within : TargetsWithin (entries seed root declaration bindings names) frame.definitions)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 PublicModels frame shared boundary ↔ PublicModels (updateMerge frame seed root declaration bindings names) shared boundary :=
 public_models_iff frame formed _ within shared privateNames boundary

theorem merge_exact (frame : Frame) (seed root declaration : Nat) (bindings : Bindings)
 (names : List Nat) (assignment : Assignment) :
 Models (updateMerge frame seed root declaration bindings names) assignment ↔
 (GeneralNominalJournalSubst249.subst (mapping frame.definitions) frame.metadata).Models assignment ∧
 All model assignment (rewrite frame.definitions frame.consumers ++
   block (transform (mapping frame.definitions) (entries seed root declaration bindings names))) :=
 exact_original_constraints frame _ (GeneralNominalRebaseDefinitions241.coherent seed root declaration bindings names) assignment
end Yulang.GeneralNominalSnapshotMerge250
