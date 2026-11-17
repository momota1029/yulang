import Yulang.GeneralPresenceSnapshotBlock250
import Yulang.GeneralNominalMaterializedSequenceModels249
/-! A concrete finite refresh producer for materialized owner frames. RHSs are
snapshots through the old definitions, not simultaneous new-state equations.
Target inclusion and public privacy remain explicit; source Step is separate. -/
namespace Yulang.GeneralNominalSnapshotOwner250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedOwnerFrame249
open GeneralNominalMaterializedSequenceModels249
open CommonNominalFullCarrier

abbrev Block := List (Entry Nat)
def update (frame : Frame) (raw : Block) : Frame :=
 rebase frame (GeneralPresenceSnapshotBlock250.refresh frame.definitions raw)

theorem update_formed (frame : Frame) (formed : Formed frame) (raw : Block)
 (within : TargetsWithin raw frame.definitions) : Formed (update frame raw) :=
 rebase_formed frame formed _ (GeneralPresenceSnapshotBlock250.refresh_safe _ _ formed.2 within)

theorem update_within (frame : Frame) (raw : Block) (within : TargetsWithin raw frame.definitions) :
 TargetsWithin (update frame raw).definitions frame.definitions :=
 GeneralPresenceSnapshotBlock250.refresh_within _ _ within

theorem public_models_iff (frame : Frame) (formed : Formed frame) (raw : Block)
 (within : TargetsWithin raw frame.definitions) (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels frame shared boundary ↔ PublicModels (update frame raw) shared boundary :=
 GeneralNominalMaterializedOwnerFrame249.public_models_iff frame formed _
   (GeneralPresenceSnapshotBlock250.refresh_safe _ _ formed.2 within)
   (same_domain_protected frame _ formed.2 (update_within frame raw within)) shared privateNames
   (subset_private _ _ (update_within frame raw within) shared privateNames) boundary

theorem exact_original_constraints (frame : Frame) (raw : Block) (coherent : Coherent raw)
 (assignment : Assignment) : Models (update frame raw) assignment ↔
 (GeneralNominalJournalSubst249.subst (mapping frame.definitions) frame.metadata).Models assignment ∧
 All model assignment (rewrite frame.definitions frame.consumers ++
   block (transform (mapping frame.definitions) raw)) := by
 change _ ∧ All model assignment (_ ++ block (GeneralPresenceSnapshotBlock250.refresh _ _)) ↔ _
 simp only [all_append,GeneralPresenceSnapshotBlock250.refresh_models _ _ coherent]
 rfl
end Yulang.GeneralNominalSnapshotOwner250
