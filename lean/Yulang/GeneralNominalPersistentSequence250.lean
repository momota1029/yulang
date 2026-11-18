import Yulang.GeneralNominalStableSlots250
import Yulang.GeneralNominalMaterializedSequence249
/-! Finite sequences construct every fresh safe block, retain all reserved
keys, and preserve public models. The supplied list is not proved finite by
the source scheduler; no Acc claim follows from this recursion. -/
namespace Yulang.GeneralNominalPersistentSequence250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalPersistentOwner250 (Block update)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedSequenceModels249 (PublicModels subset_private)
open GeneralNominalCommonBridge (Assignment)

def run : Frame → List Block → Frame
 | frame,[] => frame
 | frame,raw :: rest => run (update frame raw) rest

theorem targets_run (frame : Frame) (blocks : List Block) :
 (run frame blocks).definitions.map Prod.fst = frame.definitions.map Prod.fst := by
 induction blocks generalizing frame with
 | nil => rfl
 | cons raw rest ih => exact (ih (update frame raw)).trans (GeneralNominalPersistentOwner250.targets_update frame raw)

theorem safe_run (frame : Frame) (safe : SafeOrder frame.definitions) (blocks : List Block) :
 SafeOrder (run frame blocks).definitions := by
 induction blocks generalizing frame with
 | nil => exact safe
 | cons raw rest ih => exact ih (update frame raw) (GeneralNominalPersistentOwner250.safe_update frame safe raw)

theorem targets_length (frame : Frame) (blocks : List Block) :
 (run frame blocks).definitions.length = frame.definitions.length := by
 have equal := congrArg List.length (targets_run frame blocks)
 simpa only [List.length_map] using equal

theorem raw_coverage (frame : Frame) (blocks : List Block) (raw : Block)
 (within : TargetsWithin raw frame.definitions) : TargetsWithin raw (run frame blocks).definitions := by
 intro entry member
 obtain ⟨original,present,equal⟩ := within entry member
 have found : entry.1 ∈ frame.definitions.map Prod.fst := List.mem_map.mpr ⟨original,present,equal⟩
 rw [← targets_run frame blocks] at found
 exact List.mem_map.mp found

theorem public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions) (blocks : List Block)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels frame shared boundary ↔ PublicModels (run frame blocks) shared boundary := by
 induction blocks generalizing frame with
 | nil => exact Iff.rfl
 | cons raw rest ih =>
   exact (GeneralNominalPersistentOwner250.public_models_iff frame safe raw shared privateNames boundary).trans
     (ih (update frame raw) (GeneralNominalPersistentOwner250.safe_update frame safe raw)
       (subset_private _ _ (GeneralPresencePersistentSnapshot250.refresh_within _ _) shared privateNames))

theorem actual_owner_coverage (frame : Frame) (seed root declaration : Nat) (names : List Nat)
 (blocks : List Block) (bindings : GeneralNominalAllocation.Bindings) :
 TargetsWithin (GeneralNominalRebaseDefinitions241.entries seed root declaration bindings names)
   (run (GeneralNominalFrameReservation250.extend frame (GeneralNominalStableSlots250.slots seed root declaration names)) blocks).definitions :=
 raw_coverage _ blocks _ (GeneralNominalStableSlots250.entries_covered frame seed root declaration names bindings)
end Yulang.GeneralNominalPersistentSequence250
