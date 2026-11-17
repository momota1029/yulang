import Yulang.GeneralPresencePersistentSnapshot250
import Yulang.GeneralNominalJournalAppend250
/-! Persistent slots prevent an unused slot from disappearing between owner
refreshes. Safety is constructed for every raw list; coherent covered entries
are all retained. This finite transformer is not an actual source scheduler. -/
namespace Yulang.GeneralNominalPersistentOwner250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedOwnerFrame249 (Frame Models rebase)
open GeneralNominalMaterializedSequenceModels249 (PublicModels same_domain_protected subset_private)
open GeneralNominalJournalAppend250 (Delta attach subst)
open CommonNominalFullCarrier
abbrev Block := List (Entry Nat)

def update (frame : Frame) (raw : Block) : Frame :=
 rebase frame (GeneralPresencePersistentSnapshot250.refresh frame.definitions raw)

theorem safe_update (frame : Frame) (safe : SafeOrder frame.definitions) (raw : Block) :
 SafeOrder (update frame raw).definitions := GeneralPresencePersistentSnapshot250.refresh_safe _ _ safe

theorem targets_update (frame : Frame) (raw : Block) :
 (update frame raw).definitions.map Prod.fst = frame.definitions.map Prod.fst :=
 GeneralPresencePersistentSnapshot250.target_list _ _

theorem public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions) (raw : Block)
 (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) : PublicModels frame shared boundary ↔ PublicModels (update frame raw) shared boundary :=
 GeneralNominalArbitraryOwnerFrame250.public_models_iff frame safe _ (safe_update frame safe raw)
   (same_domain_protected frame _ safe (GeneralPresencePersistentSnapshot250.refresh_within _ _))
   shared privateNames (subset_private _ _ (GeneralPresencePersistentSnapshot250.refresh_within _ _) shared privateNames) boundary

theorem raw_constraints (frame : Frame) (raw : Block)
 (within : TargetsWithin raw frame.definitions) (coherent : Coherent raw)
 (assignment : Assignment) (valid : Models (update frame raw) assignment) :
 All model assignment (block (transform (mapping frame.definitions) raw)) :=
 GeneralPresencePersistentSnapshot250.raw_equations _ _ within coherent model assignment
   ((all_append model assignment _ _).mp valid.2).2

theorem update_attach (frame : Frame) (delta : Delta) (raw : Block) :
 update (attach frame delta) raw = attach (update frame raw) (subst (mapping frame.definitions) delta) :=
 GeneralNominalJournalAppend250.rebase_attach frame delta _

theorem augmented_public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions)
 (delta : Delta) (raw : Block) (shared : Nat → Prop)
 (privateNames : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, Models frame assignment ∧ delta.Holds assignment ∧ Agrees model shared assignment boundary) ↔
 PublicModels (attach (update frame raw) (subst (mapping frame.definitions) delta)) shared boundary := by
 have result := public_models_iff (attach frame delta) safe raw shared privateNames boundary
 rw [update_attach] at result
 simpa only [PublicModels,GeneralNominalJournalAppend250.attach_models,and_assoc] using result
end Yulang.GeneralNominalPersistentOwner250
