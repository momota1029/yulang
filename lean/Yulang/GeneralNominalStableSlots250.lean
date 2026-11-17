import Yulang.GeneralNominalFrameReservation250
import Yulang.GeneralNominalRebaseNames241
import Yulang.GeneralNominalSnapshotMerge250
/-! Reserve both concrete stable lo/hi keys for every input name once. This
covers singleton-to-many changes without creating a version key. Initial
metadata freshness is explicit; it is not inferred from ownership alone. -/
namespace Yulang.GeneralNominalStableSlots250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalAllocation (Bindings)
open GeneralNominalRebaseDefinitions241 (entries slot)
open GeneralNominalRebaseNames241 (cell domain)
open GeneralNominalFrameReservation250 (extend Fresh)
open CommonNominalFullCarrier

def slots (seed root declaration : Nat) (names : List Nat) : List Nat := domain seed [(root,declaration)] names

theorem slot_member (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (name : Nat) (named : name ∈ names) (purpose : Nat) (side : purpose = 0 ∨ purpose = 1) :
 slot seed root declaration purpose name bindings ∈ slots seed root declaration names := by
 rcases side with rfl | rfl
 · exact GeneralNominalRebaseNames241.mem_universe (owners := [(root,declaration)]) (owner := (root,declaration)) (upper := false) (List.mem_cons_self) named
 · exact GeneralNominalRebaseNames241.mem_universe (owners := [(root,declaration)]) (owner := (root,declaration)) (upper := true) (List.mem_cons_self) named

theorem slots_above (seed root declaration : Nat) (names : List Nat)
 (name : Nat) (member : name ∈ slots seed root declaration names) : seed < name := by
 obtain ⟨owner,ownerMember,member⟩ := List.mem_flatMap.mp member
 obtain ⟨input,_,member⟩ := List.mem_flatMap.mp member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl <;> exact GeneralNominalRebaseNames241.above _ _ _ _

theorem slot_count (seed root declaration : Nat) (names : List Nat) :
 (slots seed root declaration names).length = names.length * 2 := by
 simpa [slots] using GeneralNominalRebaseNames241.universe_length seed [(root,declaration)] names

theorem entries_covered (frame : Frame) (seed root declaration : Nat) (names : List Nat) (bindings : Bindings) :
 TargetsWithin (entries seed root declaration bindings names)
   (extend frame (slots seed root declaration names)).definitions := by
 intro entry member
 obtain ⟨name,named,_,rfl | rfl⟩ := (GeneralNominalRebaseDefinitions241.member_iff seed root declaration bindings names).mp member
 all_goals refine ⟨(_,TyTerm.bottom),List.mem_append_right _ ?_,rfl⟩
 · exact (GeneralPresenceReserveBlock250.member_iff _ _).mpr
     ⟨slot_member seed root declaration bindings names name named 0 (Or.inl rfl),rfl⟩
 · exact (GeneralPresenceReserveBlock250.member_iff _ _).mpr
     ⟨slot_member seed root declaration bindings names name named 1 (Or.inr rfl),rfl⟩

def install (frame : Frame) (seed root declaration : Nat) (names : List Nat) (bindings : Bindings) : Frame :=
 GeneralNominalPersistentOwner250.update (extend frame (slots seed root declaration names))
   (entries seed root declaration bindings names)

theorem actual_equations (frame : Frame) (seed root declaration : Nat) (names : List Nat)
 (bindings : Bindings) (assignment : Assignment)
 (valid : Models (install frame seed root declaration names bindings) assignment) :
 All model assignment (block (transform
   (GeneralPresenceOrderedSubstitution247.mapping (extend frame (slots seed root declaration names)).definitions)
   (entries seed root declaration bindings names))) :=
 GeneralNominalPersistentOwner250.raw_constraints _ _ (entries_covered frame seed root declaration names bindings)
   (GeneralNominalRebaseDefinitions241.coherent seed root declaration bindings names) assignment valid

theorem install_safe (frame : Frame) (safe : SafeOrder frame.definitions)
 (seed root declaration : Nat) (names : List Nat) (bindings : Bindings)
 (fresh : Fresh frame (slots seed root declaration names)) :
 SafeOrder (install frame seed root declaration names bindings).definitions :=
 GeneralNominalPersistentOwner250.safe_update _
   (GeneralNominalFrameReservation250.safe_extend frame safe _ fresh) _

theorem install_public_models_iff (frame : Frame) (safe : SafeOrder frame.definitions)
 (seed root declaration : Nat) (names : List Nat) (bindings : Bindings)
 (fresh : Fresh frame (slots seed root declaration names)) (shared : Nat → Prop)
 (publicBelow : ∀ name, shared name → name ≤ seed)
 (oldPrivate : ∀ name, shared name → ∀ entry ∈ frame.definitions, entry.1 ≠ name)
 (boundary : Assignment) :
 PublicModels frame shared boundary ↔ PublicModels (install frame seed root declaration names bindings) shared boundary := by
 have privateSlots : ∀ name ∈ slots seed root declaration names, ¬ shared name := by
   intro name member sharedName
   exact Nat.not_le_of_gt (slots_above seed root declaration names name member) (publicBelow name sharedName)
 apply (GeneralNominalFrameReservation250.public_models_iff frame _ fresh shared privateSlots boundary).trans
 apply GeneralNominalPersistentOwner250.public_models_iff _
   (GeneralNominalFrameReservation250.safe_extend frame safe _ fresh) _ shared _ boundary
 intro name sharedName entry member
 rcases List.mem_append.mp member with member | member
 · exact oldPrivate name sharedName entry member
 · intro equal
   exact privateSlots entry.1 ((GeneralPresenceReserveBlock250.member_iff _ _).mp member).1 (equal ▸ sharedName)
end Yulang.GeneralNominalStableSlots250
