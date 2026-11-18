import Yulang.GeneralNominalStableSlots250
import Yulang.GeneralPresenceGuardedAllocation247
/-! A fresh materialized owner seed is computed once from full typed support
and the explicitly listed public names. It is not asserted equal to a legacy
source seed. Reusing the returned seed avoids version allocation on refresh. -/
namespace Yulang.GeneralNominalOwnerOpening250
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFrameReservation250 (pool extend Fresh)
open GeneralNominalStableSlots250 (slots)
open GeneralPresenceOrderedBlock247
open GeneralPresenceGuardedAllocation247 (maximum member_le_maximum)

structure Handle where
 seed : Nat
 root : Nat
 declaration : Nat
 names : List Nat

def Handle.slots (handle : Handle) : List Nat := GeneralNominalStableSlots250.slots handle.seed handle.root handle.declaration handle.names

def choose (frame : Frame) (root declaration : Nat) (names shared : List Nat) : Handle :=
 ⟨maximum (pool frame ++ shared),root,declaration,names⟩

def openFrame (frame : Frame) (handle : Handle) : Frame := extend frame handle.slots

theorem fresh (frame : Frame) (root declaration : Nat) (names shared : List Nat) :
 Fresh frame (choose frame root declaration names shared).slots := by
 intro name member inside
 have above := GeneralNominalStableSlots250.slots_above _ _ _ _ name member
 have below := member_le_maximum (pool frame ++ shared) name (List.mem_append_left _ inside)
 exact Nat.not_le_of_gt above below

theorem private_names (frame : Frame) (root declaration : Nat) (names shared : List Nat)
 (name : Nat) (member : name ∈ (choose frame root declaration names shared).slots) : name ∉ shared := by
 intro inside
 have above := GeneralNominalStableSlots250.slots_above _ _ _ _ name member
 have below := member_le_maximum (pool frame ++ shared) name (List.mem_append_right _ inside)
 exact Nat.not_le_of_gt above below

theorem open_safe (frame : Frame) (safe : SafeOrder frame.definitions) (root declaration : Nat) (names shared : List Nat) :
 SafeOrder (openFrame frame (choose frame root declaration names shared)).definitions :=
 GeneralNominalFrameReservation250.safe_extend frame safe _ (fresh frame root declaration names shared)

theorem open_public_models_iff (frame : Frame) (root declaration : Nat) (names shared : List Nat)
 (boundary : Assignment) :
 PublicModels frame (fun name => name ∈ shared) boundary ↔
 PublicModels (openFrame frame (choose frame root declaration names shared)) (fun name => name ∈ shared) boundary :=
 GeneralNominalFrameReservation250.public_models_iff frame _ (fresh frame root declaration names shared)
   (fun name => name ∈ shared) (private_names frame root declaration names shared) boundary
end Yulang.GeneralNominalOwnerOpening250
