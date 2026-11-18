import Yulang.GeneralNominalOwnerExecution250
/-! Owner handles are allocated once and reused by their stable pair key.
A conflicting name list is a preparation mismatch, never a language error.
Registered tracks actual target coverage, not public privacy or reachability. -/
namespace Yulang.GeneralNominalOwnerRegistry250
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalOwnerOpening250 (Handle choose openFrame)
open GeneralPresenceDefinitionRewrite244
open GeneralNominalInstallCoverage250 (within_equal_targets)
open GeneralPresenceOrderedDependence247 (TargetsWithin)

def lookup (handles : List Handle) (root declaration : Nat) : Option Handle :=
 handles.find? (fun handle => handle.root == root && handle.declaration == declaration)

def register (frame : Frame) (handles : List Handle) (root declaration : Nat) (names shared : List Nat) :
 Option (Frame × Handle × List Handle) :=
 match lookup handles root declaration with
 | some handle => if handle.names = names then some (frame,handle,handles) else none
 | none => let handle := choose frame root declaration names shared
           some (openFrame frame handle,handle,handle :: handles)

def Registered (frame : Frame) (handles : List Handle) : Prop :=
 ∀ handle ∈ handles, ∀ name ∈ handle.slots, ∃ entry ∈ frame.definitions, entry.1 = name

theorem lookup_head (handle : Handle) (handles : List Handle) :
 lookup (handle :: handles) handle.root handle.declaration = some handle := by
 simp [lookup]

theorem existing (frame : Frame) (handles : List Handle) (root declaration : Nat) (names shared : List Nat)
 (handle : Handle) (found : lookup handles root declaration = some handle) (same : handle.names = names) :
 register frame handles root declaration names shared = some (frame,handle,handles) := by
 simp [register,found,same]

theorem new_owner (frame : Frame) (handles : List Handle) (root declaration : Nat) (names shared : List Nat)
 (absent : lookup handles root declaration = none) :
 register frame handles root declaration names shared =
 some (openFrame frame (choose frame root declaration names shared),choose frame root declaration names shared,
   choose frame root declaration names shared :: handles) := by
 simp [register,absent]

theorem no_reseed (frame : Frame) (handles : List Handle) (root declaration : Nat) (names shared laterShared : List Nat)
 (result : Frame × Handle × List Handle)
 (success : register frame handles root declaration names shared = some result) :
 register result.1 result.2.2 root declaration names laterShared = some result := by
 unfold register at success
 cases found : lookup handles root declaration with
 | none =>
   simp only [found] at success
   have equal := Option.some.inj success
   subst result
   have head : lookup (choose frame root declaration names shared :: handles) root declaration =
     some (choose frame root declaration names shared) := lookup_head _ _
   exact existing (openFrame frame (choose frame root declaration names shared))
     (choose frame root declaration names shared :: handles) root declaration names laterShared
     (choose frame root declaration names shared) head rfl
 | some handle =>
   simp only [found] at success
   split at success
   · rename_i same
     have equal := Option.some.inj success
     subst result
     exact existing frame handles root declaration names laterShared handle found same
   · simp at success

theorem new_registered (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (handle : Handle) : Registered (openFrame frame handle) (handle :: handles) := by
 intro chosen member name named
 rcases List.mem_cons.mp member with rfl | member
 · refine ⟨(name,Core.PresenceGeneration.TyTerm.bottom),List.mem_append_right _ ?_,rfl⟩
   exact (GeneralPresenceReserveBlock250.member_iff chosen.slots _).mpr ⟨named,rfl⟩
 · obtain ⟨entry,present,equal⟩ := registered chosen member name named
   exact ⟨entry,List.mem_append_left _ present,equal⟩

theorem register_registered (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (root declaration : Nat) (names shared : List Nat) (result : Frame × Handle × List Handle)
 (success : register frame handles root declaration names shared = some result) : Registered result.1 result.2.2 := by
 unfold register at success
 cases found : lookup handles root declaration with
 | none =>
   simp only [found] at success
   have equal := Option.some.inj success
   subst result
   exact new_registered frame handles registered _
 | some handle =>
   simp only [found] at success
   split at success
   · have equal := Option.some.inj success
     subst result
     exact registered
   · simp at success

theorem equal_targets_registered (before after : Frame) (handles : List Handle)
 (equal : after.definitions.map Prod.fst = before.definitions.map Prod.fst) (registered : Registered before handles) :
 Registered after handles := by
 intro handle member name named
 obtain ⟨entry,present,equalName⟩ := registered handle member name named
 have found : name ∈ before.definitions.map Prod.fst := List.mem_map.mpr ⟨entry,present,equalName⟩
 rw [← equal] at found
 exact List.mem_map.mp found

theorem trace_registered (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (commands : List GeneralNominalFiniteInstallTrace250.Command) :
 Registered (GeneralNominalFiniteInstallTrace250.run frame commands) handles :=
 equal_targets_registered frame _ handles (GeneralNominalFiniteInstallTrace250.targets_run frame commands) registered

theorem handle_coverage (frame : Frame) (handles : List Handle) (registered : Registered frame handles)
 (handle : Handle) (member : handle ∈ handles) (bindings : GeneralNominalAllocation.Bindings) :
 TargetsWithin (GeneralNominalRebaseDefinitions241.entries handle.seed handle.root handle.declaration bindings handle.names) frame.definitions := by
 intro entry present
 obtain ⟨name,named,_,rfl | rfl⟩ := (GeneralNominalRebaseDefinitions241.member_iff ..).mp present
 · obtain ⟨original,present,equal⟩ := registered handle member _
     (GeneralNominalStableSlots250.slot_member handle.seed handle.root handle.declaration bindings handle.names name named 0 (Or.inl rfl))
   exact ⟨original,present,equal⟩
 · obtain ⟨original,present,equal⟩ := registered handle member _
     (GeneralNominalStableSlots250.slot_member handle.seed handle.root handle.declaration bindings handle.names name named 1 (Or.inr rfl))
   exact ⟨original,present,equal⟩
end Yulang.GeneralNominalOwnerRegistry250
