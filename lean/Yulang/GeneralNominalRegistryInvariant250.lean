import Yulang.GeneralNominalOwnerRegistry250
/-! Registration preserves finite owner-key uniqueness, frame safety and public
models. Reusing a recorded handle after updates does not reserve new slots.
No bound on the number of distinct source-generated owners is claimed. -/
namespace Yulang.GeneralNominalRegistryInvariant250
open GeneralNominalMaterializedOwnerFrame249 (Frame)
open GeneralNominalMaterializedSequenceModels249 (PublicModels)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOwnerOpening250 (Handle choose openFrame)
open GeneralNominalOwnerRegistry250
open GeneralPresenceOrderedBlock247

def key (handle : Handle) : Nat × Nat := (handle.root,handle.declaration)
def Unique (handles : List Handle) : Prop := (handles.map key).Nodup

theorem lookup_fields (handles : List Handle) (root declaration : Nat) (handle : Handle)
 (found : lookup handles root declaration = some handle) :
 handle.root = root ∧ handle.declaration = declaration ∧ handle ∈ handles := by
 have fields := List.find?_some found
 have member := List.mem_of_find?_eq_some found
 have equal : handle.root = root ∧ handle.declaration = declaration := by simpa using fields
 exact ⟨equal.1,equal.2,member⟩

theorem absent_key (handles : List Handle) (root declaration : Nat)
 (absent : lookup handles root declaration = none) : (root,declaration) ∉ handles.map key := by
 intro member
 obtain ⟨handle,present,equal⟩ := List.mem_map.mp member
 have fields : handle.root = root ∧ handle.declaration = declaration :=
   ⟨congrArg Prod.fst equal,congrArg Prod.snd equal⟩
 have noMatch := List.find?_eq_none.mp absent handle present
 exact noMatch (by simp [fields.1,fields.2])

theorem register_unique (frame : Frame) (handles : List Handle) (unique : Unique handles)
 (root declaration : Nat) (names shared : List Nat) (result : Frame × Handle × List Handle)
 (success : register frame handles root declaration names shared = some result) : Unique result.2.2 := by
 unfold register at success
 cases found : lookup handles root declaration with
 | none =>
   simp only [found] at success
   have equal := Option.some.inj success
   subst result
   exact List.nodup_cons.mpr ⟨absent_key handles root declaration found,unique⟩
 | some handle =>
   simp only [found] at success
   split at success
   · have equal := Option.some.inj success
     subst result
     exact unique
   · simp at success

theorem register_safe (frame : Frame) (safe : SafeOrder frame.definitions) (handles : List Handle)
 (root declaration : Nat) (names shared : List Nat) (result : Frame × Handle × List Handle)
 (success : register frame handles root declaration names shared = some result) : SafeOrder result.1.definitions := by
 unfold register at success
 cases found : lookup handles root declaration with
 | none =>
   simp only [found] at success
   have equal := Option.some.inj success
   subst result
   exact GeneralNominalOwnerOpening250.open_safe frame safe root declaration names shared
 | some handle =>
   simp only [found] at success
   split at success
   · have equal := Option.some.inj success
     subst result
     exact safe
   · simp at success

theorem register_public_models_iff (frame : Frame) (handles : List Handle)
 (root declaration : Nat) (names shared : List Nat) (result : Frame × Handle × List Handle)
 (success : register frame handles root declaration names shared = some result) (boundary : Assignment) :
 PublicModels frame (fun name => name ∈ shared) boundary ↔ PublicModels result.1 (fun name => name ∈ shared) boundary := by
 unfold register at success
 cases found : lookup handles root declaration with
 | none =>
   simp only [found] at success
   have equal := Option.some.inj success
   subst result
   exact GeneralNominalOwnerOpening250.open_public_models_iff frame root declaration names shared boundary
 | some handle =>
   simp only [found] at success
   split at success
   · have equal := Option.some.inj success
     subst result
     exact Iff.rfl
   · simp at success

theorem reuse_after_trace (frame : Frame) (handles : List Handle) (root declaration : Nat) (names shared : List Nat)
 (handle : Handle) (found : lookup handles root declaration = some handle) (same : handle.names = names)
 (commands : List GeneralNominalFiniteInstallTrace250.Command) :
 register (GeneralNominalFiniteInstallTrace250.run frame commands) handles root declaration names shared =
 some (GeneralNominalFiniteInstallTrace250.run frame commands,handle,handles) :=
 existing _ handles root declaration names shared handle found same
end Yulang.GeneralNominalRegistryInvariant250
