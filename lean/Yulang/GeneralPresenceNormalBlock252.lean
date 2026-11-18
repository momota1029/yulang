import Yulang.GeneralPresenceCheckedNormal252
namespace Yulang.GeneralPresenceNormalBlock252
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceCheckedNormal252 (Side atoms normalize)
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def entries (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat)) : List (Entry Nat) :=
 source.map fun entry => (entry.1,normalize (side entry.1) (pool entry.1) entry.2)

def Supported (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat)) : Prop :=
 ∀ entry ∈ source, atoms (side entry.1) entry.2 ⊆ pool entry.1

theorem reads_subset (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 typedReads (normalize side pool term) ⊆ typedReads term := by
 cases side
 · exact GeneralPresenceUnionNormal252.normalized_reads pool term
 · exact GeneralPresenceInterNormal252.normalized_reads pool term

theorem safe (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat))
 (valid : SafeOrder source) : SafeOrder (entries side pool source) := by
 induction source with
 | nil => trivial
 | cons head tail ih =>
   refine ⟨fun member => valid.1 (reads_subset _ _ _ member),?_,?_,ih valid.2.2.2⟩
   · intro later member
     obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
     exact valid.2.1 original present
   · intro later member reads
     obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
     exact valid.2.2.1 original present (reads_subset _ _ _ reads)

theorem normalized_equivalent (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat)
 (supported : atoms side term ⊆ pool) (assignment : Assignment) :
 Equivalent ((normalize side pool term).eval model assignment) (term.eval model assignment) := by
 cases side
 · exact GeneralPresenceUnionNormal252.equivalent pool term supported assignment
 · exact GeneralPresenceInterNormal252.equivalent pool term supported assignment

theorem equations_iff (side : Side) (pool : List (TyTerm Nat)) (target : Nat) (term : TyTerm Nat)
 (supported : atoms side term ⊆ pool) (assignment : Assignment) :
 All model assignment (equations target (normalize side pool term)) ↔ All model assignment (equations target term) :=
 (GeneralNominalCaptureMerges.equations_exact ..).trans
   ((GeneralNominalRawCongruence238.equiv_iff ⟨subtype_refl _,subtype_refl _⟩
     (normalized_equivalent side pool term supported assignment)).trans
     (GeneralNominalCaptureMerges.equations_exact ..).symm)

theorem block_iff (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat))
 (supported : Supported side pool source) (assignment : Assignment) :
 All model assignment (block (entries side pool source)) ↔ All model assignment (block source) := by
 induction source with
 | nil => exact Iff.rfl
 | cons head tail ih =>
   simp only [entries,List.map_cons,block,List.flatMap_cons,all_append]
   exact and_congr (equations_iff _ _ _ _ (supported head (by simp)) assignment)
     (ih (fun entry member => supported entry (by simp [member])))

theorem targets (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat)) :
 (entries side pool source).map Prod.fst = source.map Prod.fst := by simp [entries,List.map_map]

def frame (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (original : Frame) : Frame :=
 { original with definitions := entries side pool original.definitions }

theorem frame_models_iff (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (original : Frame)
 (supported : Supported side pool original.definitions) (assignment : Assignment) :
 Models (frame side pool original) assignment ↔ Models original assignment := by
 unfold Models frame
 simp only [all_append]
 exact and_congr Iff.rfl (and_congr Iff.rfl (block_iff side pool original.definitions supported assignment))

def refreshed (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (old raw : List (Entry Nat)) : List (Entry Nat) :=
 entries side pool (GeneralPresencePersistentSnapshot250.refresh old raw)

theorem refreshed_safe (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (old raw : List (Entry Nat))
 (valid : SafeOrder old) : SafeOrder (refreshed side pool old raw) :=
 safe side pool _ (GeneralPresencePersistentSnapshot250.refresh_safe old raw valid)

theorem refreshed_targets (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (old raw : List (Entry Nat)) :
 (refreshed side pool old raw).map Prod.fst = old.map Prod.fst := by
 rw [refreshed,targets,GeneralPresencePersistentSnapshot250.target_list]
end Yulang.GeneralPresenceNormalBlock252
