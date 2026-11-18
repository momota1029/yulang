import Yulang.GeneralPresenceNormalBlock252
namespace Yulang.GeneralPresenceFiniteBlocks252
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceCheckedNormal252 (Side normalize)

def choices : Side → List (TyTerm Nat) → List (TyTerm Nat)
 | .lower => GeneralPresenceNormalFinite252.lowerCandidates
 | .upper => GeneralPresenceNormalFinite252.upperCandidates

def blocks (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) : List Nat → List (List (Entry Nat))
 | [] => [[]]
 | target :: rest => (choices (side target) (pool target)).flatMap fun term =>
   (blocks side pool rest).map ((target,term) :: ·)

theorem choice_count (side : Side) (pool : List (TyTerm Nat)) : (choices side pool).length = 2 ^ pool.length := by
 cases side
 · exact GeneralPresenceNormalFinite252.lower_count pool
 · exact GeneralPresenceNormalFinite252.upper_count pool

theorem normalized_choice (side : Side) (pool : List (TyTerm Nat)) (term : TyTerm Nat) : normalize side pool term ∈ choices side pool := by
 cases side
 · exact GeneralPresenceNormalFinite252.lower_enumerated pool term
 · exact GeneralPresenceNormalFinite252.upper_enumerated pool term

theorem entries_enumerated (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (source : List (Entry Nat)) :
 GeneralPresenceNormalBlock252.entries side pool source ∈ blocks side pool (source.map Prod.fst) := by
 induction source with
 | nil => exact List.mem_singleton_self _
 | cons first rest ih =>
   exact List.mem_flatMap.mpr ⟨_,normalized_choice _ _ _,List.mem_map.mpr ⟨_,ih,rfl⟩⟩

theorem block_count (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (targets : List Nat) :
 (blocks side pool targets).length = targets.foldr (fun target rest => 2 ^ (pool target).length * rest) 1 := by
 induction targets with
 | nil => rfl
 | cons target rest ih =>
   have copies (terms : List (TyTerm Nat)) :
   (terms.flatMap fun term => (blocks side pool rest).map ((target,term)::·)).length =
   terms.length * (blocks side pool rest).length := by
     induction terms with
     | nil => simp
     | cons first tail ih =>
       simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
       omega
   rw [blocks,copies,choice_count,ih]
   rfl

theorem persistent_enumerated (side : Nat → Side) (pool : Nat → List (TyTerm Nat)) (old raw : List (Entry Nat)) :
 GeneralPresenceNormalBlock252.refreshed side pool old raw ∈ blocks side pool (old.map Prod.fst) := by
 have known := entries_enumerated side pool (GeneralPresencePersistentSnapshot250.refresh old raw)
 rw [GeneralPresencePersistentSnapshot250.target_list] at known
 exact known

theorem duplication_reset (n : Nat) :
 GeneralPresenceNormalBlock252.refreshed (fun _ => .lower) (fun _ => [.var 0])
   (GeneralPresenceSnapshotGrowth251.definitions n) GeneralPresenceSnapshotGrowth251.raw =
 GeneralPresenceSnapshotGrowth251.definitions 0 := by
 unfold GeneralPresenceNormalBlock252.refreshed
 rw [GeneralPresenceSnapshotGrowth251.refresh]
 change [(2,GeneralPresenceUnionNormal252.normalize [.var 0] (GeneralPresenceSnapshotGrowth251.tree (n+1)))] = [(2,.var 0)]
 rw [GeneralPresenceNormalFinite252.duplicated_tree_fixed]
end Yulang.GeneralPresenceFiniteBlocks252
