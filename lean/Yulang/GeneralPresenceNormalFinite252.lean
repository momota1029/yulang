import Yulang.GeneralPresenceUnionNormal252
import Yulang.GeneralPresenceInterNormal252
namespace Yulang.GeneralPresenceNormalFinite252
open Core.PresenceGeneration

def subsets : List α → List (List α)
 | [] => [[]]
 | first :: rest => subsets rest ++ (subsets rest).map (first :: ·)

theorem selected_enumerated (pool : List α) (predicate : α → Bool) : pool.filter predicate ∈ subsets pool := by
 induction pool with
 | nil => simp [subsets]
 | cons first rest ih =>
   cases chosen : predicate first
   · simp only [List.filter_cons,chosen,Bool.false_eq_true,ite_false]
     exact List.mem_append_left _ ih
   · simp only [List.filter_cons,chosen,ite_true]
     exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)

theorem subsets_length (pool : List α) : (subsets pool).length = 2 ^ pool.length := by
 induction pool with
 | nil => rfl
 | cons first rest ih => simp only [subsets,List.length_append,List.length_map,ih,List.length_cons,Nat.pow_succ]; omega

def lowerCandidates (pool : List (TyTerm Nat)) : List (TyTerm Nat) :=
 (subsets pool).map GeneralPresenceUnionNormal252.fold

def upperCandidates (pool : List (TyTerm Nat)) : List (TyTerm Nat) :=
 (subsets pool).map GeneralPresenceInterNormal252.fold

theorem lower_enumerated (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralPresenceUnionNormal252.normalize pool term ∈ lowerCandidates pool :=
 List.mem_map.mpr ⟨_,selected_enumerated pool _,rfl⟩

theorem upper_enumerated (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralPresenceInterNormal252.normalize pool term ∈ upperCandidates pool :=
 List.mem_map.mpr ⟨_,selected_enumerated pool _,rfl⟩

theorem lower_count (pool : List (TyTerm Nat)) : (lowerCandidates pool).length = 2 ^ pool.length := by
 rw [lowerCandidates,List.length_map,subsets_length]

theorem upper_count (pool : List (TyTerm Nat)) : (upperCandidates pool).length = 2 ^ pool.length := by
 rw [upperCandidates,List.length_map,subsets_length]

theorem union_atoms_same (pool : List (TyTerm Nat)) (first last : TyTerm Nat)
 (same : ∀ term, term ∈ GeneralPresenceUnionNormal252.atoms first ↔ term ∈ GeneralPresenceUnionNormal252.atoms last) :
 GeneralPresenceUnionNormal252.normalize pool first = GeneralPresenceUnionNormal252.normalize pool last := by
 unfold GeneralPresenceUnionNormal252.normalize GeneralPresenceUnionNormal252.canonical
 congr 1
 apply List.filter_congr
 intro term _
 simp only [same term]

theorem intersection_atoms_same (pool : List (TyTerm Nat)) (first last : TyTerm Nat)
 (same : ∀ term, term ∈ GeneralPresenceInterNormal252.atoms first ↔ term ∈ GeneralPresenceInterNormal252.atoms last) :
 GeneralPresenceInterNormal252.normalize pool first = GeneralPresenceInterNormal252.normalize pool last := by
 unfold GeneralPresenceInterNormal252.normalize GeneralPresenceInterNormal252.canonical
 congr 1
 apply List.filter_congr
 intro term _
 simp only [same term]

theorem duplicated_tree_atoms (n : Nat) (term : TyTerm Nat) :
 term ∈ GeneralPresenceUnionNormal252.atoms (GeneralPresenceSnapshotGrowth251.tree n) ↔ term = .var 0 := by
 induction n with
 | zero => simp [GeneralPresenceSnapshotGrowth251.tree,GeneralPresenceUnionNormal252.atoms]
 | succ n ih => simp [GeneralPresenceSnapshotGrowth251.tree,GeneralPresenceUnionNormal252.atoms,ih]

theorem duplicated_tree_fixed (n : Nat) :
 GeneralPresenceUnionNormal252.normalize [.var 0] (GeneralPresenceSnapshotGrowth251.tree n) = .var 0 := by
 have same := union_atoms_same [.var 0] (GeneralPresenceSnapshotGrowth251.tree n) (.var 0)
   (fun term => (duplicated_tree_atoms n term).trans (by simp [GeneralPresenceUnionNormal252.atoms]))
 exact same

theorem duplicate_union_fixed (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralPresenceUnionNormal252.normalize pool (.union term term) = GeneralPresenceUnionNormal252.normalize pool term := by
 apply union_atoms_same
 intro atom
 simp [GeneralPresenceUnionNormal252.atoms]

theorem duplicate_inter_fixed (pool : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralPresenceInterNormal252.normalize pool (.inter term term) = GeneralPresenceInterNormal252.normalize pool term := by
 apply intersection_atoms_same
 intro atom
 simp [GeneralPresenceInterNormal252.atoms]
end Yulang.GeneralPresenceNormalFinite252
