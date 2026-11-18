import Yulang.GeneralPresenceSnapshotGrowth251
namespace Yulang.GeneralPresenceDuplicateUnion251
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)
open CommonNominalFullCarrier

def reduce : TyTerm Nat → TyTerm Nat
 | .union first last => if first = last then first else .union first last
 | term => term

theorem equivalent (term : TyTerm Nat) (assignment : GeneralNominalCommonBridge.Assignment) :
 Equivalent ((reduce term).eval model assignment) (term.eval model assignment) := by
 cases term
 case union first last =>
   by_cases same : first = last
   · subst last
     simp only [reduce,ite_true]
     have idem := GeneralPresenceSnapshotGrowth251.union_self (first.eval model assignment)
     exact ⟨idem.2,idem.1⟩
   · simp only [reduce,same,ite_false]
     exact ⟨subtype_refl _,subtype_refl _⟩
 all_goals exact ⟨subtype_refl _,subtype_refl _⟩

theorem reads_subset (term : TyTerm Nat) (name : Nat) (member : name ∈ typedReads (reduce term)) : name ∈ typedReads term := by
 cases term
 case union first last =>
   by_cases same : first = last
   · subst last
     simp only [reduce,ite_true] at member
     exact List.mem_append_left _ member
   · simpa only [reduce,same,ite_false] using member
 all_goals exact member

def entries (source : List (Entry Nat)) : List (Entry Nat) := source.map fun entry => (entry.1,reduce entry.2)

theorem safe (source : List (Entry Nat)) (valid : SafeOrder source) : SafeOrder (entries source) := by
 induction source with
 | nil => trivial
 | cons head tail ih =>
   refine ⟨fun member => valid.1 (reads_subset head.2 head.1 member),?_,?_,ih valid.2.2.2⟩
   · intro later member
     obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
     exact valid.2.1 original present
   · intro later member reads
     obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
     exact valid.2.2.1 original present (reads_subset head.2 original.1 reads)

theorem equations_iff (target : Nat) (term : TyTerm Nat) (assignment : GeneralNominalCommonBridge.Assignment) :
 All model assignment (equations target (reduce term)) ↔ All model assignment (equations target term) :=
 (GeneralNominalCaptureMerges.equations_exact ..).trans
   ((GeneralNominalRawCongruence238.equiv_iff ⟨subtype_refl _,subtype_refl _⟩ (equivalent term assignment)).trans
     (GeneralNominalCaptureMerges.equations_exact ..).symm)

theorem block_iff (source : List (Entry Nat)) (assignment : GeneralNominalCommonBridge.Assignment) :
 All model assignment (block (entries source)) ↔ All model assignment (block source) := by
 induction source with
 | nil => exact Iff.rfl
 | cons head tail ih =>
   simp only [entries,List.map_cons,block,List.flatMap_cons,all_append]
   exact and_congr (equations_iff head.1 head.2 assignment) ih

theorem targets (source : List (Entry Nat)) : (entries source).map Prod.fst = source.map Prod.fst := by
 simp [entries,List.map_map]

def refresh (old raw : List (Entry Nat)) : List (Entry Nat) := entries (GeneralPresencePersistentSnapshot250.refresh old raw)

theorem refresh_safe (old raw : List (Entry Nat)) (valid : SafeOrder old) : SafeOrder (refresh old raw) :=
 safe _ (GeneralPresencePersistentSnapshot250.refresh_safe old raw valid)

theorem duplication_fixed : refresh (GeneralPresenceSnapshotGrowth251.definitions 0) GeneralPresenceSnapshotGrowth251.raw =
 GeneralPresenceSnapshotGrowth251.definitions 0 := rfl
end Yulang.GeneralPresenceDuplicateUnion251
