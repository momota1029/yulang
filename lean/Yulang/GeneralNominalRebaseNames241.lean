import Yulang.GeneralNominalIdentities
import Yulang.GeneralNominalRebaseStore241
namespace Yulang.GeneralNominalRebaseNames241
open GeneralNominalRebaseStore241 (Owner)
open GeneralNominalIdentities

def key (owner : Owner) (name : Nat) (upper : Bool) : Origin :=
 (owner.1,owner.2,if upper then 1 else 0,name,0)
def cell (seed : Nat) (owner : Owner) (name : Nat) (upper : Bool) : Nat :=
 source seed (key owner name upper)

theorem above (seed owner name upper) : seed < cell seed owner name upper :=
 source_above_seed _ _

theorem owner_injective (same : cell seed first name upper = cell seed last other side) : first = last := by
 have equal := (source_identity seed _ _).mp same
 exact Prod.ext (congrArg (fun origin : Origin => origin.1) equal) (congrArg (fun origin : Origin => origin.2.1) equal)

theorem name_injective (same : cell seed owner first upper = cell seed other last side) : first = last := by
 have equal := (source_identity seed _ _).mp same
 exact congrArg (fun origin : Origin => origin.2.2.2.1) equal

theorem sides_distinct : cell seed owner name false ≠ cell seed owner name true := by
 intro same
 have equal := (source_identity seed _ _).mp same
 have impossible := congrArg (fun origin : Origin => origin.2.2.1) equal
 change (0:Nat)=1 at impossible
 omega

def domain (seed : Nat) (owners : List Owner) (names : List Nat) : List Nat :=
 owners.flatMap fun owner => names.flatMap fun name => [cell seed owner name false,cell seed owner name true]

theorem mem_universe (owner_mem : owner ∈ owners) (name_mem : name ∈ names) :
 cell seed owner name upper ∈ domain seed owners names := by
 apply List.mem_flatMap.mpr
 refine ⟨owner,owner_mem,List.mem_flatMap.mpr ⟨name,name_mem,?_⟩⟩
 cases upper <;> simp

theorem universe_length (seed : Nat) (owners : List Owner) (names : List Nat) :
 (domain seed owners names).length = owners.length * (names.length * 2) := by
 have block (owner : Owner) : (names.flatMap fun name => [cell seed owner name false,cell seed owner name true]).length = names.length * 2 := by
   induction names with
   | nil => simp
   | cons head tail ih =>
     simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
     omega
 induction owners with
 | nil => simp [domain]
 | cons owner rest ih =>
   change ((names.flatMap fun name => [cell seed owner name false,cell seed owner name true]) ++ domain seed rest names).length = _
   rw [List.length_append,block,ih]
   simp [Nat.add_mul,Nat.add_comm]
end Yulang.GeneralNominalRebaseNames241
