import Yulang.GeneralRebaseOwnerTable263

namespace Yulang.GeneralRebaseUniversalBasis263
open GeneralRebaseStep258 GeneralNominalCenters
open GeneralSourceState (Output)

/-- One potential body equation per request. Missing or untranslated bodies
reserve an address but do not thereby write it or become semantically ready. -/
def bodyKey (owner : Nat) (output : Output) : Fact :=
 GeneralRebaseOwnedOutputKeys260.key (GeneralRebaseBodyTable261.address owner output) 0

def ownerFacts (owner : Nat) (pool : List Output) : List Fact :=
 pool.map (bodyKey owner) ++ GeneralRebasePairKeys261.facts owner pool

/-- No representative Plan is needed to construct this finite address space. -/
def basis (owners : List Nat) (pool : List Output) : List Fact :=
 owners.flatMap fun owner => ownerFacts owner pool

theorem body_key_exact (plan : Plan roles) (owner : Nat) (output : Output) (fact : Fact)
 (member : fact ∈ GeneralRebaseBodyTable261.keys plan owner output) : fact = bodyKey owner output := by
 obtain ⟨index,equal⟩ := (GeneralRebaseOwnedOutputKeys260.member _ _ fact).mp member
 have small := GeneralRebaseQuadraticBudget262.schema_bound plan output
 have zero : index.val = 0 := by omega
 simpa only [bodyKey,zero] using equal

theorem table_covered (plan : Plan roles) (owner : Nat) (outputs pool : List Output)
 (covered : ∀ output ∈ outputs, output ∈ pool) :
 GeneralRebaseStableClass261.facts plan owner outputs ⊆ ownerFacts owner pool := by
 intro fact member
 rcases List.mem_append.mp member with body | pair
 · obtain ⟨output,requested,key⟩ := (GeneralRebaseBodyTable261.member ..).mp body
   exact List.mem_append_left _ (List.mem_map.mpr ⟨output,covered output requested,(body_key_exact plan owner output fact key).symm⟩)
 · exact List.mem_append_right _ (GeneralRebasePairKeys261.monotone owner outputs pool covered fact pair)

theorem proposal_covered (owners : List Nat) (pool : List Output) (plan : Plan roles) (owner : Nat)
 (listed : owner ∈ owners) (outputs : List Output) (covered : ∀ output ∈ outputs, output ∈ pool) :
 GeneralRebaseStableClass261.facts plan owner outputs ⊆ basis owners pool := by
 intro fact member
 exact List.mem_flatMap.mpr ⟨owner,listed,table_covered plan owner outputs pool covered member⟩

theorem owner_bound (owner : Nat) (pool : List Output) :
 (ownerFacts owner pool).length ≤ pool.length + pool.length * pool.length := by
 simpa only [ownerFacts,List.length_append,List.length_map] using
   Nat.add_le_add_left (GeneralRebaseQuadraticBudget262.pairs_bound owner pool) pool.length

theorem basis_bound (owners : List Nat) (pool : List Output) :
 (basis owners pool).length ≤ owners.length * (pool.length + pool.length * pool.length) :=
 GeneralRebaseQuadraticBudget262.flatMap_bound owners _ _ (fun owner _ => owner_bound owner pool)

theorem run_bound (owners : List Nat) (pool : List Output) (observe : Observer (basis owners pool))
 {steps before after} (run : GeneralRebaseBudget258.Runs observe steps before after) :
 steps ≤ owners.length * (pool.length + pool.length * pool.length) := by
 have budget := GeneralRebaseBudget258.budget observe run
 have finite := before.canonical.length_le
 have limit := basis_bound owners pool
 omega
end Yulang.GeneralRebaseUniversalBasis263
