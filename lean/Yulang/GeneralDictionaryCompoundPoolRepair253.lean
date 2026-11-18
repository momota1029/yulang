import Yulang.GeneralDictionaryCompoundPool253
import Yulang.GeneralNominalPublicPorts253
namespace Yulang.GeneralDictionaryCompoundPoolRepair253
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPool253
open GeneralNominalPublicPorts253

/-- The wider public-port candidate covers the precise reachable endpoint
missed by the named-binder-only pool. No operational definition is replaced. -/
theorem endpoint_in_ports : endpoint ∈ ports snapshot.seed root.identity declaration :=
 (argument_mem snapshot.seed root.identity declaration child (List.mem_singleton_self _) 0 (by decide)).1

theorem endpoint_in_names (keys : List (Nat × Nat))
 (owner : (root.identity,declaration.id) ∈ keys) : endpoint ∈ names registry snapshot.seed keys :=
 port_mem registry snapshot.seed root.identity keys declaration owner (List.mem_singleton_self _) endpoint endpoint_in_ports

theorem repaired_atomic_support (keys : List (Nat × Nat))
 (owner : (root.identity,declaration.id) ∈ keys) :
 GeneralPresenceUnionNormal252.atoms (Core.PresenceGeneration.TyTerm.var endpoint) ⊆
 ((GeneralNominalState.sources snapshot ++ names registry snapshot.seed keys).map Core.PresenceGeneration.TyTerm.var) := by
 intro term member
 cases List.mem_singleton.mp member
 exact List.mem_map.mpr ⟨endpoint,List.mem_append_right _ (endpoint_in_names keys owner),rfl⟩

theorem pool_gap_and_local_repair (keys : List (Nat × Nat))
 (owner : (root.identity,declaration.id) ∈ keys) :
 Core.PresenceGeneration.TyTerm.var endpoint ∉ GeneralDictionaryCompoundPool253.pool keys ∧
 endpoint ∈ names registry snapshot.seed keys :=
 ⟨endpoint_not_pool keys,endpoint_in_names keys owner⟩
end Yulang.GeneralDictionaryCompoundPoolRepair253
