import Yulang.GeneralNominalState
import Yulang.GeneralPresenceOrderedSupport247
/-! Explicit support bridge from the actual nominal state functions to the
finite Presence preparation helpers. This changes neither source allocation
nor the source language's accepted programs. -/
namespace Yulang.GeneralNominalOrderedSupport248
open Core.PresenceGeneration

theorem row_sources (term : RowTerm Nat) :
 GeneralNominalState.rowSources term = GeneralPresenceSubstitutionSupport244.rowSources term := by
 induction term <;> simp_all [GeneralNominalState.rowSources,GeneralPresenceSubstitutionSupport244.rowSources]

theorem type_sources (term : TyTerm Nat) :
 GeneralNominalState.typeSources term = GeneralPresenceSubstitutionSupport244.typeSources term := by
 induction term <;> simp_all [GeneralNominalState.typeSources,GeneralPresenceSubstitutionSupport244.typeSources,row_sources]

theorem typed_reads_subset (term : TyTerm Nat) :
 GeneralPresenceUsedSupport245.typedReads term ⊆ GeneralNominalState.typeSources term := by
 intro name member
 rw [type_sources]
 exact (GeneralPresenceUsedSupport245.sources_split term name).mpr (Or.inl member)

theorem safe_actual_pool (entries : List (GeneralPresenceDefinitionRewrite244.Entry Nat))
 (pool : List Nat) (distinct : (entries.map Prod.fst).Nodup)
 (protectedTargets : ∀ target ∈ entries, target.1 ∉ pool)
 (coveredSources : ∀ rhs ∈ entries, ∀ name ∈ GeneralNominalState.typeSources rhs.2, name ∈ pool) :
 GeneralPresenceOrderedBlock247.SafeOrder entries := by
 apply GeneralPresenceOrderedSupport247.safe_pool entries pool distinct protectedTargets
 intro rhs member name read
 exact coveredSources rhs member name (typed_reads_subset rhs.2 read)
end Yulang.GeneralNominalOrderedSupport248
