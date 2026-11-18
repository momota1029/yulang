import Yulang.GeneralDictionaryAggregateHistory256
import Yulang.GeneralNominalInitialAggregate256
namespace Yulang.GeneralDictionaryAggregateBasis256
open Core.PresenceGeneration
open GeneralDictionaryAggregateHistory256
open GeneralDictionaryReachableAggregate256 (representative)
open GeneralDictionaryLooseLoopSource240 (registry context root roles)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- The two-atom normalization pool is part of the one initial source basis,
not a basis recomputed from an expanding current state. -/
theorem initial_basis (labels : List GeneralDeclarationPatterns.Pattern) :
 pool ⊆ GeneralNominalSourcePublicBasis255.basis registry context root labels := by
 intro term member
 have cases : term = .var 2 ∨ term = .var 4 := by simpa only [pool,List.mem_cons,List.not_mem_nil,or_false] using member
 rcases cases with rfl | rfl
 all_goals
   apply GeneralNominalSourceAggregate256.source_variable
   apply List.mem_append_left
   apply List.mem_append_left
   apply List.mem_append_left
 all_goals first | exact List.mem_ofFn.mpr ⟨(2 : Fin 5),rfl⟩ | exact List.mem_ofFn.mpr ⟨(4 : Fin 5),rfl⟩

theorem pool_unique : pool.Nodup := by decide

theorem pool_private_free (invocation declaration purpose binder position : Nat)
 (atom : TyTerm Nat) (member : atom ∈ pool) :
 GeneralNominalPublicBasis253.privateName 4 invocation declaration purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources atom := by
 have above := GeneralNominalIdentities.source_above_seed 4
   (GeneralNominalAllocation.origin invocation declaration purpose binder position)
 have cases : atom = .var 2 ∨ atom = .var 4 := by simpa only [pool,List.mem_cons,List.not_mem_nil,or_false] using member
 rcases cases with rfl | rfl
 all_goals
   intro occurs
   have equal := List.mem_singleton.mp occurs
   change GeneralNominalIdentities.source 4 (GeneralNominalAllocation.origin invocation declaration purpose binder position) = _ at equal
   omega

theorem prepared_finite (n : Nat) :
 representative.lower ∈ GeneralPresenceNormalFinite252.lowerCandidates pool ∧
 representative.upper ∈ GeneralPresenceNormalFinite252.upperCandidates pool := by
 rw [← rewritten n]
 exact GeneralNominalHistoricalAggregate256.finite ..

/-- Models of the actual source satisfy the projected equation history.
No witness-only model or arbitrary substitution is being substituted here. -/
theorem source_history (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) :
 PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history n)) :=
 fun atom member => GeneralDictionaryReachableAggregate256.current_atoms n assignment valid atom (block_in_source n member)

/-- The checked normalized result has the original source capture meaning
for every model of that source stage. -/
theorem prepared_source_fits (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) (actual : Ty) :
 ∃ result, GeneralNominalHistoricalAggregate256.prepare pool (history n)
   (GeneralNominalFrameAggregate256.pairs (plan n) 0) = some result ∧
 (result.Fits assignment actual ↔ ∀ pair ∈ GeneralNominalFrameAggregate256.pairs (plan n) 0,
   GeneralNominalCaptureMerges.Fits assignment pair actual) :=
 ⟨representative,prepared n,GeneralDictionaryReachableAggregate256.fits_exact n assignment valid actual⟩
end Yulang.GeneralDictionaryAggregateBasis256
