import Yulang.GeneralPresenceOrderedDedup247
import Yulang.GeneralPresenceOrderedRebase247
/-! Adapters retain the original coherent equation list, including repeated
names. Only the internal solver representation is deduplicated. No source
input is rejected for repeating a name. Actual freshness remains a premise. -/
namespace Yulang.GeneralPresenceOrderedCoherentAdapter247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDedup247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRebase247 GeneralPresenceModelCongruence245
open GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

theorem original_satisfied (model : Model) (reflModel : ∀ value, model.subTy value value)
 (entries : List (Entry Name)) (coherent : Coherent entries)
 (safe : SafeOrder (dedup entries)) (assignment : Name → Comp model) :
 All model (solve model (dedup entries) assignment) (block entries) :=
 (block_all_iff model _ entries coherent).mp (block_satisfied model reflModel _ safe assignment)

theorem pool_extension (model : Model) (reflModel : ∀ value, model.subTy value value)
 (entries : List (Entry Name)) (coherent : Coherent entries) (pool : List Name)
 (protectedTargets : ∀ target ∈ entries, target.1 ∉ pool)
 (coveredReads : ∀ rhs ∈ entries, ∀ name ∈ typedReads rhs.2, name ∈ pool)
 (assignment : Name → Comp model) :
 ∃ extended, All model extended (block entries) ∧
   (∀ name ∈ pool, extended name = assignment name) ∧
   (∀ name, (extended name).2 = (assignment name).2) := by
 refine ⟨solve model (dedup entries) assignment,
   original_satisfied model reflModel entries coherent (safe_pool entries pool protectedTargets coveredReads) assignment,?_,
   solve_rows model _ assignment⟩
 intro name member
 apply solve_outside
 intro entry present equal
 exact protectedTargets entry (dedup_subset entries present) (equal ▸ member)

theorem targets_within_dedup (fresh old : List (Entry Name)) (coherent : Coherent old)
 (within : TargetsWithin fresh old) : TargetsWithin (dedup fresh) (dedup old) := by
 intro entry member
 obtain ⟨original,present,equal⟩ := within entry (dedup_subset fresh member)
 exact ⟨original,member_preserved old coherent original present,equal⟩

theorem original_public_models_iff (model : Model) (laws : Laws model)
 (old fresh : List (Entry Name)) (oldCoherent : Coherent old) (freshCoherent : Coherent fresh)
 (oldSafe : SafeOrder (dedup old)) (freshSafe : SafeOrder (dedup fresh))
 (within : TargetsWithin fresh old) (consumers : List (Atom Name))
 (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite (dedup old) consumers ++ block fresh) ∧
   Agrees model sharedNames assignment boundary) := by
 have result := public_models_iff model laws (dedup old) (dedup fresh) oldSafe freshSafe
   (targets_within_dedup fresh old oldCoherent within) consumers sharedNames
   (fun name shared entry member => privateTargets name shared entry (dedup_subset old member)) boundary
 simpa only [all_append,block_all_iff model _ old oldCoherent,block_all_iff model _ fresh freshCoherent] using result
end Yulang.GeneralPresenceOrderedCoherentAdapter247
