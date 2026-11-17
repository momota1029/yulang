import Yulang.GeneralPresenceOrderedCoherentAdapter247
import Yulang.GeneralPresenceOrderedSyntax247
/-! Stable-target refresh reads right-hand sides in the OLD snapshot. This is
not a solution of arbitrary simultaneous cyclic equations in the new state. -/
namespace Yulang.GeneralPresenceSnapshotBlock250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedDedup247
open GeneralPresenceOrderedSyntax247 GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

def refresh (old raw : List (Entry Name)) : List (Entry Name) :=
 dedup (transform (mapping old) raw)

theorem transformed_within (old raw : List (Entry Name)) (within : TargetsWithin raw old) :
 TargetsWithin (transform (mapping old) raw) old := by
 intro entry member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact within original present

theorem refresh_within (old raw : List (Entry Name)) (within : TargetsWithin raw old) :
 TargetsWithin (refresh old raw) old :=
 fun entry member => transformed_within old raw within entry (dedup_subset _ member)

theorem transformed_closed (old raw : List (Entry Name)) (safe : SafeOrder old) :
 ∀ entry ∈ transform (mapping old) raw, ∀ name ∈ typedReads entry.2,
 ∀ original ∈ old, original.1 ≠ name := by
 intro entry member name read original present
 obtain ⟨rhs,_,rfl⟩ := List.mem_map.mp member
 rw [typed_subst] at read
 obtain ⟨source,_,read⟩ := List.mem_flatMap.mp read
 exact mapping_closed old safe source name read original present

theorem refresh_safe (old raw : List (Entry Name)) (safe : SafeOrder old)
 (within : TargetsWithin raw old) : SafeOrder (refresh old raw) := by
 let transformed := transform (mapping old) raw
 let pool := transformed.flatMap (fun entry => typedReads entry.2)
 apply GeneralPresenceOrderedDedup247.safe_pool transformed pool
 · intro target member read
   obtain ⟨rhs,present,used⟩ := List.mem_flatMap.mp read
   obtain ⟨original,found,equal⟩ := transformed_within old raw within target member
   exact transformed_closed old raw safe rhs present target.1 used original found equal
 · intro rhs present name read
   exact List.mem_flatMap.mpr ⟨rhs,present,read⟩

theorem transformed_coherent (old raw : List (Entry Name)) (coherent : Coherent raw) :
 Coherent (transform (mapping old) raw) := by
 intro first one last two equal
 obtain ⟨a,am,rfl⟩ := List.mem_map.mp one
 obtain ⟨b,bm,rfl⟩ := List.mem_map.mp two
 exact congrArg (fun term : TyTerm Name => term.subst (mapping old)) (coherent a am b bm equal)

theorem refresh_models (old raw : List (Entry Name)) (coherent : Coherent raw)
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (block (refresh old raw)) ↔
 All model assignment (block (transform (mapping old) raw)) :=
 block_all_iff model assignment _ (transformed_coherent old raw coherent)

theorem rhs_snapshot (old : List (Entry Name)) (term : TyTerm Name)
 (model : Model) (assignment : Name → Comp model) :
 (term.subst (mapping old)).eval model assignment = term.eval model (solve model old assignment) := by
 rw [TyTerm.eval_subst]
 exact congrArg (term.eval model) (funext (mapping_eval old model assignment))
end Yulang.GeneralPresenceSnapshotBlock250
