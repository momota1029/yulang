import Yulang.PresenceGeneratedRigidShape
import Yulang.CommonPresenceVariableBounds

/-!
# Generated endpoint shapes after actual shared-pool bound propagation

The endpoint grammar is transported through the actual atom split, pool
collector, edge classifier and finite variable-bound coalescer. Propagation
can combine the lower endpoint of one source atom with the upper endpoint of
another, but cannot invent a new rigid head. No semantic assignment, solver
success, closed cache or fuel is used in these results.
-/

namespace Yulang.CommonGeneratedRigidPool

open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (splitAtoms compile)
open CommonPresenceVariableBounds (template classify)
open PresenceGeneratedRigidShape (lower upper GoodAtoms)

variable {m : Nat}

theorem split_type_member (atoms : List (Atom (Fin m))) (first last : TyTerm (Fin m)) :
    (first, last) ∈ (splitAtoms atoms).types ↔ .tyLe first last ∈ atoms := by
  induction atoms with
  | nil => simp [splitAtoms]
  | cons atom rest ih =>
      cases atom <;> simp_all [splitAtoms]

def EndpointShapes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) : Prop :=
  ∀ edge ∈ edges, lower (pool.termAt edge.1) = true ∧ upper (pool.termAt edge.2) = true

theorem compiled_endpoint_shapes (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    EndpointShapes (splitAtoms atoms).pool (compile atoms).edges := by
  intro edge member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  have shape := good (.tyLe original.val.1 original.val.2)
    ((split_type_member atoms original.val.1 original.val.2).mp original.property)
  simpa only [Pool.termAt_reference, PresenceGeneratedRigidShape.GoodAtom] using shape

def ConstraintShape (pool : Pool m) : LayerBoundTemplates.Constraint m (Fin pool.size) → Prop
  | .lower bound _ => lower (pool.termAt bound) = true
  | .flow _ _ => True
  | .upper _ bound => upper (pool.termAt bound) = true
  | .check first last => lower (pool.termAt first) = true ∧ upper (pool.termAt last) = true

theorem template_shapes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (shapes : EndpointShapes pool edges) (constraint : LayerBoundTemplates.Constraint m (Fin pool.size))
    (member : constraint ∈ template pool edges) : ConstraintShape pool constraint := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
  have shape := shapes edge included
  cases first : CommonPresenceVariableBounds.inputAt pool edge.1 <;>
    cases last : CommonPresenceVariableBounds.inputAt pool edge.2 <;>
    simp_all [classify, ConstraintShape]

theorem residual_endpoint_shapes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (shapes : EndpointShapes pool edges) :
    EndpointShapes pool (CommonBoundCoalescing.rigidComparisons (template pool edges)) := by
  intro comparison member
  obtain ⟨constraint, originalMember, contributed⟩ := List.mem_flatMap.mp member
  have shape := template_shapes pool edges shapes constraint originalMember
  cases constraint with
  | lower | flow => cases contributed
  | upper source bound =>
      obtain ⟨lowerBound, lowerMember, rfl⟩ := List.mem_map.mp contributed
      obtain ⟨start, seed, _⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds (template pool edges) source lowerBound).mp lowerMember
      exact ⟨template_shapes pool edges shapes (.lower lowerBound start) seed, shape⟩
  | check first last =>
      have same : comparison = (first, last) := List.mem_singleton.mp contributed
      subst comparison
      exact shape

/-- Every residual edge of every actual generated source clause has a lower
endpoint with no intersection under its union heads, and an upper endpoint
whose head is var/base/pair/arrow/required/width-record. Slot values remain
arbitrary common types; this theorem only concerns stored finite syntax. -/
theorem generated_residual_endpoint_shapes (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointShapes (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)) :=
  residual_endpoint_shapes _ _ (compiled_endpoint_shapes clause.pack
    (PresenceGeneratedRigidShape.generated_endpoint_shapes expression clause member))

theorem generated_core_residual_endpoint_shapes (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointShapes (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)) :=
  residual_endpoint_shapes _ _ (compiled_endpoint_shapes clause.pack
    (PresenceGeneratedRigidShape.generated_core_endpoint_shapes expression clause member))

end Yulang.CommonGeneratedRigidPool
