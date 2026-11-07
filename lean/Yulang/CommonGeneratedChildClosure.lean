import Yulang.PresenceGeneratedChildGrammar
import Yulang.CommonGeneratedRigidDescent

/-!
# Recursive generated grammar under rigid inspection and variable propagation

The stronger generated grammar is transported through the actual collector,
variable-bound propagation and symbolic child inspection. Reversed arrow
children remain admissible because both original children belong to the
recursive upper grammar, which is included in the lower grammar.

This closes the ordinary child-edge grammar over the original finite node
set. It does not solve symbolic profile constraints or supply a global fixed
point for interleaved propagation, and is not an all-parameter inference
soundness theorem.
-/

namespace Yulang.CommonGeneratedChildClosure

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (splitAtoms compile)
open CommonPresenceVariableBounds (template classify)
open PresenceGeneratedChildGrammar (lower upper GoodAtoms)
open CommonSymbolicConstraints (Check Branch)
open CommonGeneratedRigidInspection (inspect inspectSource inspectSlot saturate)

variable {m : Nat}

def EndpointGrammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) : Prop :=
  ∀ edge ∈ edges, lower (pool.termAt edge.1) = true ∧ upper (pool.termAt edge.2) = true

theorem endpoint_head_shapes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (grammar : EndpointGrammar pool edges) : CommonGeneratedRigidPool.EndpointShapes pool edges := by
  intro edge member
  exact ⟨PresenceGeneratedChildGrammar.lower_head _ (grammar edge member).1,
    PresenceGeneratedChildGrammar.upper_head _ (grammar edge member).2⟩

theorem EndpointGrammar.append {pool : Pool m} {first last : List (Fin pool.size × Fin pool.size)}
    (left : EndpointGrammar pool first) (right : EndpointGrammar pool last) :
    EndpointGrammar pool (first ++ last) := by
  intro edge member
  exact (List.mem_append.mp member).elim (left edge) (right edge)

theorem compiled_endpoint_grammar (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    EndpointGrammar (splitAtoms atoms).pool (compile atoms).edges := by
  intro edge member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  have shape := good (.tyLe original.val.1 original.val.2)
    ((CommonGeneratedRigidPool.split_type_member atoms original.val.1 original.val.2).mp original.property)
  simpa only [Pool.termAt_reference, PresenceGeneratedChildGrammar.GoodAtom] using shape

def ConstraintGrammar (pool : Pool m) : LayerBoundTemplates.Constraint m (Fin pool.size) → Prop
  | .lower bound _ => lower (pool.termAt bound) = true
  | .flow _ _ => True
  | .upper _ bound => upper (pool.termAt bound) = true
  | .check first last => lower (pool.termAt first) = true ∧ upper (pool.termAt last) = true

theorem template_grammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (shapes : EndpointGrammar pool edges) (constraint : LayerBoundTemplates.Constraint m (Fin pool.size))
    (member : constraint ∈ template pool edges) : ConstraintGrammar pool constraint := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
  have shape := shapes edge included
  cases first : CommonPresenceVariableBounds.inputAt pool edge.1 <;>
    cases last : CommonPresenceVariableBounds.inputAt pool edge.2 <;>
    simp_all [classify, ConstraintGrammar]

theorem residual_endpoint_grammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (shapes : EndpointGrammar pool edges) :
    EndpointGrammar pool (CommonBoundCoalescing.rigidComparisons (template pool edges)) := by
  intro comparison member
  obtain ⟨constraint, originalMember, contributed⟩ := List.mem_flatMap.mp member
  have shape := template_grammar pool edges shapes constraint originalMember
  cases constraint with
  | lower | flow => cases contributed
  | upper source bound =>
      obtain ⟨lowerBound, lowerMember, rfl⟩ := List.mem_map.mp contributed
      obtain ⟨start, seed, _⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds (template pool edges) source lowerBound).mp lowerMember
      exact ⟨template_grammar pool edges shapes (.lower lowerBound start) seed, shape⟩
  | check first last =>
      have same : comparison = (first, last) := List.mem_singleton.mp contributed
      subst comparison
      exact shape

/-- Every actual generated residual edge has the recursive endpoint
syntax invariant, with no restriction on semantic slot assignments. -/
theorem generated_residual_endpoint_grammar (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)) :=
  residual_endpoint_grammar _ _ (compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member))

theorem generated_core_residual_endpoint_grammar (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)) :=
  residual_endpoint_grammar _ _ (compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member))

/-- The source and target polarities of ordinary child comparisons, and
the recursively admissible target of a record profile comparison. -/
def CheckGrammar (pool : Pool m) :
    Check (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) → Prop
  | .childBelow (.ref first) (.ref last) =>
      lower (pool.termAt first) = true ∧ upper (pool.termAt last) = true
  | .childBelow _ _ => False
  | .profileBelow _ (.ref payload) => upper (pool.termAt payload) = true
  | .profileBelow _ _ => False
  | .rowBelow _ _ | .flag _ => True

theorem inspect_preserves_grammar (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (sourceGrammar : lower source = true) (targetGrammar : upper target = true) :
    ∀ check ∈ inspect pool source target sourceMember targetMember, CheckGrammar pool check := by
  cases source <;> cases target
  all_goals simp_all [lower, upper, inspect, inspectSource,
    CommonSymbolicRigidInspection.inspect, CommonSymbolicRigidInspection.unionLeft,
    CheckGrammar, Pool.child, Pool.input]
  all_goals first
    | exact ⟨PresenceGeneratedChildGrammar.upper_lower _ sourceGrammar.1,
        PresenceGeneratedChildGrammar.upper_lower _ sourceGrammar.2⟩
    | exact ⟨PresenceGeneratedChildGrammar.upper_lower _ targetGrammar.1,
        PresenceGeneratedChildGrammar.upper_lower _ sourceGrammar.2⟩

theorem inspectSlot_preserves_grammar (pool : Pool m) (edge : Fin pool.size × Fin pool.size)
    (sourceGrammar : lower (pool.termAt edge.1) = true)
    (targetGrammar : upper (pool.termAt edge.2) = true) :
    ∀ check ∈ inspectSlot pool edge, CheckGrammar pool check :=
  inspect_preserves_grammar pool _ _ _ _ sourceGrammar targetGrammar

/-- Static discharge preserves the recursive grammar on every returned
branch, including the negative input comparison emitted by arrows. -/
theorem saturate_preserves_grammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (grammar : EndpointGrammar pool edges) (branch : CommonGeneratedRigidInspection.Checks pool)
    (returned : branch ∈ saturate pool edges) : ∀ check ∈ branch, CheckGrammar pool check := by
  intro check present
  have original := CommonGeneratedRigidDescent.discharge_subset _ branch returned check present
  obtain ⟨edge, member, emitted⟩ := List.mem_flatMap.mp original
  exact inspectSlot_preserves_grammar pool edge (grammar edge member).1 (grammar edge member).2
    check emitted

/-- Extract only ordinary edges, without interpreting or discarding the
independent row, Boolean and profile constraints in the same branch. -/
def childEdges (checks : CommonGeneratedRigidInspection.Checks pool) :
    List (Fin pool.size × Fin pool.size) :=
  checks.flatMap fun
    | .childBelow (.ref first) (.ref last) => [(first, last)]
    | _ => []

theorem childEdges_preserves_grammar (pool : Pool m)
    (checks : CommonGeneratedRigidInspection.Checks pool)
    (grammar : ∀ check ∈ checks, CheckGrammar pool check) : EndpointGrammar pool (childEdges checks) := by
  intro edge member
  obtain ⟨check, included, contributed⟩ := List.mem_flatMap.mp member
  have checked := grammar check included
  cases check with
  | childBelow first last =>
      cases first with
      | ref first =>
          cases last with
          | ref last =>
              have same := List.mem_singleton.mp contributed
              subst edge
              exact checked
          | _ => cases checked
      | _ => cases checked
  | rowBelow | flag | profileBelow => cases contributed

/-- Retaining the original edges while adding every emitted ordinary child
edge preserves the invariant needed by the next inspection pass. -/
theorem accumulate_preserves_grammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (grammar : EndpointGrammar pool edges) (branch : CommonGeneratedRigidInspection.Checks pool)
    (returned : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons (template pool edges))) :
    EndpointGrammar pool (edges ++ childEdges branch) :=
  grammar.append (childEdges_preserves_grammar pool branch
    (saturate_preserves_grammar pool _ (residual_endpoint_grammar pool edges grammar) branch returned))

/-- Ordinary child inspection and another variable-bound propagation round
preserve the same grammar, with no caller-supplied support premise. -/
theorem generated_reinspection_grammar (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : CommonGeneratedRigidInspection.Checks (splitAtoms clause.pack).pool)
    (returned : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges))) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (childEdges branch))) :=
  residual_endpoint_grammar _ _ (childEdges_preserves_grammar _ branch
    (saturate_preserves_grammar _ _ (generated_residual_endpoint_grammar expression clause member)
      branch returned))

theorem generated_core_reinspection_grammar (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : CommonGeneratedRigidInspection.Checks (splitAtoms clause.pack).pool)
    (returned : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges))) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (childEdges branch))) :=
  residual_endpoint_grammar _ _ (childEdges_preserves_grammar _ branch
    (saturate_preserves_grammar _ _ (generated_core_residual_endpoint_grammar expression clause member)
      branch returned))

end Yulang.CommonGeneratedChildClosure
