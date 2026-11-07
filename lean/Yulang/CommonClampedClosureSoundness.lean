import Yulang.CommonFiniteChildInspection
import Yulang.CommonOrdinaryEdgeClosure
import Yulang.CommonPresenceClampedBounds

/-!
# Conditional soundness of clamped equations at an ordinary-edge fixed point

This is an internal soundness lemma. It retains explicit row, Boolean and
profile obligations from rigid inspection. The proof uses constructor depth
and source-term weight, not a circular appeal to full subtype exactness for
the same ordinary edge set. It is not yet the unrestricted source family:
the non-child obligations must still be solved by the full symbolic compiler.
-/

namespace Yulang.CommonClampedClosureSoundness

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes EdgesHold rowEval restrict)
open CommonPresenceVariableBounds (template inputAt classify)
open CommonGeneratedChildClosure (EndpointGrammar CheckGrammar)
open CommonGeneratedRigidDescent (weight)
open CommonGeneratedRigidInspection (inspectSlot)
open CommonFiniteChildInspection (BelowAt GuardedAt CheckAt BranchAt sameDepth)
open CommonSymbolicConstraints (Check)

variable {m : Nat}

abbrev RigidEdges (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool) :=
  CommonBoundCoalescing.rigidComparisons (template pool edges)

def NonChildHolds (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    Check (Core.PresenceGeneration.RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) → Prop
  | .childBelow _ _ => True
  | other => other.Holds (rowEval rows) values values

def NonChildChecks (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) : Prop :=
  ∀ check ∈ CommonOrdinaryEdgeClosure.residualChecks pool edges, NonChildHolds pool rows values check

theorem meetTypes_at_iff (depth : Nat) (source : Ty) (types : List Ty) :
    BelowAt depth source (CommonBoundCoalescing.meetTypes types) ↔
      ∀ target ∈ types, BelowAt depth source target := by
  induction types with
  | nil =>
      simp only [List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (CommonBoundCoalescing.le_top source depth)
  | cons target rest ih =>
      change CommonFinite.ProducerLe _ _ (.inter _ _) ↔ _
      rw [CommonFinite.producerLe_inter_iff]
      change (BelowAt depth source target ∧ BelowAt depth source (CommonBoundCoalescing.meetTypes rest)) ↔ _
      simp only [List.mem_cons, forall_eq_or_imp]
      exact and_congr_right (fun _ => ih)

theorem upper_at_iff (depth : Nat) (evaluate : Bound → Ty) (problem : LayerBoundTemplates.Problem n Bound)
    (index : Fin n) (source : Ty) :
    BelowAt depth source (CommonBoundCoalescing.upper evaluate problem index) ↔
      ∀ bound ∈ LayerBoundTemplates.upperBounds problem index, BelowAt depth source (evaluate bound) := by
  simp only [CommonBoundCoalescing.upper, meetTypes_at_iff, List.forall_mem_map]

theorem lower_upper_pair_member (problem : LayerBoundTemplates.Problem n Bound)
    (source upper : Bound) (index : Fin n) (lowerMember : .lower source index ∈ problem)
    (upperMember : upper ∈ LayerBoundTemplates.upperBounds problem index) :
    (source, upper) ∈ CommonBoundCoalescing.rigidComparisons problem := by
  obtain ⟨finish, seed, path⟩ := (PresenceBoundCoalescing.mem_upperBounds problem index upper).mp upperMember
  apply List.mem_flatMap.mpr
  refine ⟨.upper finish upper, seed, ?_⟩
  exact List.mem_map.mpr ⟨source,
    (PresenceBoundCoalescing.mem_lowerBounds problem finish source).mpr ⟨index, lowerMember, path⟩, rfl⟩

private theorem flow_path (problem : LayerBoundTemplates.Problem n Bound)
    (source target : Fin n) (member : .flow source target ∈ problem) :
    LayerBoundTemplates.Reaches problem source target := by
  exact FiniteWorklist.Path.cons (List.mem_filterMap.mpr ⟨.flow source target, member, by simp⟩)
    (FiniteWorklist.Path.nil target)

/-- An edge with a fixed rigid source needs only comparisons with that same
source against its propagated upper targets. The source weight never rises
at this step. Variable sources already satisfy upper and flow constraints. -/
theorem edge_at_of_rigid_source (depth : Nat) (pool : Pool m)
    (edges : CommonOrdinaryEdgeClosure.Edges pool) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (edge : Fin pool.size × Fin pool.size) (member : edge ∈ edges)
    (rigidSource : ∀ target, (edge.1, target) ∈ RigidEdges pool edges →
      BelowAt depth (values edge.1) (values target)) :
    BelowAt depth (values edge.1) (values edge.2) := by
  have classified : classify pool edge ∈ template pool edges := List.mem_map.mpr ⟨edge, member, rfl⟩
  cases first : inputAt pool edge.1 with
  | none =>
      cases last : inputAt pool edge.2 with
      | none =>
          have checked : .check edge.1 edge.2 ∈ template pool edges := by
            simpa only [classify, first, last] using classified
          exact rigidSource edge.2 (List.mem_flatMap.mpr ⟨.check edge.1 edge.2, checked, by simp⟩)
      | some target =>
          have lowerMember : .lower edge.1 target ∈ template pool edges := by
            simpa only [classify, first, last] using classified
          have lowerBelow : Common.Subtype (values edge.1)
              (CommonBoundCoalescing.expand values (template pool edges) parameters target) :=
            Common.subtype_trans (CommonBoundCoalescing.lower_lower values (template pool edges) edge.1 target lowerMember)
              (CommonBoundCoalescing.le_union_left _ _)
          have upperBelow := (upper_at_iff depth values (template pool edges) target (values edge.1)).mpr
            (fun bound included => rigidSource bound
              (lower_upper_pair_member (template pool edges) edge.1 bound target lowerMember included))
          have expanded := ((CommonPresenceClampedBounds.models_exact pool edges rows parameters values).mp model).2 target
          rw [(CommonPresenceVariableBounds.variable_some_iff pool edge.2 target).mp last]
          exact CommonFinite.producerLe_trans
            ((CommonFinite.producerLe_inter_iff _ _ _).mpr ⟨lowerBelow depth, upperBelow⟩) (expanded.1 depth)
  | some source =>
      cases last : inputAt pool edge.2 with
      | none =>
          have upperMember : .upper source edge.2 ∈ template pool edges := by
            simpa only [classify, first, last] using classified
          rw [(CommonPresenceVariableBounds.variable_some_iff pool edge.1 source).mp first]
          exact CommonPresenceClampedBounds.models_below_bound pool edges rows parameters values model source edge.2
            ((PresenceBoundCoalescing.mem_upperBounds (template pool edges) source edge.2).mpr
              ⟨source, upperMember, .nil source⟩) depth
      | some target =>
          have flowMember : .flow source target ∈ template pool edges := by
            simpa only [classify, first, last] using classified
          rw [(CommonPresenceVariableBounds.variable_some_iff pool edge.1 source).mp first,
            (CommonPresenceVariableBounds.variable_some_iff pool edge.2 target).mp last]
          exact CommonPresenceClampedBounds.models_along_path pool edges rows parameters values model
            (flow_path (template pool edges) source target flowMember) depth

theorem closed_child_member (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool)
    (closed : CommonOrdinaryEdgeClosure.Closed pool edges)
    (origin : Fin pool.size × Fin pool.size) (originMember : origin ∈ RigidEdges pool edges)
    (first last : Fin pool.size)
    (present : .childBelow (.ref first) (.ref last) ∈ inspectSlot pool origin) : (first, last) ∈ edges := by
  apply closed
  apply (TypeConstraintGraph.mem_unique _ _).mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨.childBelow (.ref first) (.ref last), ?_, by simp⟩
  exact List.mem_flatMap.mpr ⟨origin, originMember, present⟩

/-- Assuming guarded children at the previous observation, same-depth union
children close by strict source-weight induction. -/
theorem rigid_at_of_guarded (depth : Nat) (pool : Pool m)
    (edges : CommonOrdinaryEdgeClosure.Edges pool) (grammar : EndpointGrammar pool edges)
    (closed : CommonOrdinaryEdgeClosure.Closed pool edges) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (nonChild : NonChildChecks pool edges rows values)
    (guarded : ∀ edge ∈ edges, GuardedAt depth (values edge.1) (values edge.2)) :
    ∀ edge ∈ RigidEdges pool edges, BelowAt depth (values edge.1) (values edge.2) := by
  have realizes := ((CommonPresenceClampedBounds.models_exact pool edges rows parameters values).mp model).1
  have shapes := CommonGeneratedChildClosure.residual_endpoint_grammar pool edges grammar
  have byWeight : ∀ size, ∀ edge ∈ RigidEdges pool edges,
      weight (pool.termAt edge.1) = size → BelowAt depth (values edge.1) (values edge.2) := by
    intro size
    refine Nat.strongRecOn size ?_
    intro current ih edge member measured
    have endpoints := CommonPresenceVariableBounds.residuals_rigid pool edges edge member
    have sourceRigid := CommonGeneratedRigidDescent.rigid_termAt pool edge.1 endpoints.1
    have targetRigid := CommonGeneratedRigidDescent.rigid_termAt pool edge.2 endpoints.2
    apply CommonFiniteChildInspection.inspectSlot_at_sound depth pool edge (shapes edge member).1
      (shapes edge member).2 sourceRigid targetRigid rows values realizes
    intro check included
    have checked := CommonGeneratedChildClosure.inspectSlot_preserves_grammar pool edge
      (shapes edge member).1 (shapes edge member).2 check included
    cases check with
    | childBelow firstPayload lastPayload =>
        cases firstPayload with
        | ref first =>
            cases lastPayload with
            | ref last =>
                have childMember := closed_child_member pool edges closed edge member first last included
                simp only [CheckAt, CommonPayloadProjection.Payload.evalLayer]
                split
                · rename_i same
                  have smaller := CommonFiniteChildInspection.sameDepth_child_decreases pool _ _ _ _
                    (shapes edge member).2 targetRigid same first last included
                  apply edge_at_of_rigid_source depth pool edges rows parameters values model (first, last) childMember
                  intro target compared
                  exact ih (weight (pool.termAt first)) (by omega) (first, target) compared rfl
                · exact guarded (first, last) childMember
            | _ => cases checked
        | _ => cases checked
    | rowBelow | flag | profileBelow =>
        exact nonChild _ (List.mem_flatMap.mpr ⟨edge, member, included⟩)
  intro edge member
  exact byWeight _ edge member rfl

/-- Every finite constructor observation is sound. There is no global child
subtyping premise: the zero case is trivial on guarded references, and each
successor uses only the preceding observation. -/
theorem finite_edges (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool)
    (grammar : EndpointGrammar pool edges) (closed : CommonOrdinaryEdgeClosure.Closed pool edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (nonChild : NonChildChecks pool edges rows values) (depth : Nat) :
    ∀ edge ∈ edges, BelowAt depth (values edge.1) (values edge.2) := by
  induction depth with
  | zero =>
      have rigid := rigid_at_of_guarded 0 pool edges grammar closed rows parameters values model nonChild
        (fun edge _ => CommonFiniteChildInspection.guarded_zero _ _)
      intro edge member
      exact edge_at_of_rigid_source 0 pool edges rows parameters values model edge member
        (fun target compared => rigid (edge.1, target) compared)
  | succ depth ih =>
      have rigid := rigid_at_of_guarded (depth + 1) pool edges grammar closed rows parameters values model nonChild
        (fun edge member => (CommonFiniteChildInspection.guarded_succ depth _ _).mpr (ih edge member))
      intro edge member
      exact edge_at_of_rigid_source (depth + 1) pool edges rows parameters values model edge member
        (fun target compared => rigid (edge.1, target) compared)

/-- Internal conditional soundness. The explicit non-child constraints are
the remaining compiler work; no ordinary edge or full rigid comparison is
assumed to hold. Constructor depth and syntax weight discharge those edges. -/
theorem conditional_soundness (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool)
    (grammar : EndpointGrammar pool edges) (closed : CommonOrdinaryEdgeClosure.Closed pool edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (CommonPresenceClampedBounds.graph pool edges rows parameters) values)
    (nonChild : NonChildChecks pool edges rows values) : EdgesHold edges values := by
  intro edge member depth
  exact finite_edges pool edges grammar closed rows parameters values model nonChild depth edge member

theorem solve_sound_of_nonChild (pool : Pool m) (edges : CommonOrdinaryEdgeClosure.Edges pool)
    (grammar : EndpointGrammar pool edges) (closed : CommonOrdinaryEdgeClosure.Closed pool edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty)
    (nonChild : NonChildChecks pool edges rows
      (CommonPresenceClampedBounds.solve pool edges rows parameters recursiveParameters)) :
    EdgesHold edges (CommonPresenceClampedBounds.solve pool edges rows parameters recursiveParameters) :=
  conditional_soundness pool edges grammar closed rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) nonChild

end Yulang.CommonClampedClosureSoundness
