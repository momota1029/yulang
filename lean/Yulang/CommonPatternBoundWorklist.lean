import Yulang.CommonPatternBoundPolarity
import Yulang.CommonBoundRefWorklist

/-!
# A finite worklist that inspects pattern variant and optional targets

The finite inventory and variable-flow closure are unchanged. Only the actual
inspection computation is extended. Syntax invariants below are internal
provenance conditions, not restrictions on assigned Common values or rows.
-/

namespace Yulang.CommonPatternBoundWorklist

open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPoolQueries (queries)
open CommonBoundRefWorklist (Index Edge Aux Branch State inventory rigid edgeHolds auxHolds EdgesHold)
open CommonBoundRefInspection (LowerRef)
open CommonPatternBoundInspection (UpperRef)

variable {m : Nat}

def inspect (pool : Pool m) (edge : Edge pool) : List (Branch pool) :=
  CommonBoundRefBranches.splitOutput pool (queries pool)
    (CommonPatternBoundInspection.inspect pool edge.1.val edge.2.val)
    (CommonPatternBoundInspection.inspect_supported_refs pool edge.1.val edge.2.val
      edge.1.property edge.2.property)

def run (pool : Pool m) (edges : List (Edge pool)) : List (State pool) :=
  FiniteBranchingWorklist.run (inventory pool) (rigid pool) (inspect pool) edges []

theorem inspection_supported (pool : Pool m) :
    FiniteBranchingWorklist.InspectionSupported (inventory pool) (inspect pool) := by
  intro _ _ _ _ edge _
  exact CommonBoundRefWorklist.inventory_complete pool edge

theorem run_finished (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    FiniteBranchingWorklist.pending (inventory pool) (rigid pool) final = none :=
  FiniteBranchingWorklist.run_finished (inventory pool) (rigid pool) (inspect pool) edges []
    (CommonBoundRefWorklist.edges_supported pool edges) (inspection_supported pool) final returned

theorem run_closed (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    FiniteBranchingWorklist.Closed (rigid pool) (inspect pool) final :=
  FiniteBranchingWorklist.run_closed (inventory pool) (rigid pool) (inspect pool) edges []
    (CommonBoundRefWorklist.edges_supported pool edges) (inspection_supported pool)
    (CommonBoundRefWorklist.rigid_supported pool) final returned

theorem run_bound (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    final.processed.Nodup ∧ final.trace.length = final.processed.length ∧
      final.trace.length ≤ (5 * pool.size + 3) ^ 2 := by
  obtain ⟨distinct, _, _, lengths, bound⟩ :=
    FiniteBranchingWorklist.run_bound (inventory pool) (rigid pool) (inspect pool) edges []
      (CommonBoundRefWorklist.edges_supported pool edges) (inspection_supported pool) final returned
  exact ⟨distinct, lengths, Nat.le_trans bound (CommonBoundRefCoalescing.generated_inventory_bound pool)⟩

def Grammar (pool : Pool m) (edges : List (Edge pool)) : Prop :=
  ∀ edge ∈ edges, LowerRef pool edge.1.val ∧ UpperRef pool edge.2.val

theorem Grammar.append {pool : Pool m} {first last : List (Edge pool)}
    (left : Grammar pool first) (right : Grammar pool last) : Grammar pool (first ++ last) := by
  intro edge member
  exact (List.mem_append.mp member).elim (left edge) (right edge)

def ConstraintGrammar (pool : Pool m) : LayerBoundTemplates.Constraint m (Index pool) → Prop
  | .lower bound _ => LowerRef pool bound.val
  | .flow _ _ => True
  | .upper _ bound => UpperRef pool bound.val
  | .check first last => LowerRef pool first.val ∧ UpperRef pool last.val

theorem template_grammar (pool : Pool m) (edges : List (Edge pool))
    (grammar : Grammar pool edges) (constraint : LayerBoundTemplates.Constraint m (Index pool))
    (member : constraint ∈ CommonBoundRefCoalescing.template pool (queries pool) edges) :
    ConstraintGrammar pool constraint := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
  have shape := grammar edge included
  cases first : CommonBoundRefCoalescing.inputAt pool (queries pool) edge.1 <;>
    cases last : CommonBoundRefCoalescing.inputAt pool (queries pool) edge.2 <;>
    simp_all [CommonBoundRefCoalescing.classify, ConstraintGrammar]

theorem rigid_grammar (pool : Pool m) (edges : List (Edge pool))
    (grammar : Grammar pool edges) : Grammar pool (rigid pool edges) := by
  intro comparison member
  obtain ⟨constraint, originalMember, contributed⟩ := List.mem_flatMap.mp member
  have shape := template_grammar pool edges grammar constraint originalMember
  cases constraint with
  | lower | flow => cases contributed
  | upper source bound =>
      obtain ⟨lowerBound, lowerMember, rfl⟩ := List.mem_map.mp contributed
      obtain ⟨start, seed, _⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds
          (CommonBoundRefCoalescing.template pool (queries pool) edges) source lowerBound).mp lowerMember
      exact ⟨template_grammar pool edges grammar (.lower lowerBound start) seed, shape⟩
  | check first last =>
      have same : comparison = (first, last) := List.mem_singleton.mp contributed
      subst comparison
      exact shape

theorem inspect_grammar (pool : Pool m) (edge : Edge pool)
    (first : LowerRef pool edge.1.val) (last : UpperRef pool edge.2.val)
    (branch : Branch pool) (returned : branch ∈ inspect pool edge) : Grammar pool branch.children := by
  obtain ⟨⟨original, included⟩, _, rfl⟩ := List.mem_map.mp returned
  intro child member
  exact CommonPatternBoundInspection.inspected_child_polarity pool edge.1.val edge.2.val first last
    original included child.1.val child.2.val
    (CommonBoundRefBranches.splitBranch_child_origin pool (queries pool) original _ child member)

theorem preserve_grammar (pool : Pool m) (current : List (Edge pool))
    (grammar : Grammar pool current) (edge : Edge pool) (member : edge ∈ rigid pool current)
    (branch : Branch pool) (returned : branch ∈ inspect pool edge) :
    Grammar pool (branch.children ++ current) := by
  have shape := rigid_grammar pool current grammar edge member
  exact (inspect_grammar pool edge shape.1 shape.2 branch returned).append grammar

theorem run_grammar (pool : Pool m) (edges : List (Edge pool)) (grammar : Grammar pool edges)
    (final : State pool) (returned : final ∈ run pool edges) : Grammar pool final.edges :=
  FiniteBranchingWorklist.run_preserves (inventory pool) (rigid pool) (inspect pool)
    (Grammar pool) (preserve_grammar pool) edges [] grammar final returned

theorem inspect_models_exact (pool : Pool m) (edge : Edge pool)
    (first : LowerRef pool edge.1.val) (last : UpperRef pool edge.2.val)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (widths : CommonGeneratedWidth.PoolWidth pool values) :
    (∃ branch ∈ inspect pool edge, branch.Models (edgeHolds pool values) (auxHolds pool rows values)) ↔
      edgeHolds pool values edge :=
  (CommonBoundRefBranches.splitOutput_exact pool (queries pool) rows values _ _).trans
    (CommonPatternBoundInspection.inspect_exact pool edge.1.val edge.2.val first last rows values realizes widths)

/-- Independent models are recovered by the actual finite run, with arbitrary
Common node and row assignments and without requiring run success as a premise. -/
theorem run_models_exact (pool : Pool m) (edges : List (Edge pool)) (grammar : Grammar pool edges)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (widths : CommonGeneratedWidth.PoolWidth pool values) :
    EdgesHold pool values edges ↔
      ∃ final ∈ run pool edges, final.Models (edgeHolds pool values) (auxHolds pool rows values) := by
  have exactness := FiniteBranchingWorklist.run_models_exact_invariant
    (inventory pool) (rigid pool) (inspect pool) (Grammar pool) (preserve_grammar pool)
    (edgeHolds pool values) (auxHolds pool rows values)
    (fun current _ valid => CommonBoundRefWorklist.rigid_sound pool rows values realizes current valid)
    (by
      intro current good edge _ included
      have shape := rigid_grammar pool current good edge included
      exact (inspect_models_exact pool edge shape.1 shape.2 rows values realizes widths).symm)
    edges [] grammar
  constructor
  · intro accepted
    exact exactness.mp ⟨accepted, by simp⟩
  · intro returned
    exact (exactness.mpr returned).1

end Yulang.CommonPatternBoundWorklist
