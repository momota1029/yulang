import Yulang.CommonBoundRefBranches
import Yulang.CommonBoundRefExact

/-!
# The finite worklist for actual fixed bound-reference inspection

The inventory contains every pair of query-supported references over the
original shared pool. Inspection emits ordinary indexed edges and original
row/literal auxiliary checks. The executable worklist contains no model,
realizer, grammar proof, chosen solution, or caller fuel.

Every returned branch is closed under rigid discovery and records at most
`(5N+3)^2` inspections along its trace. These are unconditional properties of
this actual finite computation; semantic and generated-grammar connections
are separate theorems.
-/

namespace Yulang.CommonBoundRefWorklist

open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPoolQueries (queries)

variable {m : Nat}

abbrev Index (pool : Pool m) := CommonBoundRefCoalescing.Index pool (queries pool)
abbrev Edge (pool : Pool m) := CommonBoundRefCoalescing.Edge pool (queries pool)
abbrev Aux (pool : Pool m) := CommonOptionalBoundEncoding.InputCheck pool
abbrev Branch (pool : Pool m) := CommonBoundRefBranches.Split pool (queries pool)
abbrev State (pool : Pool m) := FiniteBranchingWorklist.State (Edge pool) (Aux pool)

def inventory (pool : Pool m) : List (Edge pool) :=
  CommonBoundRefCoalescing.inventory pool (queries pool)

def rigid (pool : Pool m) (edges : List (Edge pool)) : List (Edge pool) :=
  CommonBoundRefCoalescing.rigid pool (queries pool) edges

def inspect (pool : Pool m) (edge : Edge pool) : List (Branch pool) :=
  CommonBoundRefBranches.splitOutput pool (queries pool)
    (CommonBoundRefInspection.inspect pool edge.1.val edge.2.val)
    (CommonBoundRefInspection.inspect_supported_refs pool edge.1.val edge.2.val
      edge.1.property edge.2.property)

def run (pool : Pool m) (edges : List (Edge pool)) : List (State pool) :=
  FiniteBranchingWorklist.run (inventory pool) (rigid pool) (inspect pool) edges []

theorem inventory_complete (pool : Pool m) (edge : Edge pool) : edge ∈ inventory pool :=
  CommonBoundRefCoalescing.inventory_member pool (queries pool) edge

theorem edges_supported (pool : Pool m) (edges : List (Edge pool)) : edges ⊆ inventory pool :=
  fun edge _ => inventory_complete pool edge

theorem inspection_supported (pool : Pool m) :
    FiniteBranchingWorklist.InspectionSupported (inventory pool) (inspect pool) := by
  intro _ _ _ _ edge _
  exact inventory_complete pool edge

theorem rigid_supported (pool : Pool m) :
    FiniteBranchingWorklist.RigidSupported (inventory pool) (rigid pool) := by
  intro _ _ edge _
  exact inventory_complete pool edge

/-- There is no unprocessed rigid edge at any returned state. -/
theorem run_finished (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    FiniteBranchingWorklist.pending (inventory pool) (rigid pool) final = none :=
  FiniteBranchingWorklist.run_finished (inventory pool) (rigid pool) (inspect pool) edges []
    (edges_supported pool edges) (inspection_supported pool) final returned

/-- Every final rigid edge has an actual selected inspection branch in the
trace, with every child and auxiliary check retained in the final state. -/
theorem run_closed (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    FiniteBranchingWorklist.Closed (rigid pool) (inspect pool) final :=
  FiniteBranchingWorklist.run_closed (inventory pool) (rigid pool) (inspect pool) edges []
    (edges_supported pool edges) (inspection_supported pool) (rigid_supported pool) final returned

/-- This is a per-branch inspection bound, not a linear bound on the number
of alternatives explored by the branching computation. -/
theorem run_bound (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) :
    final.processed.Nodup ∧ final.trace.length = final.processed.length ∧
      final.trace.length ≤ (5 * pool.size + 3) ^ 2 := by
  obtain ⟨distinct, _, _, lengths, bound⟩ :=
    FiniteBranchingWorklist.run_bound (inventory pool) (rigid pool) (inspect pool) edges []
      (edges_supported pool edges) (inspection_supported pool) final returned
  exact ⟨distinct, lengths, Nat.le_trans bound (CommonBoundRefCoalescing.generated_inventory_bound pool)⟩

theorem run_retains (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) : edges ⊆ final.edges :=
  (FiniteBranchingWorklist.run_retains (inventory pool) (rigid pool) (inspect pool)
    edges [] final returned).1

end Yulang.CommonBoundRefWorklist
