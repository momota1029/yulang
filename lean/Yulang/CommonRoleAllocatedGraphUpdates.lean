import Yulang.CommonRoleClosureSourceAllocation

/-! Concrete old-node edits commute with allocation. This includes arbitrary
finite edits to cyclic graphs and exact complete inspection snapshots. Payloads
refer only to old storage; introducing new syntax-node references and general
interval solver generation remain outside this auxiliary B4 boundary. -/
namespace Yulang.CommonRoleAllocatedGraphUpdates
open CommonRoleSourceIdentity (Table Slot retain)
open CommonRoleRegularGraph (Graph Node)
open CommonRoleAllocatedGraph (allocate mapNode retainSnapshot)
open CommonRoleCanonicalSourceGraph (canonical)
open CommonRoleCanonicalSourceGrowth (newRoot retainObservation)
open CommonRoleGraphInspection (inspect inspectSnapshot VisibleHead)

abbrev Edit (n : Nat) := Fin n × Node n

/-- Replace one concrete node, without changing any other address. -/
def write (graph : Graph n) (edit : Edit n) : Graph n := fun i =>
  if i = edit.1 then edit.2 else graph i

def run (graph : Graph n) : List (Edit n) → Graph n
  | [] => graph
  | edit :: rest => run (write graph edit) rest

/-- Both the destination and every payload edge use retained old addresses. -/
def lift (table extra : Table) (edit : Edit table.length) : Edit (table ++ extra).length :=
  (retain table extra edit.1, mapNode (retain table extra) edit.2)

private theorem retain_injective (table extra : Table) :
    Function.Injective (retain table extra) := by
  intro a b equal
  apply Fin.ext
  exact congrArg (fun i : Slot (table ++ extra) => i.val) equal

/-- This commutation is graph equality, not only observational equivalence. -/
theorem write_allocate (table extra : Table) (graph : Graph table.length)
    (edit : Edit table.length) :
    write (allocate table extra graph) (lift table extra edit) =
      allocate table extra (write graph edit) := by
  funext i
  by_cases old : i.val < table.length
  · let j : Slot table := ⟨i.val, old⟩
    have same : i = retain table extra j := Fin.ext rfl
    rw [same]
    simp only [write, lift, CommonRoleAllocatedGraph.allocate,
      CommonRoleAllocatedGraph.grow_retained, (retain_injective table extra).eq_iff]
    split <;> rfl
  · have different : i ≠ retain table extra edit.1 := by
      intro same
      apply old
      have values := congrArg Fin.val same
      simpa [retain] using values ▸ edit.1.isLt
    simp [write, lift, different, allocate, CommonRoleAllocatedGraph.grow, old]

/-- Arbitrary repeated edits, including cycle-changing edits, are transported. -/
theorem run_allocate (table extra : Table) (graph : Graph table.length)
    (edits : List (Edit table.length)) :
    run (allocate table extra graph) (edits.map (lift table extra)) =
      allocate table extra (run graph edits) := by
  induction edits generalizing graph with
  | nil => rfl
  | cons edit rest ih =>
    simp only [run, List.map_cons, write_allocate]
    exact ih (write graph edit)

/-- Exact snapshots are compared after the same edits, not with stale old state. -/
theorem updated_snapshot (table extra : Table) (graph : Graph table.length)
    (edits : List (Edit table.length)) (role : Nat) (root : Slot table)
    (visible : List VisibleHead) :
    inspectSnapshot (run (allocate table extra graph) (edits.map (lift table extra)))
      role (retain table extra root) visible =
      retainSnapshot table extra (inspectSnapshot (run graph edits) role root visible) := by
  rw [run_allocate, CommonRoleAllocatedGraph.snapshot_allocated]

open CommonRoleClosureSourceAllocation (names entry Trace)
open CommonRoleMaterializedDomain (SourceRequest)
open CommonRoleOpenProducer (Registry)
open CommonRoleCacheInvalidation (dependencies)

/-- Every dependency reached by actual generation shares the precomputed table,
then follows any finite old-node update history with its full exact snapshot. -/
theorem actual_history_updated_allocation (table : Table) (registry : Registry)
    (root child : SourceRequest table.length) (history : Trace registry root child)
    (owner : Slot table) (member : owner ∈ dependencies child)
    (graph : Graph table.length) (edits : List (Edit table.length)) :
    ∃ i : Slot (names table registry root), entry table registry root i = (child, owner) ∧
      ∀ (role : Nat) (visible : List VisibleHead),
        inspectSnapshot (run (allocate table (names table registry root) graph)
          (edits.map (lift table (names table registry root)))) role
          (newRoot table (names table registry root) i) visible =
        retainSnapshot table (names table registry root)
          (inspectSnapshot (run graph edits) role (canonical table owner) visible) := by
  obtain ⟨_, allocated⟩ := CommonRoleClosureSourceAllocation.trace_allocated
    table registry root child history
  obtain ⟨i, found⟩ := allocated owner member
  refine ⟨i, found, ?_⟩
  intro role visible
  rw [run_allocate]
  simpa only [found] using CommonRoleClosureSourceAllocation.allocated_snapshot
    table registry root (run graph edits) role visible i

/-- Update every old address from a concrete readout, leaving the suffix intact.
This writes existing expanded storage rather than discarding and reallocating it. -/
def refresh (table extra : Table) (updated : Graph table.length)
    (expanded : Graph (table ++ extra).length) : Graph (table ++ extra).length := fun i =>
  if h : i.val < table.length then
    mapNode (retain table extra) (updated ⟨i.val, h⟩)
  else expanded i

/-- Refresh implements allocation of the updated graph while retaining the suffix. -/
theorem refresh_allocate (table extra : Table) (original updated : Graph table.length) :
    refresh table extra updated (allocate table extra original) = allocate table extra updated := by
  funext i
  simp only [refresh, allocate, CommonRoleAllocatedGraph.grow]
  split <;> simp_all

open CommonRoleDynamicIndexResidualBatches (Problem Satisfies appendMany solve)
open CommonRoleScalarSourceInspection (graph code)
open Core.PresenceGeneration (Comp)

/-- The concrete finite ordinary solver drives writes to old storage. The
positive-string adapter is a proof fragment, not a language rejection rule. -/
def solveRefresh (table extra : Table) (initial : Graph table.length)
    (p : Problem table) (updates : List (Problem table)) : Graph (table ++ extra).length :=
  refresh table extra (graph (solve table p updates).state) (allocate table extra initial)

/-- Full post-update snapshots agree, with no original/updated graph premise. -/
theorem solve_snapshot_exact (table extra : Table) (initial : Graph table.length)
    (p : Problem table) (updates : List (Problem table)) (role : Nat) (i : Slot table)
    (visible : List VisibleHead) :
    inspectSnapshot (solveRefresh table extra initial p updates) role
      (canonical (table ++ extra) (retain table extra i)) visible =
    retainSnapshot table extra
      (inspectSnapshot (CommonRoleCanonicalSourceGraph.prepare table p updates).nodes role
        ((CommonRoleCanonicalSourceGraph.prepare table p updates).root i) visible) := by
  unfold solveRefresh
  rw [refresh_allocate, CommonRoleAllocatedGraph.canonical_snapshot_allocated]
  rfl

/-- Soundness and completeness for original source string entailment after all
ordinary updates, observed through allocated and refreshed canonical storage. -/
theorem solve_string_exact (table extra : Table) (initial : Graph table.length)
    (p : Problem table) (updates : List (Problem table)) (i : Slot table) :
    inspect (solveRefresh table extra initial p updates) (.scalar (code .str))
      (canonical (table ++ extra) (retain table extra i)) = .matched [] ↔
    ∀ a : Slot table → Comp Common.model, Satisfies table (appendMany table p updates) a →
      Common.Equivalent (a i).1 (.base .str) := by
  unfold solveRefresh
  rw [refresh_allocate, CommonRoleAllocatedGraph.canonical_inspect_allocated]
  have transport : ∀ o : CommonRoleGraphInspection.Observation table.length,
      retainObservation table extra o = .matched [] ↔ o = .matched [] := by
    intro o
    cases o <;> simp [retainObservation]
  rw [transport]
  exact CommonRoleCanonicalSourceGraph.inspect_string_exact table p updates i

/-- Unknown after refresh is exactly two disagreeing original source models;
not a supplied consistency or graph-adequacy assumption. -/
theorem solve_unknown_exact (table extra : Table) (initial : Graph table.length)
    (p : Problem table) (updates : List (Problem table)) (role : Nat) (i : Slot table)
    (visible : List VisibleHead) :
    inspectSnapshot (solveRefresh table extra initial p updates) role
      (canonical (table ++ extra) (retain table extra i)) visible = .unknown ↔
    ∃ a b : Slot table → Comp Common.model,
      Satisfies table (appendMany table p updates) a ∧
      Satisfies table (appendMany table p updates) b ∧
      ¬ Common.Equivalent (a i).1 (b i).1 := by
  rw [solve_snapshot_exact]
  have transport : ∀ snapshot : CommonRoleGraphInspection.Snapshot table.length,
      retainSnapshot table extra snapshot = .unknown ↔ snapshot = .unknown := by
    intro snapshot
    cases snapshot <;> simp [retainSnapshot]
  rw [transport]
  exact CommonRoleCanonicalSourceGraph.snapshot_unknown_exact table p updates role i visible

/-- End-to-end dependency readout: any actual generated child's source owner can
be inspected after concrete finite ordinary updates in the one shared allocation.
The generation and positive-string ordinary adapters share source slots, not an
assumed equivalence of their type systems. This does not prove child selection. -/
theorem actual_history_solve_exact (table : Table) (registry : Registry)
    (root child : SourceRequest table.length) (history : Trace registry root child)
    (owner : Slot table) (member : owner ∈ dependencies child)
    (initial : Graph table.length) (p : Problem table) (updates : List (Problem table)) :
    ∃ i : Slot (names table registry root), entry table registry root i = (child, owner) ∧
      (inspect (solveRefresh table (names table registry root) initial p updates)
        (.scalar (code .str)) (newRoot table (names table registry root) i) = .matched [] ↔
        ∀ a : Slot table → Comp Common.model,
          Satisfies table (appendMany table p updates) a →
            Common.Equivalent (a owner).1 (.base .str)) ∧
      (∀ (role : Nat) (visible : List VisibleHead),
        inspectSnapshot (solveRefresh table (names table registry root) initial p updates)
          role (newRoot table (names table registry root) i) visible = .unknown ↔
          ∃ a b : Slot table → Comp Common.model,
            Satisfies table (appendMany table p updates) a ∧
            Satisfies table (appendMany table p updates) b ∧
            ¬ Common.Equivalent (a owner).1 (b owner).1) := by
  obtain ⟨_, allocated⟩ := CommonRoleClosureSourceAllocation.trace_allocated
    table registry root child history
  obtain ⟨i, found⟩ := allocated owner member
  have routed : newRoot table (names table registry root) i =
      canonical (table ++ names table registry root)
        (retain table (names table registry root) owner) := by
    rw [CommonRoleClosureSourceAllocation.allocated_root,
      CommonRoleCanonicalSourceGrowth.canonical_retained]
    simp only [found]
  refine ⟨i, found, ?_, ?_⟩
  · rw [routed]
    exact solve_string_exact table (names table registry root) initial p updates owner
  · intro role visible
    rw [routed]
    exact solve_unknown_exact table (names table registry root) initial p updates role owner visible

end Yulang.CommonRoleAllocatedGraphUpdates
