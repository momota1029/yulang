import Yulang.CommonRoleChildSourceAllocation

/-! One finite source occurrence allocation for all structural descendants in
 the unary/int adapter. The table retains order and duplicates, and does not
 depend on the current state or on which child is currently selected. This is
 auxiliary B4 work; general interval and recursive-node allocation remain open. -/
namespace Yulang.CommonRoleClosureSourceAllocation
open CommonRoleMaterializedDomain CommonRoleChildTemplates
open CommonRoleCacheInvalidation (dependencies)
open CommonRoleSourceIdentity (Table Slot source retain)
open CommonRoleCanonicalSourceGraph (canonical)
open CommonRoleCanonicalSourceGrowth (newRoot)
open CommonRoleAllocatedGraph (allocate retainSnapshot)
open CommonRoleRegularGraph (Graph)
open CommonRoleGraphInspection (inspectSnapshot VisibleHead)
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleSettledConstraints (State)
open CommonRoleSourceTemplateClosure (closure Reach materializedDomain)

/-- Every closure position contributes its ordered dependency occurrences. -/
def entries (registry : Registry) (root : SourceRequest n) :
    List (SourceRequest n × Fin n) :=
  (closure registry root).flatMap fun child =>
    (dependencies child).map fun owner => (child, owner)

/-- Independent structural reachability exactly characterizes occurrence entries.
This does not identify structural alternatives with actual candidate selection. -/
theorem entries_exact (registry : Registry) (root child : SourceRequest n) (owner : Fin n) :
    (child, owner) ∈ entries registry root ↔
      Reach registry root child ∧ owner ∈ dependencies child := by
  simp only [entries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨q, present, i, member, same, equal⟩
    subst q
    subst i
    exact ⟨CommonRoleSourceTemplateClosure.closure_sound registry root child present, member⟩
  · rintro ⟨reachable, member⟩
    exact ⟨child, CommonRoleSourceTemplateClosure.closure_complete registry root child reachable,
      owner, member, rfl, rfl⟩

/-- Names for a single allocation, shared by the complete structural closure. -/
def names (table : Table) (registry : Registry) (root : SourceRequest table.length) : Table :=
  (entries registry root).map fun e => source table e.2

/-- Each allocated index remembers both its child and old source owner. -/
def entry (table : Table) (registry : Registry) (root : SourceRequest table.length)
    (i : Slot (names table registry root)) : SourceRequest table.length × Slot table :=
  (entries registry root).get ⟨i.val, by simpa [names] using i.isLt⟩

theorem entry_present (table : Table) (registry : Registry) (root : SourceRequest table.length)
    (i : Slot (names table registry root)) :
    Reach registry root (entry table registry root i).1 ∧
      (entry table registry root i).2 ∈ dependencies (entry table registry root i).1 := by
  apply (entries_exact registry root _ _).mp
  exact List.get_mem ..

/-- Every reachable child's dependency has a location in the shared allocation. -/
theorem dependency_present (table : Table) (registry : Registry)
    (root child : SourceRequest table.length) (reachable : Reach registry root child)
    (owner : Slot table) (member : owner ∈ dependencies child) :
    ∃ i : Slot (names table registry root), entry table registry root i = (child, owner) := by
  obtain ⟨i, found⟩ := List.get_of_mem ((entries_exact registry root child owner).mpr
    ⟨reachable, member⟩)
  exact ⟨⟨i.val, by simp [names]⟩, found⟩

/-- Every allocated occurrence originates in a source dependency of the root. -/
theorem owner_in_root (table : Table) (registry : Registry) (root : SourceRequest table.length)
    (i : Slot (names table registry root)) :
    (entry table registry root i).2 ∈ dependencies root := by
  obtain ⟨reachable, member⟩ := entry_present table registry root i
  exact CommonRoleChildSourceAllocation.closure_dependencies registry root _
    (CommonRoleSourceTemplateClosure.closure_complete registry root _ reachable) _ member

theorem occurrence_source (table : Table) (registry : Registry)
    (root : SourceRequest table.length) (i : Slot (names table registry root)) :
    source (names table registry root) i = source table (entry table registry root i).2 := by
  simp [source, names, entry]

/-- Numeric canonical roots are computed from generated names, not assumed. -/
theorem allocated_root (table : Table) (registry : Registry)
    (root : SourceRequest table.length) (i : Slot (names table registry root)) :
    newRoot table (names table registry root) i =
      retain table (names table registry root) (canonical table (entry table registry root i).2) :=
  (CommonRoleCanonicalSourceGrowth.newRoot_old_exact ..).mpr (occurrence_source ..)

/-- Identity across different children and repeated occurrences is exactly old
source-name equality, regardless of their current observations. -/
theorem identity_exact (table : Table) (registry : Registry)
    (root : SourceRequest table.length) (i j : Slot (names table registry root)) :
    newRoot table (names table registry root) i = newRoot table (names table registry root) j ↔
      source table (entry table registry root i).2 = source table (entry table registry root j).2 := by
  rw [CommonRoleCanonicalSourceGrowth.newRoot_identity_exact, occurrence_source, occurrence_source]

/-- Full head inspection retains K2, capture payloads, order and duplicates. -/
theorem allocated_snapshot (table : Table) (registry : Registry)
    (root : SourceRequest table.length) (graph : Graph table.length)
    (role : Nat) (visible : List VisibleHead) (i : Slot (names table registry root)) :
    inspectSnapshot (allocate table (names table registry root) graph) role
      (newRoot table (names table registry root) i) visible =
        retainSnapshot table (names table registry root)
          (inspectSnapshot graph role (canonical table (entry table registry root i).2) visible) := by
  rw [allocated_root, CommonRoleAllocatedGraph.snapshot_allocated]

/-- A finite actual production history. Every edge stores its own ordinary
state in `Generated`, so no agreement between successive states is required. -/
inductive Trace (registry : Registry) (root : SourceRequest n) : SourceRequest n → Prop where
  | start : Trace registry root root
  | step {parent child : SourceRequest n} :
      Trace registry root parent → Generated registry child parent → Trace registry root child

/-- The global domain is derived from actual history, not supplied by the caller. -/
theorem trace_closed (registry : Registry) (root child : SourceRequest n)
    (trace : Trace registry root child) : child ∈ closure registry root := by
  induction trace with
  | start => rw [closure]; exact List.mem_cons_self
  | step _ edge ih => exact CommonRoleSourceTemplateClosure.generated_closed registry root _ _ ih edge

/-- Every dependency after any finite actual history has a place in the original
allocation, and every future materialization remains in the computed domain. -/
theorem trace_allocated (table : Table) (registry : Registry)
    (root child : SourceRequest table.length) (trace : Trace registry root child) :
    (∀ future : State table.length, child.eval future ∈ materializedDomain registry root) ∧
    (∀ owner ∈ dependencies child, ∃ i : Slot (names table registry root),
      entry table registry root i = (child, owner)) := by
  have present := trace_closed registry root child trace
  exact ⟨CommonRoleSourceTemplateClosure.all_states_present registry root child present,
    fun owner member => dependency_present table registry root child
      (CommonRoleSourceTemplateClosure.closure_sound registry root child present) owner member⟩

/-- Every actual capture-bearing child uses the same precomputed finite occurrence
allocation. State changes and later descendants do not require a larger domain.
The production/capture hypotheses are those of the existing unary/int adapter,
not a claim of general interval resolution or complete B4. -/
theorem actual_child_shared_allocation (table : Table) (registry : Registry)
    (root parent : SourceRequest table.length) (history : Trace registry root parent)
    (s : State table.length) (d : Declaration) (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (parent.eval s) = some (d, lp, hp))
    (located : CommonRoleCaptureOrigin.captureDepth d.head = some depth)
    (generated : child ∈ children (parent.eval s) d lp hp) :
    ∃ childSource : SourceRequest table.length,
      Trace registry root childSource ∧ childSource.eval s = child ∧
      (∀ future : State table.length, childSource.eval future ∈ materializedDomain registry root) ∧
      (∀ owner ∈ dependencies childSource, ∃ i : Slot (names table registry root),
        entry table registry root i = (childSource, owner) ∧
        source (names table registry root) i = source table owner ∧
        newRoot table (names table registry root) i =
          retain table (names table registry root) (canonical table owner) ∧
        ∀ (graph : Graph table.length) (role : Nat) (visible : List VisibleHead),
          inspectSnapshot (allocate table (names table registry root) graph) role
            (newRoot table (names table registry root) i) visible =
              retainSnapshot table (names table registry root)
                (inspectSnapshot graph role (canonical table owner) visible)) := by
  obtain ⟨childSource, equal, edge, _⟩ :=
    CommonRoleChildTemplates.every_child_generated registry parent s d lp hp depth child
      produced located generated
  have childHistory := Trace.step history edge
  obtain ⟨future, allocated⟩ := trace_allocated table registry root childSource childHistory
  refine ⟨childSource, childHistory, equal, future, ?_⟩
  intro owner member
  obtain ⟨i, found⟩ := allocated owner member
  refine ⟨i, found, ?_, ?_, ?_⟩
  · simpa only [found] using occurrence_source table registry root i
  · simpa only [found] using allocated_root table registry root i
  · intro graph role visible
    simpa only [found] using allocated_snapshot table registry root graph role visible i

end Yulang.CommonRoleClosureSourceAllocation
