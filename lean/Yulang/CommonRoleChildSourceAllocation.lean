import Yulang.CommonRoleAllocatedGraph
import Yulang.CommonRoleCacheInvalidation

/-! Actual unary child production computes occurrence names from retained source
slots and connects them to canonical graph allocation. This is the existing
int-materialization adapter, not general interval or recursive-node allocation.
Constructed type wrappers are not allocated as fresh source variables. -/
namespace Yulang.CommonRoleChildSourceAllocation
open CommonRoleMaterializedDomain CommonRoleChildTemplates
open CommonRoleCacheInvalidation (slots dependencies)
open CommonRoleSourceIdentity (Table Slot source retain)
open CommonRoleCanonicalSourceGraph (canonical)
open CommonRoleCanonicalSourceGrowth (newRoot retainObservation)
open CommonRoleAllocatedGraph (allocate retainSnapshot)
open CommonRoleRegularGraph (Graph)
open CommonRoleGraphInspection (inspectSnapshot VisibleHead)
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleSettledConstraints (State)

/-- Structural extraction cannot invent a source slot. -/
theorem extract_dependencies (depth : Nat) (parent child : Endpoint n)
    (found : extract depth parent = some child) :
    ∀ i ∈ slots child, i ∈ slots parent := by
  induction depth generalizing parent child with
  | zero => cases found; exact fun _ h => h
  | succ depth ih =>
    cases parent with
    | slot i => simp [extract] at found
    | fixed t =>
      simp only [extract] at found
      obtain ⟨v, _, equal⟩ := Option.map_eq_some_iff.mp found
      subst child
      simp [slots]
    | wrap c e => exact ih e child found

/-- Instantiation can copy or discard dependencies, but introduces none. -/
theorem plug_dependencies (t : Template) (e : Endpoint n) :
    ∀ i ∈ slots (plug t e), i ∈ slots e := by
  induction t with
  | var name => exact fun _ h => h
  | atom a => simp [plug, slots]
  | wrap c t ih => exact ih

/-- Every declaration child retains the source dependencies of its parent. -/
theorem declaration_dependencies (d : Declaration) (parent child : SourceRequest n)
    (member : child ∈ CommonRoleSourceTemplateClosure.declarationChildren d parent) :
    ∀ i ∈ dependencies child, i ∈ dependencies parent := by
  unfold CommonRoleSourceTemplateClosure.declarationChildren at member
  split at member
  · simp at member
  · rename_i depth located
    split at member
    · rename_i lo hi lf hf
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
      intro i hiDep
      rcases List.mem_append.mp hiDep with lower | upper
      · exact List.mem_append_left _
          (extract_dependencies depth parent.lower lo lf i (plug_dependencies r.2 lo i lower))
      · exact List.mem_append_right _
          (extract_dependencies depth parent.upper hi hf i (plug_dependencies r.2 hi i upper))
    · simp at member

/-- The structural enumerator also retains source dependencies, including
alternatives that are not selected in the present state. -/
theorem next_dependencies (registry : Registry) (parent child : SourceRequest n)
    (member : child ∈ CommonRoleSourceTemplateClosure.next registry parent) :
    ∀ i ∈ dependencies child, i ∈ dependencies parent := by
  obtain ⟨d, _, generated⟩ := List.mem_flatMap.mp (List.mem_filter.mp member).1
  exact declaration_dependencies d parent child generated

/-- Every recursively generated template uses only source slots of the root.
The result holds across arbitrary state changes between generation steps. -/
theorem closure_dependencies (registry : Registry) (root child : SourceRequest n)
    (member : child ∈ CommonRoleSourceTemplateClosure.closure registry root) :
    ∀ i ∈ dependencies child, i ∈ dependencies root := by
  have path := CommonRoleSourceTemplateClosure.closure_sound registry root child member
  clear member
  induction path with
  | refl => exact fun _ h => h
  | step edge _ ih => exact fun i h => next_dependencies registry _ _ edge i (ih i h)

/-- Allocate one occurrence per ordered endpoint dependency, retaining duplicates. -/
def occurrenceNames (table : Table) (child : SourceRequest table.length) : Table :=
  (dependencies child).map (source table)

/-- The occurrence's old owner is computed by its position, not chosen by value. -/
def owner (table : Table) (child : SourceRequest table.length)
    (i : Slot (occurrenceNames table child)) : Slot table :=
  (dependencies child).get ⟨i.val, by simpa [occurrenceNames] using i.isLt⟩

theorem owner_present (table : Table) (child : SourceRequest table.length)
    (i : Slot (occurrenceNames table child)) : owner table child i ∈ dependencies child :=
  List.get_mem ..

theorem occurrence_source (table : Table) (child : SourceRequest table.length)
    (i : Slot (occurrenceNames table child)) :
    source (occurrenceNames table child) i = source table (owner table child i) := by
  simp [source, occurrenceNames, owner]

/-- Exact numeric roots follow from the generated names without an alias premise. -/
theorem allocated_root (table : Table) (child : SourceRequest table.length)
    (i : Slot (occurrenceNames table child)) :
    newRoot table (occurrenceNames table child) i =
      retain table (occurrenceNames table child) (canonical table (owner table child i)) :=
  (CommonRoleCanonicalSourceGrowth.newRoot_old_exact ..).mpr (occurrence_source ..)

/-- Distinct generated occurrences share a root exactly when original source
names agree. Equal unknown observations never identify different source names. -/
theorem allocated_identity_exact (table : Table) (child : SourceRequest table.length)
    (i j : Slot (occurrenceNames table child)) :
    newRoot table (occurrenceNames table child) i =
      newRoot table (occurrenceNames table child) j ↔
      source table (owner table child i) = source table (owner table child j) := by
  rw [CommonRoleCanonicalSourceGrowth.newRoot_identity_exact,
    occurrence_source, occurrence_source]

/-- Complete inspection at each generated occurrence retains the computed old
canonical root, including K2, capture payloads, visible order and duplicates. -/
theorem allocated_snapshot (table : Table) (child : SourceRequest table.length)
    (graph : Graph table.length) (role : Nat) (visible : List VisibleHead)
    (i : Slot (occurrenceNames table child)) :
    inspectSnapshot (allocate table (occurrenceNames table child) graph) role
      (newRoot table (occurrenceNames table child) i) visible =
        retainSnapshot table (occurrenceNames table child)
          (inspectSnapshot graph role (canonical table (owner table child i)) visible) := by
  rw [allocated_root, CommonRoleAllocatedGraph.snapshot_allocated]

/-- Actual producer to finite source occurrence allocation, in the unary int-only
adapter. Arbitrary graphs and future states are allowed; no graph adequacy or
source-name equality is supplied. This is auxiliary B4 work, not final resolution. -/
theorem actual_child_allocation (table : Table) (registry : Registry)
    (root parent : SourceRequest table.length)
    (parentPresent : parent ∈ CommonRoleSourceTemplateClosure.closure registry root)
    (s : State table.length) (d : Declaration) (lp hp : Ty) (depth : Nat) (child : Request)
    (produced : production registry.declarations (parent.eval s) = some (d, lp, hp))
    (located : CommonRoleCaptureOrigin.captureDepth d.head = some depth)
    (generated : child ∈ children (parent.eval s) d lp hp) :
    ∃ childSource : SourceRequest table.length,
      childSource ∈ CommonRoleSourceTemplateClosure.closure registry root ∧
      childSource.eval s = child ∧
      (∀ future : State table.length, childSource.eval future ∈
        CommonRoleSourceTemplateClosure.materializedDomain registry root) ∧
      (∀ i : Slot (occurrenceNames table childSource),
        owner table childSource i ∈ dependencies root ∧
        newRoot table (occurrenceNames table childSource) i =
          retain table (occurrenceNames table childSource)
            (canonical table (owner table childSource i)) ∧
        ∀ (graph : Graph table.length) (role : Nat) (visible : List VisibleHead),
          inspectSnapshot (allocate table (occurrenceNames table childSource) graph) role
            (newRoot table (occurrenceNames table childSource) i) visible =
              retainSnapshot table (occurrenceNames table childSource)
                (inspectSnapshot graph role (canonical table (owner table childSource i)) visible)) := by
  obtain ⟨childSource, present, equal⟩ :=
    CommonRoleSourceTemplateClosure.actual_child_closed registry root parent parentPresent
      s d lp hp depth child produced located generated
  refine ⟨childSource, present, equal,
    CommonRoleSourceTemplateClosure.all_states_present registry root childSource present, ?_⟩
  intro i
  exact ⟨closure_dependencies registry root childSource present _ (owner_present table childSource i),
    allocated_root table childSource i,
    fun graph role visible => allocated_snapshot table childSource graph role visible i⟩

end Yulang.CommonRoleChildSourceAllocation
