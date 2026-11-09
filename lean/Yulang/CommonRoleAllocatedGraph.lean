import Yulang.CommonRoleCanonicalSourceGrowth

/-! Executable graph growth retains structural and nominal edges at old source
indices. All finite observations and direct structural cycles are preserved.
Allocation of unresolved new storage also preserves bisimulation-based K2 and
the complete head snapshot. Later updates to old nodes are outside this boundary. -/
namespace Yulang.CommonRoleAllocatedGraph
open CommonRoleSourceIdentity (Table Slot)
open CommonRoleSourceIdentity (retain)
open CommonRoleCanonicalSourceGraph (canonical)
open CommonRoleCanonicalSourceGrowth (canonical_retained)
open CommonRoleRegularGraph
open CommonRoleGraphBisimulation (observe)

/-- Reconstruct every explicit child edge, including nominal arguments. -/
def mapNode (f : Fin n → Fin m) : Node n → Node m
  | .unresolved => .unresolved
  | .scalar name => .scalar name
  | .structural name children => .structural name (children.map f)
  | .nominal name children => .nominal name (children.map f)

/-- Old storage is reconstructed. Only genuinely new slots use supplied nodes. -/
def grow (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) :
    Graph (table ++ extra).length := fun i =>
  if h : i.val < table.length then
    mapNode (retain table extra) (graph ⟨i.val,h⟩)
  else fresh i

@[simp] theorem grow_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (i : Slot table) :
    grow table extra graph fresh (retain table extra i) =
      mapNode (retain table extra) (graph i) := by
  simp [grow, retain, i.isLt]

@[simp] theorem successors_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (i : Slot table) :
    successors (grow table extra graph fresh) (retain table extra i) =
      (successors graph i).map (retain table extra) := by
  simp only [successors, grow_retained]
  cases graph i <;> rfl

private theorem retain_injective (table extra : Table) :
    Function.Injective (retain table extra) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Slot (table ++ extra) => x.val) h

/-- Forward path transport follows reconstructed edges, not fresh storage. -/
theorem path_forward (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    {a b : Slot table} (path : FiniteWorklist.Path (successors graph) a b) :
    FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) (retain table extra b) := by
  induction path with
  | nil a => exact .nil _
  | cons edge rest ih =>
    exact .cons (by rw [successors_retained]; exact List.mem_map_of_mem edge) ih

/-- Every path starting in old storage stays there and comes from an old path. -/
theorem path_origin (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (a : Slot table) (target : Slot (table ++ extra))
    (path : FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) target) :
    ∃ b : Slot table, target = retain table extra b ∧
      FiniteWorklist.Path (successors graph) a b := by
  generalize h : retain table extra a = start at path
  induction path generalizing a with
  | nil start => exact ⟨a,h.symm,.nil _⟩
  | @cons start middle target edge rest ih =>
    rw [← h, successors_retained] at edge
    obtain ⟨old, member, same⟩ := List.mem_map.mp edge
    obtain ⟨b, endSame, oldPath⟩ := ih old same
    exact ⟨b,endSame,.cons member oldPath⟩

/-- No old path is added or lost by allocating any finite suffix. -/
theorem path_exact (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (a b : Slot table) :
    FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) (retain table extra b) ↔
        FiniteWorklist.Path (successors graph) a b := by
  constructor
  · intro path
    obtain ⟨old, same, original⟩ := path_origin table extra graph fresh a _ path
    have eq := retain_injective table extra same
    subst old
    exact original
  · exact path_forward table extra graph fresh

/-- Exact semantic preservation includes cycles through nominal arguments. -/
theorem structural_cycle_exact (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    StructuralCycleAt (grow table extra graph fresh) (retain table extra root) ↔
      StructuralCycleAt graph root := by
  cases found : graph root with
  | unresolved => simp [StructuralCycleAt, found, mapNode]
  | scalar name => simp [StructuralCycleAt, found, mapNode]
  | nominal name children => simp [StructuralCycleAt, found, mapNode]
  | structural name children =>
    simp only [StructuralCycleAt, grow_retained, found, mapNode, Node.structural.injEq]
    constructor
    · rintro ⟨other, otherChildren, ⟨sameName,sameChildren⟩, next, member, path⟩
      subst other
      subst otherChildren
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
      subst next
      exact ⟨name,children,⟨rfl,rfl⟩,old,oldMember,(path_exact ..).mp path⟩
    · rintro ⟨other, otherChildren, ⟨sameName,sameChildren⟩, next, member, path⟩
      subst other
      subst otherChildren
      exact ⟨name,children.map (retain table extra),⟨rfl,rfl⟩,
        retain table extra next,List.mem_map_of_mem member,path_forward table extra graph fresh path⟩

/-- The actual finite reachability test gives the same direct-cycle answer. -/
theorem recursiveAt_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    recursiveAt (grow table extra graph fresh) (retain table extra root) =
      recursiveAt graph root := by
  apply Bool.eq_iff_iff.mpr
  rw [recursive_at_exact,recursive_at_exact,structural_cycle_exact]

/-- Every finite depth, including arbitrarily many turns around a cycle, agrees. -/
theorem observe_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (depth : Nat) (root : Slot table) :
    observe (grow table extra graph fresh) depth (retain table extra root) =
      observe graph depth root := by
  induction depth generalizing root with
  | zero => rfl
  | succ depth ih =>
    simp only [observe, grow_retained]
    cases graph root <;> simp [mapNode, List.map_map, ih]

/-- Old source canonicalization and reconstructed graph observation commute. -/
theorem canonical_observe_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (depth : Nat) (root : Slot table) :
    observe (grow table extra graph fresh) depth
      (canonical (table ++ extra) (retain table extra root)) =
        observe graph depth (canonical table root) := by
  rw [canonical_retained,observe_retained]

theorem canonical_cycle_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    recursiveAt (grow table extra graph fresh)
      (canonical (table ++ extra) (retain table extra root)) =
        recursiveAt graph (canonical table root) := by
  rw [canonical_retained,recursiveAt_retained]

open CommonRoleGraphBisimulation

private theorem children_reindex (f : Fin n → Fin m) (old : Relation n)
    (new : Relation m) (correspond : ∀ a b, (f a,f b) ∈ new ↔ (a,b) ∈ old)
    (xs ys : List (Fin n)) :
    childrenRelated new (xs.map f) (ys.map f) ↔ childrenRelated old xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [childrenRelated]
  | cons a xs ih => cases ys <;> simp [childrenRelated,correspond,ih]

private theorem node_reindex (f : Fin n → Fin m) (injective : Function.Injective f)
    (old : Relation n) (new : Relation m)
    (correspond : ∀ a b, (f a,f b) ∈ new ↔ (a,b) ∈ old)
    (a b : Fin n) (x y : Node n) :
    nodeRelated new (f a) (f b) (mapNode f x) (mapNode f y) ↔
      nodeRelated old a b x y := by
  cases x <;> cases y <;> simp [nodeRelated,mapNode,
    children_reindex f old new correspond,injective.eq_iff]

private def lifted (table extra : Table) (relation : Relation table.length) :
    Relation (table ++ extra).length :=
  (allPairs (table ++ extra).length).filter fun p =>
    decide (p ∈ relation.map fun q => (retain table extra q.1,retain table extra q.2))

private theorem lifted_exact (table extra : Table) (relation : Relation table.length)
    (a b : Slot table) :
    (retain table extra a,retain table extra b) ∈ lifted table extra relation ↔
      (a,b) ∈ relation := by
  simp only [lifted,List.mem_filter,mem_all_pairs,true_and,decide_eq_true_eq,List.mem_map]
  constructor
  · rintro ⟨⟨x,y⟩,member,equal⟩
    have ha := retain_injective table extra (Prod.mk.inj equal).1
    have hb := retain_injective table extra (Prod.mk.inj equal).2
    change x = a at ha
    change y = b at hb
    subst x
    subst y
    exact member
  · intro member
    exact ⟨(a,b),member,rfl⟩

private def lowered (table extra : Table) (relation : Relation (table ++ extra).length) :
    Relation table.length :=
  (allPairs table.length).filter fun p =>
    decide ((retain table extra p.1,retain table extra p.2) ∈ relation)

private theorem lowered_exact (table extra : Table)
    (relation : Relation (table ++ extra).length) (a b : Slot table) :
    (a,b) ∈ lowered table extra relation ↔
      (retain table extra a,retain table extra b) ∈ relation := by
  simp [lowered,mem_all_pairs]

/-- Bisimulation between old nodes is unchanged, even with arbitrary fresh nodes.
The finite witnesses are constructed in both directions. -/
theorem bisimilar_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (a b : Slot table) :
    Bisimilar (grow table extra graph fresh) (retain table extra a) (retain table extra b) ↔
      Bisimilar graph a b := by
  constructor
  · rintro ⟨relation,_,member,valid⟩
    refine ⟨lowered table extra relation,List.filter_sublist,
      (lowered_exact ..).mpr member,?_⟩
    intro p hp
    have expanded := valid (retain table extra p.1,retain table extra p.2)
      ((lowered_exact ..).mp hp)
    simp only [grow_retained] at expanded
    exact (node_reindex (retain table extra) (retain_injective table extra)
      (lowered table extra relation) relation
      (fun x y => (lowered_exact table extra relation x y).symm) p.1 p.2 _ _).mp expanded
  · rintro ⟨relation,_,member,valid⟩
    refine ⟨lifted table extra relation,List.filter_sublist,
      (lifted_exact ..).mpr member,?_⟩
    intro p hp
    have mapped := (List.mem_filter.mp hp).2
    simp only [decide_eq_true_eq,List.mem_map] at mapped
    obtain ⟨q,hq,rfl⟩ := mapped
    simp only [grow_retained]
    exact (node_reindex (retain table extra) (retain_injective table extra)
      relation (lifted table extra relation) (lifted_exact table extra relation)
      q.1 q.2 _ _).mpr (valid q hq)

/-- Fresh source storage starts unresolved; aliases still use canonical old roots. -/
def allocate (table extra : Table) (graph : Graph table.length) :
    Graph (table ++ extra).length := grow table extra graph (fun _ => .unresolved)

private theorem structural_origin (table extra : Table) (graph : Graph table.length)
    (node : Slot (table ++ extra)) (name : Nat) (children : List (Slot (table ++ extra)))
    (structural : allocate table extra graph node = .structural name children) :
    ∃ old : Slot table, node = retain table extra old := by
  unfold allocate grow at structural
  split at structural
  · rename_i h
    exact ⟨⟨node.val,h⟩,Fin.ext rfl⟩
  · cases structural

/-- Allocation of unresolved storage preserves the full bisimulation-based K2
snapshot, including finite unrollings of existing cycles. -/
theorem regularAt_allocated (table extra : Table) (graph : Graph table.length)
    (root : Slot table) :
    regularAt (allocate table extra graph) (retain table extra root) =
      regularAt graph root := by
  apply Bool.eq_iff_iff.mpr
  rw [regular_at_exact,regular_at_exact]
  unfold RegularAt
  constructor
  · intro h
    rcases h with direct | ⟨head,other,cycle,similar⟩
    · exact Or.inl ((structural_cycle_exact ..).mp direct)
    · obtain ⟨name,children,found,next,member,path⟩ := cycle
      obtain ⟨old,rfl⟩ := structural_origin table extra graph other name children found
      refine Or.inr ⟨?_,old,?_,(bisimilar_retained ..).mp similar⟩
      · cases hroot : graph root <;>
          simp [allocate,grow_retained,hroot,mapNode] at head ⊢
      · exact (structural_cycle_exact ..).mp ⟨name,children,found,next,member,path⟩
  · intro h
    rcases h with direct | ⟨head,other,cycle,similar⟩
    · exact Or.inl ((structural_cycle_exact ..).mpr direct)
    · refine Or.inr ⟨?_,retain table extra other,
        (structural_cycle_exact ..).mpr cycle,(bisimilar_retained ..).mpr similar⟩
      obtain ⟨name,children,found⟩ := head
      exact ⟨name,children.map (retain table extra),by simp [allocate,found,mapNode]⟩

open CommonRoleGraphInspection
open CommonRoleCanonicalSourceGrowth (retainObservation)

private theorem retain_combine (table extra : Table) (a b : Observation table.length) :
    retainObservation table extra (combine a b) =
      combine (retainObservation table extra a) (retainObservation table extra b) := by
  cases a <;> cases b <;> simp [combine,retainObservation,List.map_append]

mutual
  /-- Every actual head pattern preserves its exact result and capture order.
  The statement includes unresolved nodes, recursive graphs and nominal arguments. -/
  theorem inspect_allocated (table extra : Table) (graph : Graph table.length)
      (pattern : Pattern) (root : Slot table) :
      inspect (allocate table extra graph) pattern (retain table extra root) =
        retainObservation table extra (inspect graph pattern root) := by
    cases pattern with
    | «variable» name => simp [inspect,retainObservation]
    | shared names => simp [inspect,retainObservation,List.map_map]
    | scalar expected =>
      simp only [inspect,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp [mapNode,retainObservation]
        split <;> rfl
    | structural expected patterns =>
      simp only [inspect,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp only [mapNode,retainObservation]
        all_goals try rfl
        split
        · exact inspectChildren_allocated table extra graph patterns _
        · rfl
    | nominal expected patterns =>
      simp only [inspect,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp only [mapNode,retainObservation]
        all_goals try rfl
        split
        · exact inspectChildren_allocated table extra graph patterns _
        · rfl
  termination_by sizeOf pattern

  theorem inspectChildren_allocated (table extra : Table) (graph : Graph table.length)
      (patterns : List Pattern) (roots : List (Slot table)) :
      inspectChildren (allocate table extra graph) patterns (roots.map (retain table extra)) =
        retainObservation table extra (inspectChildren graph patterns roots) := by
    cases patterns with
    | nil => cases roots <;> simp [inspectChildren,retainObservation]
    | cons pattern patterns =>
      cases roots with
      | nil => simp [inspectChildren,retainObservation]
      | cons root roots =>
        simp only [List.map_cons,inspectChildren]
        rw [inspect_allocated,inspectChildren_allocated,retain_combine]
  termination_by sizeOf patterns
end

mutual
  /-- The all-siblings inspector preserves later observations after mismatches. -/
  theorem inspectAll_allocated (table extra : Table) (graph : Graph table.length)
      (pattern : Pattern) (root : Slot table) :
      inspectAll (allocate table extra graph) pattern (retain table extra root) =
        (inspectAll graph pattern root).map (retainObservation table extra) := by
    cases pattern with
    | «variable» name => simp [inspectAll,retainObservation]
    | shared names => simp [inspectAll,retainObservation,List.map_map]
    | scalar expected =>
      simp only [inspectAll,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp [mapNode,retainObservation]
        split <;> rfl
    | structural expected patterns =>
      simp only [inspectAll,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp only [mapNode,retainObservation,List.map_cons,List.map_nil]
        all_goals try rfl
        split
        · exact inspectAllChildren_allocated table extra graph patterns _
        · rfl
    | nominal expected patterns =>
      simp only [inspectAll,regularAt_allocated]
      split
      · rfl
      · simp only [allocate,grow_retained]
        cases graph root <;> simp only [mapNode,retainObservation,List.map_cons,List.map_nil]
        all_goals try rfl
        split
        · exact inspectAllChildren_allocated table extra graph patterns _
        · rfl
  termination_by sizeOf pattern

  theorem inspectAllChildren_allocated (table extra : Table) (graph : Graph table.length)
      (patterns : List Pattern) (roots : List (Slot table)) :
      inspectAllChildren (allocate table extra graph) patterns (roots.map (retain table extra)) =
        (inspectAllChildren graph patterns roots).map (retainObservation table extra) := by
    cases patterns with
    | nil => cases roots <;> simp [inspectAllChildren,retainObservation]
    | cons pattern patterns =>
      cases roots with
      | nil => simp [inspectAllChildren,retainObservation]
      | cons root roots =>
        simp only [List.map_cons,inspectAllChildren]
        rw [inspectAll_allocated,inspectAllChildren_allocated,List.map_append]
  termination_by sizeOf patterns
end

/-- Canonical old roots keep the entire inspector observation after allocation. -/
theorem canonical_inspect_allocated (table extra : Table) (graph : Graph table.length)
    (pattern : Pattern) (root : Slot table) :
    inspect (allocate table extra graph) pattern
      (canonical (table ++ extra) (retain table extra root)) =
        retainObservation table extra (inspect graph pattern (canonical table root)) := by
  rw [canonical_retained,inspect_allocated]

theorem inspectAllVisible_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectAllVisible (allocate table extra graph) role (retain table extra root) visible =
      (inspectAllVisible graph role root visible).map
        (fun p => (p.1,p.2.map (retainObservation table extra))) := by
  induction visible with
  | nil => rfl
  | cons head rest ih =>
    simp only [inspectAllVisible,List.filterMap_cons] at ih ⊢
    split <;> simp_all [inspectAll_allocated]

/-- Transport a complete snapshot without losing head order or duplicates. -/
def retainSnapshot (table extra : Table) : Snapshot table.length → Snapshot (table ++ extra).length
  | .unknown => .unknown
  | .cycle node => .cycle (retain table extra node)
  | .heads heads => .heads (heads.map fun p => (p.1,p.2.map (retainObservation table extra)))

/-- The existing full snapshot entry point commutes with allocation. -/
theorem snapshot_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectSnapshot (allocate table extra graph) role (retain table extra root) visible =
      retainSnapshot table extra (inspectSnapshot graph role root visible) := by
  have node := grow_retained table extra graph (fun _ => .unresolved) root
  change allocate table extra graph (retain table extra root) = _ at node
  simp only [inspectSnapshot,node,regularAt_allocated]
  cases graph root <;> simp only [mapNode]
  · rfl
  all_goals split
  all_goals try rfl
  all_goals simp [retainSnapshot,inspectAllVisible_allocated]

/-- Exact canonical snapshot after both root routing and graph reconstruction. -/
theorem canonical_snapshot_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectSnapshot (allocate table extra graph) role
      (canonical (table ++ extra) (retain table extra root)) visible =
        retainSnapshot table extra (inspectSnapshot graph role (canonical table root) visible) := by
  rw [canonical_retained,snapshot_allocated]

/-- A finite unrolling with a shared unknown keeps its cycle encounter after
new aliases and fresh unknown source names are allocated. -/
theorem unrolling_allocation_regression :
    inspect (allocate [7,7,9] [9,7,11] unrolledWithSharedUnknown)
      (.structural 0 [.variable 3,.variable 4]) (retain [7,7,9] [9,7,11] 0) =
        .cycle (retain [7,7,9] [9,7,11] 0) := by
  rw [inspect_allocated]
  have regular := unrolled_shared_unknown_detected.2
  simp [inspect,regular,retainObservation]

/-- New raw storage begins unknown. Its source root may instead be an old alias. -/
theorem allocate_new_unresolved (table extra : Table) (graph : Graph table.length)
    (i : Slot extra) :
    allocate table extra graph (CommonRoleCanonicalSourceGrowth.allocated table extra i) =
      .unresolved := by
  have h : ¬ table.length + i.val < table.length := by omega
  simp [allocate,grow,CommonRoleCanonicalSourceGrowth.allocated,h]

/-- An allocated alias immediately reuses the old canonical head observation. -/
theorem new_alias_inspection (table extra : Table) (graph : Graph table.length)
    (pattern : Pattern) (old : Slot table) (new : Slot extra)
    (same : CommonRoleSourceIdentity.source extra new = CommonRoleSourceIdentity.source table old) :
    inspect (allocate table extra graph) pattern
      (CommonRoleCanonicalSourceGrowth.newRoot table extra new) =
        retainObservation table extra (inspect graph pattern (canonical table old)) := by
  rw [CommonRoleCanonicalSourceGrowth.newRoot_exact,
    CommonRoleCanonicalSourceGrowth.allocated_alias_root table extra old new same,
    inspect_allocated]

/-- A genuinely new source name starts unknown at its computed canonical root;
no external root or graph correctness premise is required. -/
theorem fresh_snapshot_unknown (table extra : Table) (graph : Graph table.length)
    (role : Nat) (new : Slot extra) (visible : List VisibleHead)
    (fresh : CommonRoleSourceDescent.representative table
      (CommonRoleSourceIdentity.source extra new) = none) :
    inspectSnapshot (allocate table extra graph) role
      (CommonRoleCanonicalSourceGrowth.newRoot table extra new) visible = .unknown := by
  rw [CommonRoleCanonicalSourceGrowth.newRoot_exact,
    CommonRoleCanonicalSourceGrowth.allocated_fresh_root table extra new fresh]
  exact (snapshot_unknown_exact ..).mpr (allocate_new_unresolved ..)

end Yulang.CommonRoleAllocatedGraph
