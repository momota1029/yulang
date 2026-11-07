import Yulang.CommonGeneratedChildClosure

/-!
# Finite closure of ordinary comparisons on the original common node pool

The inventory contains all pairs of original node IDs. Each round propagates
variable bounds, symbolically inspects the resulting rigid comparisons, adds
their ordinary child edges to the existing edges, and removes duplicates.
An internal inventory-size bound suffices: every nonterminal round strictly
increases the number of distinct edges. The public construction takes no
fuel, closure certificate, row/value assignment or success premise.

This closes ordinary edges only. Row, presence and profile checks remain
separate constraints, and the original edges are retained. The semantic
preservation theorem below is not an all-parameter solution theorem.
-/

namespace Yulang.CommonOrdinaryEdgeClosure

open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceVariableBounds (template)
open CommonGeneratedChildClosure (EndpointGrammar CheckGrammar childEdges)
open CommonGeneratedRigidInspection (inspectSlot)
open CommonPresenceConstraintGraph (EdgesHold Realizes rowEval splitAtoms compile)
open TypeConstraintGraph (unique mem_unique unique_nodup)
open CommonSymbolicConstraints (Branch Check)

variable {m : Nat}

abbrev Edges (pool : Pool m) := List (Fin pool.size × Fin pool.size)

/-- The complete ordinary-edge inventory is constructed from the pool. -/
def inventory (pool : Pool m) : Edges pool :=
  (List.finRange pool.size).flatMap fun first =>
    (List.finRange pool.size).map fun last => (first, last)

theorem inventory_member (pool : Pool m) (edge : Fin pool.size × Fin pool.size) :
    edge ∈ inventory pool :=
  List.mem_flatMap.mpr ⟨edge.1, List.mem_finRange _,
    List.mem_map.mpr ⟨edge.2, List.mem_finRange _, rfl⟩⟩

theorem inventory_length (pool : Pool m) : (inventory pool).length = pool.size * pool.size := by
  have productLength (first last : List (Fin pool.size)) :
      (first.flatMap fun a => last.map fun b => (a, b)).length = first.length * last.length := by
    induction first with
    | nil => simp
    | cons head rest ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]
  simpa only [inventory, List.length_finRange] using
    productLength (List.finRange pool.size) (List.finRange pool.size)

theorem nodup_length_bound (pool : Pool m) (edges : Edges pool) (distinct : edges.Nodup) :
    edges.length ≤ pool.size * pool.size := by
  rw [← inventory_length]
  exact distinct.length_le_of_subset (fun _ _ => inventory_member pool _)

def residualChecks (pool : Pool m) (edges : Edges pool) : CommonGeneratedRigidInspection.Checks pool :=
  (CommonBoundCoalescing.rigidComparisons (template pool edges)).flatMap (inspectSlot pool)

def step (pool : Pool m) (edges : Edges pool) : Edges pool :=
  unique (edges ++ childEdges (residualChecks pool edges))

theorem step_contains (pool : Pool m) (edges : Edges pool) : edges ⊆ step pool edges := by
  intro edge member
  exact (mem_unique _ _).mpr (List.mem_append_left _ member)

theorem step_nodup (pool : Pool m) (edges : Edges pool) : (step pool edges).Nodup := unique_nodup _

theorem step_length_bound (pool : Pool m) (edges : Edges pool) :
    (step pool edges).length ≤ pool.size * pool.size :=
  nodup_length_bound pool _ (step_nodup pool edges)

def Closed (pool : Pool m) (edges : Edges pool) : Prop := step pool edges ⊆ edges

private theorem reverse_subset_of_length {first last : List α}
    (distinct : first.Nodup) (included : first ⊆ last) (lengths : last.length ≤ first.length) :
    last ⊆ first := by
  intro value member
  classical
  by_cases present : value ∈ first
  · exact present
  have missing := present
  have longer : (value :: first).Nodup := List.nodup_cons.mpr ⟨missing, distinct⟩
  have inside : value :: first ⊆ last := by
    intro actual present
    exact (List.mem_cons.mp present).elim (fun same => same ▸ member) (fun inside => included inside)
  have bounded := longer.length_le_of_subset inside
  simp only [List.length_cons] at bounded
  omega

private theorem closed_of_length (pool : Pool m) (edges : Edges pool) (distinct : edges.Nodup)
    (lengths : (step pool edges).length ≤ edges.length) : Closed pool edges :=
  reverse_subset_of_length distinct (step_contains pool edges) lengths

private def iterate (pool : Pool m) : Nat → Edges pool → Edges pool
  | 0, edges => edges
  | rounds + 1, edges =>
      if (step pool edges).length = edges.length then edges else iterate pool rounds (step pool edges)

private theorem iterate_nodup (pool : Pool m) (rounds : Nat) (edges : Edges pool)
    (distinct : edges.Nodup) : (iterate pool rounds edges).Nodup := by
  induction rounds generalizing edges with
  | zero => exact distinct
  | succ rounds ih =>
      simp only [iterate]
      split
      · exact distinct
      · exact ih _ (step_nodup pool edges)

private theorem iterate_contains (pool : Pool m) (rounds : Nat) (edges : Edges pool) :
    edges ⊆ iterate pool rounds edges := by
  induction rounds generalizing edges with
  | zero => exact List.Subset.refl _
  | succ rounds ih =>
      simp only [iterate]
      split
      · exact List.Subset.refl _
      · exact List.Subset.trans (step_contains pool edges) (ih _)

private theorem iterate_closed (pool : Pool m) (rounds : Nat) (edges : Edges pool)
    (distinct : edges.Nodup) (enough : pool.size * pool.size ≤ edges.length + rounds) :
    Closed pool (iterate pool rounds edges) := by
  induction rounds generalizing edges with
  | zero =>
      exact closed_of_length pool edges distinct (by have bound := step_length_bound pool edges; omega)
  | succ rounds ih =>
      simp only [iterate]
      split
      · rename_i same
        exact closed_of_length pool edges distinct (Nat.le_of_eq same)
      · rename_i different
        apply ih _ (step_nodup pool edges)
        have growing := distinct.length_le_of_subset (step_contains pool edges)
        omega

/-- At most the internally computed N² growth rounds are required. -/
def ordinaryEdgeClosure (pool : Pool m) (edges : Edges pool) : Edges pool :=
  iterate pool (pool.size * pool.size) (unique edges)

theorem ordinary_edge_closure_nodup (pool : Pool m) (edges : Edges pool) :
    (ordinaryEdgeClosure pool edges).Nodup := iterate_nodup pool _ _ (unique_nodup edges)

theorem ordinary_edge_closure_bound (pool : Pool m) (edges : Edges pool) :
    (ordinaryEdgeClosure pool edges).length ≤ pool.size * pool.size :=
  nodup_length_bound pool _ (ordinary_edge_closure_nodup pool edges)

theorem ordinary_edge_closure_contains (pool : Pool m) (edges : Edges pool) :
    edges ⊆ ordinaryEdgeClosure pool edges := by
  intro edge member
  exact iterate_contains pool _ _ ((mem_unique _ _).mpr member)

theorem ordinary_edge_closure_closed (pool : Pool m) (edges : Edges pool) :
    Closed pool (ordinaryEdgeClosure pool edges) :=
  iterate_closed pool _ _ (unique_nodup edges) (by omega)

/-- Fixed point as a finite graph, independent of list ordering. -/
theorem ordinary_edge_closure_fixedpoint (pool : Pool m) (edges : Edges pool)
    (edge : Fin pool.size × Fin pool.size) :
    edge ∈ step pool (ordinaryEdgeClosure pool edges) ↔ edge ∈ ordinaryEdgeClosure pool edges :=
  ⟨fun member => ordinary_edge_closure_closed pool edges member,
    fun member => step_contains pool _ member⟩

theorem ordinary_edge_closure_children (pool : Pool m) (edges : Edges pool) :
    childEdges (residualChecks pool (ordinaryEdgeClosure pool edges)) ⊆ ordinaryEdgeClosure pool edges := by
  intro edge member
  exact ordinary_edge_closure_closed pool edges
    ((mem_unique _ _).mpr (List.mem_append_right _ member))

theorem residualChecks_grammar (pool : Pool m) (edges : Edges pool)
    (grammar : EndpointGrammar pool edges) :
    ∀ check ∈ residualChecks pool edges, CheckGrammar pool check := by
  intro check member
  obtain ⟨edge, included, emitted⟩ := List.mem_flatMap.mp member
  have shape := CommonGeneratedChildClosure.residual_endpoint_grammar pool edges grammar edge included
  exact CommonGeneratedChildClosure.inspectSlot_preserves_grammar pool edge shape.1 shape.2 check emitted

theorem step_grammar (pool : Pool m) (edges : Edges pool) (grammar : EndpointGrammar pool edges) :
    EndpointGrammar pool (step pool edges) := by
  intro edge member
  have present := (mem_unique _ _).mp member
  exact (List.mem_append.mp present).elim (grammar edge)
    (CommonGeneratedChildClosure.childEdges_preserves_grammar pool _
      (residualChecks_grammar pool edges grammar) edge)

private theorem iterate_grammar (pool : Pool m) (rounds : Nat) (edges : Edges pool)
    (grammar : EndpointGrammar pool edges) : EndpointGrammar pool (iterate pool rounds edges) := by
  induction rounds generalizing edges with
  | zero => exact grammar
  | succ rounds ih =>
      simp only [iterate]
      split
      · exact grammar
      · exact ih _ (step_grammar pool edges grammar)

theorem ordinary_edge_closure_grammar (pool : Pool m) (edges : Edges pool)
    (grammar : EndpointGrammar pool edges) : EndpointGrammar pool (ordinaryEdgeClosure pool edges) := by
  apply iterate_grammar
  intro edge member
  exact grammar edge ((mem_unique _ _).mp member)

theorem generated_closure_grammar (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (ordinaryEdgeClosure (splitAtoms clause.pack).pool (compile clause.pack).edges) :=
  ordinary_edge_closure_grammar _ _ (CommonGeneratedChildClosure.compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member))

theorem generated_core_closure_grammar (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    EndpointGrammar (splitAtoms clause.pack).pool
      (ordinaryEdgeClosure (splitAtoms clause.pack).pool (compile clause.pack).edges) :=
  ordinary_edge_closure_grammar _ _ (CommonGeneratedChildClosure.compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member))

theorem childEdges_sound (pool : Pool m) (checks : CommonGeneratedRigidInspection.Checks pool)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (valid : Branch.Holds (rowEval rows) values values checks) : EdgesHold (childEdges checks) values := by
  intro edge member
  obtain ⟨check, included, contributed⟩ := List.mem_flatMap.mp member
  have checked := valid check included
  cases check with
  | childBelow first last =>
      cases first with
      | ref first =>
          cases last with
          | ref last =>
              have same := List.mem_singleton.mp contributed
              subst edge
              exact checked
          | _ => cases contributed
      | _ => cases contributed
  | rowBelow | flag | profileBelow => cases contributed

theorem residualChecks_sound (pool : Pool m) (edges : Edges pool) (grammar : EndpointGrammar pool edges)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) :
    Branch.Holds (rowEval rows) values values (residualChecks pool edges) := by
  have residual : EdgesHold (CommonBoundCoalescing.rigidComparisons (template pool edges)) values :=
    (CommonBoundCoalescing.consistent_iff_satisfiable values (template pool edges)).mpr
      ⟨CommonPresenceConstraintGraph.restrict pool values,
        CommonPresenceVariableBounds.models_of_edges pool edges values valid⟩
  have shapes := CommonGeneratedChildClosure.endpoint_head_shapes pool _
    (CommonGeneratedChildClosure.residual_endpoint_grammar pool edges grammar)
  apply (CommonSymbolicConstraints.holds_flatMap (rowEval rows) values values _ _).mpr
  intro edge member
  exact (CommonGeneratedRigidInspection.inspect_slot_exact pool edge (shapes edge member).1
    (shapes edge member).2 rows values realizes).mpr (residual edge member)

theorem step_sound (pool : Pool m) (edges : Edges pool) (grammar : EndpointGrammar pool edges)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) :
    EdgesHold (step pool edges) values := by
  intro edge member
  have present := (mem_unique _ _).mp member
  exact (List.mem_append.mp present).elim (valid edge)
    (childEdges_sound pool _ rows values (residualChecks_sound pool edges grammar rows values realizes valid) edge)

theorem step_exact (pool : Pool m) (edges : Edges pool) (grammar : EndpointGrammar pool edges)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : Realizes pool rows values) :
    EdgesHold (step pool edges) values ↔ EdgesHold edges values :=
  ⟨fun valid edge member => valid edge (step_contains pool edges member),
    step_sound pool edges grammar rows values realizes⟩

private theorem iterate_exact (pool : Pool m) (rounds : Nat) (edges : Edges pool)
    (grammar : EndpointGrammar pool edges) (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : Realizes pool rows values) :
    EdgesHold (iterate pool rounds edges) values ↔ EdgesHold edges values := by
  induction rounds generalizing edges with
  | zero => rfl
  | succ rounds ih =>
      simp only [iterate]
      split
      · rfl
      · exact (ih _ (step_grammar pool edges grammar)).trans (step_exact pool edges grammar rows values realizes)

/-- Under the independent original constructor equations, the accumulated
ordinary comparisons preserve and reflect all original edge assignments. -/
theorem ordinary_edge_closure_exact (pool : Pool m) (edges : Edges pool)
    (grammar : EndpointGrammar pool edges) (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : Realizes pool rows values) :
    EdgesHold (ordinaryEdgeClosure pool edges) values ↔ EdgesHold edges values := by
  have retained : EndpointGrammar pool (unique edges) :=
    fun edge member => grammar edge ((mem_unique _ _).mp member)
  exact (iterate_exact pool _ _ retained rows values realizes).trans (by simp [EdgesHold])

theorem generated_closure_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Common.Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Common.Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values) :
    EdgesHold (ordinaryEdgeClosure (splitAtoms clause.pack).pool (compile clause.pack).edges) values ↔
      EdgesHold (compile clause.pack).edges values :=
  ordinary_edge_closure_exact _ _ (CommonGeneratedChildClosure.compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member)) rows values realizes

theorem generated_core_closure_exact (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Common.Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Common.Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values) :
    EdgesHold (ordinaryEdgeClosure (splitAtoms clause.pack).pool (compile clause.pack).edges) values ↔
      EdgesHold (compile clause.pack).edges values :=
  ordinary_edge_closure_exact _ _ (CommonGeneratedChildClosure.compiled_endpoint_grammar clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member)) rows values realizes

end Yulang.CommonOrdinaryEdgeClosure
