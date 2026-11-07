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
open CommonBoundRefInspection (LowerRef UpperRef)

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

/-- A syntactic invariant on the original lower and upper endpoints. It is
not part of the executable state or the independent model interpretation. -/
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

/-- Variable flow only selects lower and upper endpoints already present
in the template, including paths and cycles in its shared variable graph. -/
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
  exact CommonBoundRefInspection.inspected_child_polarity pool edge.1.val edge.2.val first last
    original included child.1.val child.2.val
    (CommonBoundRefBranches.splitBranch_child_origin pool (queries pool) original _ child member)

theorem preserve_grammar (pool : Pool m) (current : List (Edge pool))
    (grammar : Grammar pool current) (edge : Edge pool) (member : edge ∈ rigid pool current)
    (branch : Branch pool) (returned : branch ∈ inspect pool edge) :
    Grammar pool (branch.children ++ current) := by
  have shape := rigid_grammar pool current grammar edge member
  exact (inspect_grammar pool edge shape.1 shape.2 branch returned).append grammar

/-- Every returned branch retains the recursive endpoint syntax invariant.
No semantic slot assignment or successful model is needed for this fact. -/
theorem run_grammar (pool : Pool m) (edges : List (Edge pool)) (grammar : Grammar pool edges)
    (final : State pool) (returned : final ∈ run pool edges) : Grammar pool final.edges :=
  FiniteBranchingWorklist.run_preserves (inventory pool) (rigid pool) (inspect pool)
    (Grammar pool) (preserve_grammar pool) edges [] grammar final returned

theorem inspect_aux_origin (pool : Pool m) (edge : Edge pool) (branch : Branch pool)
    (returned : branch ∈ inspect pool edge) (item : Aux pool) (present : item ∈ branch.aux) :
    ∃ original ∈ CommonBoundRefInspection.inspect pool edge.1.val edge.2.val, item ∈ original := by
  obtain ⟨⟨original, included⟩, _, rfl⟩ := List.mem_map.mp returned
  exact ⟨original, included,
    CommonBoundRefBranches.splitBranch_aux_origin pool (queries pool) original _ item present⟩

theorem inspect_auxiliary (pool : Pool m) (edge : Edge pool) (branch : Branch pool)
    (returned : branch ∈ inspect pool edge) (item : Aux pool) (present : item ∈ branch.aux) :
    CommonBoundRefBranches.Auxiliary item := by
  obtain ⟨⟨original, _⟩, _, rfl⟩ := List.mem_map.mp returned
  exact CommonBoundRefBranches.splitBranch_auxiliary pool (queries pool) original _ item present

/-- Auxiliary checks contain original row comparisons or the literal true.
In particular they contain no profile, dynamic Boolean, or false literal. -/
def RowOrTrue (item : Aux pool) : Prop :=
  match item with
  | .rowBelow _ _ => True
  | .flag (.literal value) => value = true
  | _ => False

theorem inspect_row_or_true (pool : Pool m) (edge : Edge pool) (branch : Branch pool)
    (returned : branch ∈ inspect pool edge) (item : Aux pool) (present : item ∈ branch.aux) :
    RowOrTrue item := by
  have auxiliary := inspect_auxiliary pool edge branch returned item present
  obtain ⟨original, included, emitted⟩ := inspect_aux_origin pool edge branch returned item present
  cases item with
  | rowBelow => trivial
  | flag expression =>
      cases expression with
      | literal value =>
          exact CommonBoundRefInspection.inspected_literal_true pool edge.1.val edge.2.val
            original included value emitted
      | _ => cases auxiliary
  | _ => cases auxiliary

theorem run_aux_origin (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) (item : Aux pool) (present : item ∈ final.aux) :
    ∃ edge branch, branch ∈ inspect pool edge ∧ item ∈ branch.aux := by
  have origin := FiniteBranchingWorklist.run_aux_origin (inventory pool) (rigid pool) (inspect pool)
    edges [] final returned item present
  exact origin.elim (fun impossible => False.elim (List.not_mem_nil impossible)) id

/-- This output property is unconditional, including for inputs outside the
generated grammar. Initial auxiliary constraints are empty by construction. -/
theorem run_row_or_true (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) (item : Aux pool) (present : item ∈ final.aux) :
    RowOrTrue item := by
  obtain ⟨edge, branch, included, emitted⟩ := run_aux_origin pool edges final returned item present
  exact inspect_row_or_true pool edge branch included item emitted

abbrev edgeHolds (pool : Pool m) (values : Fin pool.size → Common.Ty) :=
  CommonBoundRefBranches.edgeHolds pool (queries pool) values

abbrev auxHolds (pool : Pool m) (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty) :=
  CommonBoundRefBranches.auxHolds pool rows values

def EdgesHold (pool : Pool m) (values : Fin pool.size → Common.Ty) (edges : List (Edge pool)) : Prop :=
  ∀ edge ∈ edges, edgeHolds pool values edge

/-- The split inspector has the same independent meaning as its parent
comparison under the original constructor equations and pool-width invariant. -/
theorem inspect_models_exact (pool : Pool m) (edge : Edge pool)
    (first : LowerRef pool edge.1.val) (last : UpperRef pool edge.2.val)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (widths : CommonGeneratedWidth.PoolWidth pool values) :
    (∃ branch ∈ inspect pool edge, branch.Models (edgeHolds pool values) (auxHolds pool rows values)) ↔
      edgeHolds pool values edge :=
  (CommonBoundRefBranches.splitOutput_exact pool (queries pool) rows values _ _).trans
    (CommonBoundRefInspection.inspect_exact pool edge.1.val edge.2.val first last rows values realizes widths)

theorem extended_edge_exact (pool : Pool m) (rows : Fin m → Common.Row)
    (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values) (edge : Edge pool) :
    Common.Subtype
      (CommonOptionalPool.extendValues pool (queries pool) rows values
        (CommonBoundRefCoalescing.encode pool (queries pool) edge.1))
      (CommonOptionalPool.extendValues pool (queries pool) rows values
        (CommonBoundRefCoalescing.encode pool (queries pool) edge.2)) ↔
      edgeHolds pool values edge := by
  have same (index : Index pool) : Common.Equivalent
      (CommonOptionalPool.extendValues pool (queries pool) rows values
        (CommonBoundRefCoalescing.encode pool (queries pool) index))
      (index.val.eval values) := by
    simpa only [CommonOptionalPool.restrict_extend, CommonBoundRefCoalescing.encode] using
      CommonOptionalBoundEncoding.encode_exact pool (queries pool) rows
        (CommonOptionalPool.extendValues pool (queries pool) rows values)
        (CommonOptionalPool.extend_realizes pool (queries pool) rows values realizes) index.val index.property
  exact CommonSymbolicBoundInspection.subtype_congr (same edge.1) (same edge.2)

/-- The variable-flow pass entails its rigid comparisons for every original
constructor realizer. Its proof uses the exact, independent finite extension. -/
theorem rigid_sound (pool : Pool m) (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (edges : List (Edge pool)) (accepted : EdgesHold pool values edges) :
    EdgesHold pool values (rigid pool edges) := by
  have encoded : CommonBoundRefCoalescing.EdgesHold pool (queries pool)
      (CommonOptionalPool.extendValues pool (queries pool) rows values) edges := by
    intro edge member
    exact (extended_edge_exact pool rows values realizes edge).mpr (accepted edge member)
  have entailed := CommonBoundRefCoalescing.rigid_sound pool (queries pool)
    (CommonOptionalPool.extendValues pool (queries pool) rows values) edges encoded
  intro edge member
  exact (extended_edge_exact pool rows values realizes edge).mp (entailed edge member)

/-- For every independent row assignment and every original constructor
realizer satisfying pool width, the initial edges hold iff at least one
returned state models all its retained edges and auxiliary constraints.

The syntax invariant is an explicit theorem premise and is preserved by the
actual computation. No semantic law is stored in a state or its model. -/
theorem run_models_exact (pool : Pool m) (edges : List (Edge pool)) (grammar : Grammar pool edges)
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (widths : CommonGeneratedWidth.PoolWidth pool values) :
    EdgesHold pool values edges ↔
      ∃ final ∈ run pool edges, final.Models (edgeHolds pool values) (auxHolds pool rows values) := by
  have exactness := FiniteBranchingWorklist.run_models_exact_invariant
    (inventory pool) (rigid pool) (inspect pool) (Grammar pool) (preserve_grammar pool)
    (edgeHolds pool values) (auxHolds pool rows values)
    (fun current _ valid => rigid_sound pool rows values realizes current valid)
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

/-- Embedding initial source comparisons preserves each original shared
node ID; no auxiliary reference occurs in this initial edge list. -/
def originalEdges (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) : List (Edge pool) :=
  edges.map fun edge =>
    (CommonBoundRefCoalescing.original pool (queries pool) edge.1,
      CommonBoundRefCoalescing.original pool (queries pool) edge.2)

theorem original_edges_grammar (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (grammar : ∀ edge ∈ edges, PresenceGeneratedChildGrammar.lower (pool.termAt edge.1) = true ∧
      PresenceGeneratedChildGrammar.upper (pool.termAt edge.2) = true) :
    Grammar pool (originalEdges pool edges) := by
  intro edge member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  exact grammar original included

theorem original_edges_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (values : Fin pool.size → Common.Ty) :
    EdgesHold pool values (originalEdges pool edges) ↔ CommonPresenceConstraintGraph.EdgesHold edges values := by
  simp only [EdgesHold, originalEdges, List.forall_mem_map, edgeHolds, CommonBoundRefBranches.edgeHolds,
    CommonBoundRefCoalescing.original, CommonSymbolicBoundInspection.BoundRef.eval,
    CommonPresenceConstraintGraph.EdgesHold]

/-- The endpoint premise is supplied internally by the actual clause compiler. -/
theorem compiled_grammar (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms) :
    Grammar (CommonPresenceConstraintGraph.splitAtoms atoms).pool
      (originalEdges (CommonPresenceConstraintGraph.splitAtoms atoms).pool
        (CommonPresenceConstraintGraph.compile atoms).edges) := by
  apply original_edges_grammar
  intro edge member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  have shape := good (.tyLe original.val.1 original.val.2)
    ((CommonGeneratedRigidPool.split_type_member atoms original.val.1 original.val.2).mp original.property)
  simpa only [Pool.termAt_reference, PresenceGeneratedChildGrammar.GoodAtom] using shape

theorem generated_grammar (expression : Inference.Expr) (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    Grammar (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
      (originalEdges (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
        (CommonPresenceConstraintGraph.compile clause.pack).edges) :=
  compiled_grammar clause.pack (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member)

theorem generated_core_grammar (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    Grammar (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
      (originalEdges (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
        (CommonPresenceConstraintGraph.compile clause.pack).edges) :=
  compiled_grammar clause.pack (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member)

/-- The reverse semantic implication uses only retention of initial edges. -/
theorem run_models_retain_initial (pool : Pool m) (edges : List (Edge pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty) (final : State pool)
    (returned : final ∈ run pool edges)
    (models : final.Models (edgeHolds pool values) (auxHolds pool rows values)) :
    EdgesHold pool values edges :=
  fun edge included => models.1 edge (run_retains pool edges final returned included)

/-- For generated clauses the width premise of local optional inspection is
derived from the initial edges. It is not a premise of this equivalence. -/
theorem compiled_run_models_exact (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin m → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.splitAtoms atoms).pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes
      (CommonPresenceConstraintGraph.splitAtoms atoms).pool rows values) :
    CommonPresenceConstraintGraph.EdgesHold (CommonPresenceConstraintGraph.compile atoms).edges values ↔
      ∃ final ∈ run (CommonPresenceConstraintGraph.splitAtoms atoms).pool
          (originalEdges (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges),
        final.Models (edgeHolds (CommonPresenceConstraintGraph.splitAtoms atoms).pool values)
          (auxHolds (CommonPresenceConstraintGraph.splitAtoms atoms).pool rows values) := by
  constructor
  · intro accepted
    exact (run_models_exact _ _ (compiled_grammar atoms good) rows values realizes
      (CommonGeneratedWidth.compiled_pool_width atoms good widths rows values realizes accepted)).mp
      ((original_edges_exact _ _ values).mpr accepted)
  · rintro ⟨final, returned, models⟩
    exact (original_edges_exact _ _ values).mp
      (run_models_retain_initial _ _ rows values final returned models)

theorem generated_run_models_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes
      (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool rows values) :
    CommonPresenceConstraintGraph.EdgesHold (CommonPresenceConstraintGraph.compile clause.pack).edges values ↔
      ∃ final ∈ run (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
          (originalEdges (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
            (CommonPresenceConstraintGraph.compile clause.pack).edges),
        final.Models (edgeHolds (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool values)
          (auxHolds (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool rows values) :=
  compiled_run_models_exact clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_width_atoms expression clause member) rows values realizes

theorem generated_core_run_models_exact (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes
      (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool rows values) :
    CommonPresenceConstraintGraph.EdgesHold (CommonPresenceConstraintGraph.compile clause.pack).edges values ↔
      ∃ final ∈ run (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
          (originalEdges (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool
            (CommonPresenceConstraintGraph.compile clause.pack).edges),
        final.Models (edgeHolds (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool values)
          (auxHolds (CommonPresenceConstraintGraph.splitAtoms clause.pack).pool rows values) :=
  compiled_run_models_exact clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause member) rows values realizes

end Yulang.CommonBoundRefWorklist
