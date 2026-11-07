import Yulang.CommonSignedExpressionPool

/-! Real lower-bound graph compilation of every signed row-expression node.
Internal nodes are lower approximations; existential extension uses exact
expression evaluations. This does not yet pack whole formulas. -/
namespace Yulang.CommonSignedExpressionGraph
open Common (Row Occurrence rowLe)
open CommonEffectRequestGeneration (RowExpr)
open CommonSignedFlowFamily (Graph Edge Action)
open CommonSignedExpressionPool (Pool subterms evaluate extend restrict)

variable {scopes inputs : Nat}

def rawHead (scopes key : Nat) : Occurrence := (key, List.replicate scopes 0)

theorem head_member_iff (key : Nat) (occurrence : Occurrence) :
    (CommonSignedRows.commonAlgebra scopes).head key occurrence ↔ occurrence = rawHead scopes key := by
  have zeros : List.ofFn (fun _ : Fin scopes => (0 : Int)) = List.replicate scopes 0 := by
    apply List.ext_getElem
    · simp
    · intro index hi hj
      simp
  simp [CommonSignedRows.commonAlgebra, CommonSignedRows.embedRow,
    CommonSignedRows.encodeOccurrence, Directed.raw, rawHead, zeros, eq_comm]

theorem head_le_iff (key : Nat) (row : Row) :
    rowLe ((CommonSignedRows.commonAlgebra scopes).head key) row ↔ row (rawHead scopes key) := by
  constructor
  · intro included
    exact included _ ((head_member_iff _ _).mpr rfl)
  · intro member occurrence present
    have same := (head_member_iff _ _).mp present
    exact same ▸ member

def nodeValue (pool : Pool scopes inputs) (rows : Fin pool.size → Row)
    (expression : RowExpr scopes (Fin inputs)) (member : expression ∈ pool.terms) : Row :=
  match expression with
  | .var index => rows (pool.input index)
  | .empty => Common.rowEmpty
  | .head key => (CommonSignedRows.commonAlgebra scopes).head key
  | .union first last => Common.rowJoin
      (rows (pool.child _ member first (by simp [subterms])))
      (rows (pool.child _ member last (by simp [subterms])))
  | .protect scope permission body => CommonSignedRows.commonProtect scope.val permission.allows
      (rows (pool.child _ member body (by simp [subterms])))
  | .release scope permission body => CommonSignedRows.commonRelease scope.val permission.allows
      (rows (pool.child _ member body (by simp [subterms])))
  | .residual handled body => CommonSignedRows.commonResidual handled
      (rows (pool.child _ member body (by simp [subterms])))

def nodeEdges (pool : Pool scopes inputs) (expression : RowExpr scopes (Fin inputs))
    (member : expression ∈ pool.terms) : List (Edge pool.size) :=
  match expression with
  | .var _ | .empty | .head _ => []
  | .union first last =>
      [⟨pool.child _ member first (by simp [subterms]), pool.reference _ member, .identity⟩,
       ⟨pool.child _ member last (by simp [subterms]), pool.reference _ member, .identity⟩]
  | .protect scope permission body =>
      [⟨pool.child _ member body (by simp [subterms]), pool.reference _ member, .shift scope.val permission 1⟩]
  | .release scope permission body =>
      [⟨pool.child _ member body (by simp [subterms]), pool.reference _ member, .shift scope.val permission (-1)⟩]
  | .residual handled body =>
      [⟨pool.child _ member body (by simp [subterms]), pool.reference _ member, .residual handled⟩]

def nodeHeads (pool : Pool scopes inputs) (expression : RowExpr scopes (Fin inputs))
    (member : expression ∈ pool.terms) : List (Fin pool.size × Occurrence) :=
  match expression with
  | .head key => [(pool.reference _ member, rawHead scopes key)]
  | _ => []

def EdgesHold (edges : List (Edge slots)) (rows : Fin slots → Row) : Prop :=
  ∀ edge ∈ edges, ∀ source target, rows edge.source source → edge.action.run source = some target → rows edge.target target

def HeadsHold (heads : List (Fin slots × Occurrence)) (rows : Fin slots → Row) : Prop :=
  ∀ head ∈ heads, rows head.1 head.2

theorem identity_edge_iff (rows : Fin slots → Row) (source target : Fin slots) :
    (∀ a b, rows source a → Action.identity.run a = some b → rows target b) ↔ rowLe (rows source) (rows target) := by
  simp [Action.run, Common.rowLe]

theorem node_exact (pool : Pool scopes inputs) (rows : Fin pool.size → Row)
    (expression : RowExpr scopes (Fin inputs)) (member : expression ∈ pool.terms) :
    rowLe (nodeValue pool rows expression member) (rows (pool.reference _ member)) ↔
      EdgesHold (nodeEdges pool expression member) rows ∧ HeadsHold (nodeHeads pool expression member) rows := by
  cases expression with
  | var index =>
    simp [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold, Pool.input, Common.rowLe_refl]
  | empty => simp [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold, Common.rowEmpty_le]
  | head key => simpa [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold] using head_le_iff key (rows (pool.reference (.head key) member))
  | union first last =>
    simp [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold,
      Action.run, Common.rowLe, Common.rowJoin, or_imp, forall_and]
  | protect scope permission body =>
    simpa [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold, CommonSignedRows.commonProtect] using
      (CommonSignedFlowFamily.shift_edge_exact scope.val permission 1
        (rows (pool.child _ member body (by simp [subterms]))) (rows (pool.reference _ member))).symm
  | release scope permission body =>
    simpa [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold, CommonSignedRows.commonRelease] using
      (CommonSignedFlowFamily.shift_edge_exact scope.val permission (-1)
        (rows (pool.child _ member body (by simp [subterms]))) (rows (pool.reference _ member))).symm
  | residual handled body =>
    simpa [nodeValue, nodeEdges, nodeHeads, EdgesHold, HeadsHold] using
      (CommonSignedFlowFamily.residual_edge_exact handled
        (rows (pool.child _ member body (by simp [subterms]))) (rows (pool.reference _ member))).symm

def lowerScheme (pool : Pool scopes inputs) : CommonSignedGraphSolver.Scheme pool.size :=
  ⟨⟨pool.terms.attach.flatMap (fun term => nodeEdges pool term.val term.property), []⟩,
    pool.terms.attach.flatMap (fun term => nodeHeads pool term.val term.property)⟩

def LowerHolds (pool : Pool scopes inputs) (rows : Fin pool.size → Row) : Prop :=
  ∀ expression, ∀ member : expression ∈ pool.terms,
    rowLe (nodeValue pool rows expression member) (rows (pool.reference _ member))

theorem lowerScheme_exact (pool : Pool scopes inputs) (rows : Fin pool.size → Row) :
    CommonSignedGraphSolver.Models (lowerScheme pool) rows ↔ LowerHolds pool rows := by
  constructor
  · rintro ⟨⟨edges, _⟩, heads⟩ expression member
    apply (node_exact pool rows expression member).mpr
    constructor
    · intro edge included
      exact edges edge (List.mem_flatMap.mpr ⟨⟨expression, member⟩, by simp, included⟩)
    · intro head included
      exact heads head (List.mem_flatMap.mpr ⟨⟨expression, member⟩, by simp, included⟩)
  · intro lower
    refine ⟨⟨?_, by simp [lowerScheme]⟩, ?_⟩
    · intro edge member
      obtain ⟨term, _, included⟩ := List.mem_flatMap.mp member
      exact ((node_exact pool rows term.val term.property).mp (lower term.val term.property)).1 edge included
    · intro head member
      obtain ⟨term, _, included⟩ := List.mem_flatMap.mp member
      exact ((node_exact pool rows term.val term.property).mp (lower term.val term.property)).2 head included

/-- The exact expression evaluation is always a conservative lower model. -/
theorem extend_lower (pool : Pool scopes inputs) (rows : Fin inputs → Row) : LowerHolds pool (extend pool rows) := by
  intro expression member
  have same : nodeValue pool (extend pool rows) expression member = evaluate rows expression := by
    cases expression <;> simp only [nodeValue, Pool.child, Pool.input,
      CommonSignedExpressionPool.extend_reference, evaluate, RowExpr.eval]
    all_goals rfl
  rw [same, CommonSignedExpressionPool.extend_reference]
  exact Common.rowLe_refl _
/-- Every model's internal node is above the original expression meaning.
All shared original row variables are read through the same restriction. -/
theorem evaluate_below_node (pool : Pool scopes inputs) (rows : Fin pool.size → Row)
    (lower : LowerHolds pool rows) (expression : RowExpr scopes (Fin inputs))
    (member : expression ∈ pool.terms) :
    rowLe (evaluate (restrict pool rows) expression) (rows (pool.reference expression member)) := by
  induction expression with
  | var index => exact Common.rowLe_refl _
  | empty => exact Common.rowEmpty_le _
  | head key => exact lower _ member
  | union first last firstIH lastIH =>
    have firstBound := firstIH (pool.closed _ member first (by simp [subterms]))
    have lastBound := lastIH (pool.closed _ member last (by simp [subterms]))
    intro occurrence present
    apply lower _ member occurrence
    exact present.elim (fun present => Or.inl (firstBound occurrence present))
      (fun present => Or.inr (lastBound occurrence present))
  | protect scope permission body ih =>
    have childBound := ih (pool.closed _ member body (by simp [subterms]))
    intro occurrence present
    apply lower _ member occurrence
    exact childBound _ present
  | release scope permission body ih =>
    have childBound := ih (pool.closed _ member body (by simp [subterms]))
    intro occurrence present
    apply lower _ member occurrence
    exact childBound _ present
  | residual handled body ih =>
    have childBound := ih (pool.closed _ member body (by simp [subterms]))
    intro occurrence present
    apply lower _ member occurrence
    exact ⟨childBound occurrence present.1, present.2⟩
end Yulang.CommonSignedExpressionGraph
