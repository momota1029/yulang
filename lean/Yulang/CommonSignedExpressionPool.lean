import Yulang.CommonSignedGraphSolver
import Yulang.TypeConstraintGraph

/-! A shared finite allocator for all signed row-expression subterms. Original
row variables retain one shared reference and arbitrary independent rows. -/
namespace Yulang.CommonSignedExpressionPool
open Common (Row)
open CommonEffectRequestGeneration (RowExpr Computation)

variable {scopes inputs : Nat}

deriving instance DecidableEq for RowExpr

def subterms (expression : RowExpr scopes (Fin inputs)) : List (RowExpr scopes (Fin inputs)) :=
  expression :: match expression with
    | .union first last => subterms first ++ subterms last
    | .protect _ _ child | .release _ _ child | .residual _ child => subterms child
    | _ => []

@[simp] theorem self_mem_subterms (expression : RowExpr scopes (Fin inputs)) : expression ∈ subterms expression := by
  cases expression <;> simp [subterms]

theorem subterms_trans (expression part child : RowExpr scopes (Fin inputs))
    (inside : part ∈ subterms expression) (deeper : child ∈ subterms part) : child ∈ subterms expression := by
  induction expression with
  | var | empty | head =>
    have same := List.mem_singleton.mp inside
    subst part
    exact deeper
  | union first last firstIH lastIH =>
    rcases List.mem_cons.mp inside with same | inside
    · subst part; exact deeper
    · rcases List.mem_append.mp inside with fromFirst | fromLast
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (firstIH fromFirst))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (lastIH fromLast))
  | protect _ _ body ih | release _ _ body ih | residual _ body ih =>
    rcases List.mem_cons.mp inside with same | inside
    · subst part; exact deeper
    · exact List.mem_cons_of_mem _ (ih inside)

/-- Structural collector evidence is internal; compiled schemes store only
finite graphs and references, never these proof fields. -/
structure Pool (scopes inputs : Nat) where
  terms : List (RowExpr scopes (Fin inputs))
  distinct : terms.Nodup
  variables : ∀ index, .var index ∈ terms
  closed : ∀ term ∈ terms, ∀ part ∈ subterms term, part ∈ terms

def collect (roots : List (RowExpr scopes (Fin inputs))) : Pool scopes inputs where
  terms := TypeConstraintGraph.unique ((List.ofFn fun index : Fin inputs => RowExpr.var index) ++ roots.flatMap subterms)
  distinct := TypeConstraintGraph.unique_nodup _
  variables := by
    intro index
    apply (TypeConstraintGraph.mem_unique _ _).mpr
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
  closed := by
    intro term member part inside
    apply (TypeConstraintGraph.mem_unique _ _).mpr
    have original := (TypeConstraintGraph.mem_unique _ _).mp member
    rcases List.mem_append.mp original with fromVariables | fromRoots
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp fromVariables
      have same : part = .var index := by simpa [subterms] using inside
      rw [same]
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
    · obtain ⟨root, present, rootContains⟩ := List.mem_flatMap.mp fromRoots
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨root, present, subterms_trans root term part rootContains inside⟩)

theorem collect_covers (roots : List (RowExpr scopes (Fin inputs))) (root : RowExpr scopes (Fin inputs))
    (member : root ∈ roots) : root ∈ (collect roots).terms := by
  apply (TypeConstraintGraph.mem_unique _ _).mpr
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨root, member, self_mem_subterms root⟩)

namespace Pool

def size (pool : Pool scopes inputs) : Nat := pool.terms.length

def termAt (pool : Pool scopes inputs) (index : Fin pool.size) : RowExpr scopes (Fin inputs) := pool.terms[index.val]'index.isLt

theorem at_mem (pool : Pool scopes inputs) (index : Fin pool.size) : pool.termAt index ∈ pool.terms :=
  List.getElem_mem index.isLt

def reference (pool : Pool scopes inputs) (term : RowExpr scopes (Fin inputs)) (member : term ∈ pool.terms) : Fin pool.size :=
  ⟨pool.terms.idxOf term, List.idxOf_lt_length_of_mem member⟩

@[simp] theorem termAt_reference (pool : Pool scopes inputs) (term : RowExpr scopes (Fin inputs)) (member : term ∈ pool.terms) :
    pool.termAt (pool.reference term member) = term := List.getElem_idxOf (List.idxOf_lt_length_of_mem member)

@[simp] theorem reference_termAt (pool : Pool scopes inputs) (index : Fin pool.size) :
    pool.reference (pool.termAt index) (pool.at_mem index) = index := by
  apply Fin.ext
  exact pool.distinct.idxOf_getElem index.val index.isLt

def input (pool : Pool scopes inputs) (index : Fin inputs) : Fin pool.size := pool.reference (.var index) (pool.variables index)

def child (pool : Pool scopes inputs) (term : RowExpr scopes (Fin inputs)) (member : term ∈ pool.terms)
    (part : RowExpr scopes (Fin inputs)) (inside : part ∈ subterms term) : Fin pool.size :=
  pool.reference part (pool.closed term member part inside)
end Pool

/-- Value components are unused by signed row syntax. -/
def evaluate (rows : Fin inputs → Row) (expression : RowExpr scopes (Fin inputs)) : Row :=
  expression.eval (fun index => (.base .unit, rows index))

def extend (pool : Pool scopes inputs) (rows : Fin inputs → Row) : Fin pool.size → Row :=
  fun index => evaluate rows (pool.termAt index)

def restrict (pool : Pool scopes inputs) (rows : Fin pool.size → Row) : Fin inputs → Row := rows ∘ pool.input

@[simp] theorem extend_reference (pool : Pool scopes inputs) (rows : Fin inputs → Row)
    (expression : RowExpr scopes (Fin inputs)) (member : expression ∈ pool.terms) :
    extend pool rows (pool.reference expression member) = evaluate rows expression := by
  simp only [extend, Pool.termAt_reference]

@[simp] theorem restrict_extend (pool : Pool scopes inputs) (rows : Fin inputs → Row) : restrict pool (extend pool rows) = rows := by
  funext index
  simp [restrict, Pool.input, evaluate, RowExpr.eval]

theorem input_injective (pool : Pool scopes inputs) : Function.Injective pool.input := by
  intro first last same
  have equal := congrArg pool.termAt same
  simpa only [Pool.input, Pool.termAt_reference, RowExpr.var.injEq] using equal
end Yulang.CommonSignedExpressionPool
