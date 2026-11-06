import Yulang.NestedValueSolver
import Yulang.TypeSimplification

/-!
# Constructing shared finite graphs from actual type inequalities

The input is a finite list of inequalities over the existing `TyTerm (Fin m)`.
Rows have a fixed interpretation. A finite collector contains every original
variable and every subterm, then removes duplicates and assigns node indices.
Repeated variable occurrences therefore share one actual solver node.

The graph's constructor interpretation is defined for an arbitrary inference
model. Normalization preserves every input assignment and every graph realizer;
it does not ask the caller to supply a solution to perform construction.
Source unions and target intersections are decomposed exactly. Other lattice
positions and unknown record spines return `unsupported`, separately from a
solver rejection. All construction and saturation terminate without caller fuel.
-/

namespace Yulang.TypeConstraintGraph

open Inference

universe u v

variable {m : Nat} {RowType : Type u}

/-! ## Exact front decomposition -/

abbrev Problem (m : Nat) := List (TyTerm (Fin m) × TyTerm (Fin m))

def evaluate (model : Model) (rows : Fin m → model.Row) (value : Fin m → model.Ty)
    (term : TyTerm (Fin m)) : model.Ty :=
  term.eval model (fun index => (value index, rows index))

def Holds (model : Model) (rows : Fin m → model.Row) (value : Fin m → model.Ty)
    (problem : Problem m) : Prop :=
  ∀ constraint ∈ problem,
    model.subTy (evaluate model rows value constraint.1) (evaluate model rows value constraint.2)

@[simp] theorem holds_nil (model : Model) (rows : Fin m → model.Row)
    (value : Fin m → model.Ty) : Holds model rows value [] := by
  intro constraint impossible
  cases impossible

@[simp] theorem holds_cons (model : Model) (rows : Fin m → model.Row)
    (value : Fin m → model.Ty) (constraint : TyTerm (Fin m) × TyTerm (Fin m))
    (rest : Problem m) :
    Holds model rows value (constraint :: rest) ↔
      model.subTy (evaluate model rows value constraint.1) (evaluate model rows value constraint.2) ∧
        Holds model rows value rest := by
  simp only [Holds, List.mem_cons, forall_eq_or_imp]

@[simp] theorem holds_append (model : Model) (rows : Fin m → model.Row)
    (value : Fin m → model.Ty) (left right : Problem m) :
    Holds model rows value (left ++ right) ↔
      Holds model rows value left ∧ Holds model rows value right := by
  simp only [Holds, List.mem_append, or_imp, forall_and]

/-- These are the only semantic laws used by the front decomposition. -/
structure LatticeRules (model : Model) : Prop where
  union_is_join : ∀ a b c, model.subTy (model.union a b) c ↔ model.subTy a c ∧ model.subTy b c
  inter_is_meet : ∀ a b c, model.subTy c (model.inter a b) ↔ model.subTy c a ∧ model.subTy c b

/-- Lattice nodes cannot remain inside rigid constructor nodes. Record field
values may contain unknowns, while the tail must be a known record spine. -/
def rigid : TyTerm (Fin m) → Bool
  | .var _ | .base _ | .bottom | .top | .emptyRecord => true
  | .union _ _ | .inter _ _ => false
  | .pair left right => rigid left && rigid right
  | .record _ value rest =>
      ValueBoundElimination.recordSpine rest && rigid value && rigid rest
  | .variant _ payload => rigid payload
  | .arrow input _ output _ => rigid input && rigid output

def RigidProblem (problem : Problem m) : Prop :=
  ∀ constraint ∈ problem, rigid constraint.1 = true ∧ rigid constraint.2 = true

@[simp] theorem rigidProblem_nil : RigidProblem ([] : Problem m) := by
  intro constraint impossible
  cases impossible

@[simp] theorem rigidProblem_cons (constraint : TyTerm (Fin m) × TyTerm (Fin m))
    (rest : Problem m) :
    RigidProblem (constraint :: rest) ↔
      (rigid constraint.1 = true ∧ rigid constraint.2 = true) ∧ RigidProblem rest := by
  simp only [RigidProblem, List.mem_cons, forall_eq_or_imp]

@[simp] theorem rigidProblem_append (left right : Problem m) :
    RigidProblem (left ++ right) ↔ RigidProblem left ∧ RigidProblem right := by
  constructor
  · intro valid
    exact ⟨fun constraint member => valid constraint (List.mem_append_left _ member),
      fun constraint member => valid constraint (List.mem_append_right _ member)⟩
  · rintro ⟨first, last⟩ constraint member
    exact (List.mem_append.mp member).elim (first constraint) (last constraint)

/-- Append two successful decompositions, preserving an unsupported result. -/
def appendSome (left right : Option (Problem m)) : Option (Problem m) :=
  match left, right with
  | some first, some last => some (first ++ last)
  | _, _ => none

theorem appendSome_some_iff (left right : Option (Problem m)) (result : Problem m) :
    appendSome left right = some result ↔
      ∃ first last, left = some first ∧ right = some last ∧ result = first ++ last := by
  cases left <;> cases right <;> simp [appendSome, eq_comm]

/-- A finite syntax recursion: union-left and intersection-right are split;
all other lattice positions remain explicitly unsupported. -/
def splitInequality (source target : TyTerm (Fin m)) : Option (Problem m) :=
  match source, target with
  | .union left right, target =>
      appendSome (splitInequality left target) (splitInequality right target)
  | source, .inter left right =>
      appendSome (splitInequality source left) (splitInequality source right)
  | source, target =>
      if rigid source && rigid target then some [(source, target)] else none
termination_by TypeSimplification.nodes source + TypeSimplification.nodes target
decreasing_by
  all_goals simp_wf
  all_goals simp only [TypeSimplification.nodes]
  all_goals omega

theorem splitInequality_some_rigid (source target : TyTerm (Fin m)) (result : Problem m)
    (returned : splitInequality source target = some result) : RigidProblem result := by
  rw [splitInequality.eq_def] at returned
  split at returned
  · obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
      (appendSome_some_iff _ _ _).mp returned
    exact (rigidProblem_append first last).mpr
      ⟨splitInequality_some_rigid _ _ first firstFound,
        splitInequality_some_rigid _ _ last lastFound⟩
  · obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
      (appendSome_some_iff _ _ _).mp returned
    exact (rigidProblem_append first last).mpr
      ⟨splitInequality_some_rigid _ _ first firstFound,
        splitInequality_some_rigid _ _ last lastFound⟩
  · split at returned
    · rename_i accepted
      have same := Option.some.inj returned
      subst result
      exact (rigidProblem_cons _ []).mpr ⟨Bool.and_eq_true_iff.mp accepted, rigidProblem_nil⟩
    · cases returned
termination_by TypeSimplification.nodes source + TypeSimplification.nodes target
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals simp only [TypeSimplification.nodes]
  all_goals omega

/-- Every accepted decomposition is equivalent at each fixed assignment in
any model with the two stated lattice laws. -/
theorem splitInequality_some_exact (model : Model) (laws : LatticeRules model)
    (rows : Fin m → model.Row) (value : Fin m → model.Ty)
    (source target : TyTerm (Fin m)) (result : Problem m)
    (returned : splitInequality source target = some result) :
    Holds model rows value result ↔ model.subTy (evaluate model rows value source)
      (evaluate model rows value target) := by
  rw [splitInequality.eq_def] at returned
  split at returned
  · obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
      (appendSome_some_iff _ _ _).mp returned
    rw [holds_append,
      splitInequality_some_exact model laws rows value _ _ first firstFound,
      splitInequality_some_exact model laws rows value _ _ last lastFound]
    exact (laws.union_is_join _ _ _).symm
  · obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
      (appendSome_some_iff _ _ _).mp returned
    rw [holds_append,
      splitInequality_some_exact model laws rows value _ _ first firstFound,
      splitInequality_some_exact model laws rows value _ _ last lastFound]
    exact (laws.inter_is_meet _ _ _).symm
  · split at returned
    · have same := Option.some.inj returned
      subst result
      simp only [holds_cons, holds_nil, and_true]
    · cases returned
termination_by TypeSimplification.nodes source + TypeSimplification.nodes target
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals simp only [TypeSimplification.nodes]
  all_goals omega

def splitProblem : Problem m → Option (Problem m)
  | [] => some []
  | (source, target) :: rest => appendSome (splitInequality source target) (splitProblem rest)

theorem splitProblem_some_rigid (problem result : Problem m)
    (returned : splitProblem problem = some result) : RigidProblem result := by
  induction problem generalizing result with
  | nil =>
      have same : ([] : Problem m) = result := Option.some.inj returned
      subst result
      exact rigidProblem_nil
  | cons constraint rest ih =>
      obtain ⟨source, target⟩ := constraint
      obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
        (appendSome_some_iff _ _ _).mp returned
      exact (rigidProblem_append first last).mpr
        ⟨splitInequality_some_rigid source target first firstFound, ih last lastFound⟩

theorem splitProblem_some_exact (model : Model) (laws : LatticeRules model)
    (rows : Fin m → model.Row) (value : Fin m → model.Ty)
    (problem result : Problem m) (returned : splitProblem problem = some result) :
    Holds model rows value result ↔ Holds model rows value problem := by
  induction problem generalizing result with
  | nil =>
      have same : ([] : Problem m) = result := Option.some.inj returned
      subst result
      rfl
  | cons constraint rest ih =>
      obtain ⟨source, target⟩ := constraint
      obtain ⟨first, last, firstFound, lastFound, rfl⟩ :=
        (appendSome_some_iff _ _ _).mp returned
      rw [holds_append, holds_cons,
        splitInequality_some_exact model laws rows value source target first firstFound,
        ih last lastFound]


/-! ## Finite node collection and interpretation -/

/-- All value subterms, including the term itself. Row variables have their
own fixed interpretation and do not allocate additional value nodes. -/
def subterms (term : TyTerm (Fin m)) : List (TyTerm (Fin m)) :=
  term :: match term with
  | .union left right | .inter left right | .pair left right | .record _ left right =>
      subterms left ++ subterms right
  | .variant _ payload => subterms payload
  | .arrow input _ output _ => subterms input ++ subterms output
  | _ => []

@[simp] theorem self_mem_subterms (term : TyTerm (Fin m)) : term ∈ subterms term := by
  cases term <;> simp [subterms]

theorem subterms_trans (term part child : TyTerm (Fin m))
    (inside : part ∈ subterms term) (deeper : child ∈ subterms part) :
    child ∈ subterms term := by
  induction term with
  | var | base | bottom | top | emptyRecord =>
      have equal := List.mem_singleton.mp inside
      subst part
      exact deeper
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb | record _ a b iha ihb | arrow a _ b _ iha ihb =>
      rcases List.mem_cons.mp inside with same | inside
      · subst part
        exact deeper
      · rcases List.mem_append.mp inside with left | right
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iha left))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihb right))
  | variant label payload ih =>
      rcases List.mem_cons.mp inside with same | inside
      · subst part
        exact deeper
      · exact List.mem_cons_of_mem _ (ih inside)

theorem rigid_subterms (term part : TyTerm (Fin m)) (valid : rigid term = true)
    (member : part ∈ subterms term) : rigid part = true := by
  induction term with
  | var | base | bottom | top | emptyRecord =>
      have equal := List.mem_singleton.mp member
      subst part
      exact valid
  | union | inter => cases valid
  | pair a b iha ihb | arrow a _ b _ iha ihb =>
      have checks := Bool.and_eq_true_iff.mp valid
      rcases List.mem_cons.mp member with same | member
      · subst part; exact valid
      · rcases List.mem_append.mp member with left | right
        · exact iha checks.1 left
        · exact ihb checks.2 right
  | record label head rest ihh ihr =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ rigid head = true) ∧
          rigid rest = true := by simpa only [rigid, Bool.and_eq_true] using valid
      rcases List.mem_cons.mp member with same | member
      · subst part; exact valid
      · rcases List.mem_append.mp member with left | right
        · exact ihh checks.1.2 left
        · exact ihr checks.2 right
  | variant label payload ih =>
      rcases List.mem_cons.mp member with same | member
      · subst part; exact valid
      · exact ih valid member

/-- A simple, total deduplicator with an explicit no-duplicates certificate. -/
def unique [DecidableEq α] : List α → List α
  | [] => []
  | first :: rest => if first ∈ rest then unique rest else first :: unique rest

@[simp] theorem mem_unique [DecidableEq α] (value : α) (list : List α) :
    value ∈ unique list ↔ value ∈ list := by
  induction list with
  | nil => simp [unique]
  | cons first rest ih =>
      simp only [unique]
      split <;> simp_all

theorem unique_nodup [DecidableEq α] (list : List α) : (unique list).Nodup := by
  induction list with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      simp only [unique]
      split
      · exact ih
      · exact List.nodup_cons.mpr ⟨by simpa only [mem_unique] using ‹first ∉ rest›, ih⟩

def rawTerms (problem : Problem m) : List (TyTerm (Fin m)) :=
  (List.finRange m).map TyTerm.var ++ problem.flatMap fun edge => subterms edge.1 ++ subterms edge.2

/-- Closure and uniqueness are proofs; only the finite term table is retained
by code generation. -/
structure Pool (m : Nat) where
  terms : List (TyTerm (Fin m))
  distinct : terms.Nodup
  variables : ∀ index, .var index ∈ terms
  closed : ∀ term ∈ terms, ∀ part ∈ subterms term, part ∈ terms
  supported : ∀ term ∈ terms, rigid term = true

def collect (problem : Problem m) (valid : RigidProblem problem) : Pool m where
  terms := unique (rawTerms problem)
  distinct := unique_nodup _
  variables := by
    intro index
    apply (mem_unique _ _).mpr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨index, by simp, rfl⟩)
  closed := by
    intro term member part inside
    apply (mem_unique _ _).mpr
    have original := (mem_unique term (rawTerms problem)).mp member
    rcases List.mem_append.mp original with fromVars | fromProblem
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp fromVars
      have same : part = .var index := by simpa [subterms] using inside
      subst part
      exact original
    · obtain ⟨edge, edgeMember, fromEdge⟩ := List.mem_flatMap.mp fromProblem
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨edge, edgeMember, ?_⟩
      rcases List.mem_append.mp fromEdge with left | right
      · exact List.mem_append_left _ (subterms_trans _ _ _ left inside)
      · exact List.mem_append_right _ (subterms_trans _ _ _ right inside)
  supported := by
    intro term member
    have original := (mem_unique term (rawTerms problem)).mp member
    rcases List.mem_append.mp original with fromVars | fromProblem
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp fromVars
      rfl
    · obtain ⟨edge, edgeMember, fromEdge⟩ := List.mem_flatMap.mp fromProblem
      rcases List.mem_append.mp fromEdge with left | right
      · exact rigid_subterms _ _ (valid edge edgeMember).1 left
      · exact rigid_subterms _ _ (valid edge edgeMember).2 right

theorem collect_covers (problem : Problem m) (valid : RigidProblem problem)
    (edge : TyTerm (Fin m) × TyTerm (Fin m)) (member : edge ∈ problem) :
    edge.1 ∈ (collect problem valid).terms ∧ edge.2 ∈ (collect problem valid).terms := by
  constructor <;> apply (mem_unique _ _).mpr <;> apply List.mem_append_right <;>
    apply List.mem_flatMap.mpr
  · exact ⟨edge, member, List.mem_append_left _ (self_mem_subterms _)⟩
  · exact ⟨edge, member, List.mem_append_right _ (self_mem_subterms _)⟩

namespace Pool

def size (pool : Pool m) : Nat := pool.terms.length

def termAt (pool : Pool m) (index : Fin pool.size) : TyTerm (Fin m)  := pool.terms[index.val]'index.isLt

theorem at_mem (pool : Pool m) (index : Fin pool.size) : pool.termAt index ∈ pool.terms :=
  List.getElem_mem index.isLt

def reference (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : Fin pool.size :=
  ⟨pool.terms.idxOf term, List.idxOf_lt_length_of_mem member⟩

@[simp] theorem termAt_reference (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    pool.termAt (pool.reference term member) = term :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem member)

@[simp] theorem reference_termAt (pool : Pool m) (index : Fin pool.size) :
    pool.reference (pool.termAt index) (pool.at_mem index) = index := by
  apply Fin.ext
  exact pool.distinct.idxOf_getElem index.val index.isLt

def input (pool : Pool m) (index : Fin m) : Fin pool.size := pool.reference (.var index) (pool.variables index)

theorem input_injective (pool : Pool m) : Function.Injective pool.input := by
  intro first second same
  have equal := congrArg pool.termAt same
  simpa only [input, termAt_reference, TyTerm.var.injEq] using equal

/-- Direct child references retain their subterm membership as erased proofs. -/
def child (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (part : TyTerm (Fin m)) (inside : part ∈ subterms term) : Fin pool.size :=
  pool.reference part (pool.closed term member part inside)

end Pool

/-- Rows are interpreted independently of any value assignment. -/
def rowEval (empty : RowType) (join : RowType → RowType → RowType) (rows : Fin m → RowType) :
    RowTerm (Fin m) → RowType
  | .var index => rows index
  | .empty => empty
  | .join left right => join (rowEval empty join rows left) (rowEval empty join rows right)

theorem rowEval_eq (model : Model) (rows : Fin m → model.Row) (value : Fin m → model.Ty)
    (term : RowTerm (Fin m)) :
    rowEval model.empty model.join rows term = term.eval model (fun i => (value i, rows i)) := by
  induction term with
  | var | empty => rfl
  | join left right ihl ihr => simp only [rowEval, RowTerm.eval, ihl, ihr]

/-- Record fields keep their source order and duplicates. Lookup in the target
solver therefore has exactly the original first-field-wins behavior. -/
def indexedFields (pool : Pool m) : (term : TyTerm (Fin m)) → term ∈ pool.terms →
    List (Nat × Fin pool.size)
  | .record label value rest, member =>
      (label, pool.child _ member value (by simp [subterms])) ::
        indexedFields pool rest (pool.closed _ member rest (by simp [subterms]))
  | _, _ => []

def nodeOf (pool : Pool m) (empty : RowType) (join : RowType → RowType → RowType)
    (rows : Fin m → RowType) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    NestedValueSolver.Node pool.size RowType :=
  match term with
  | .var _ => .var
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union _ _ | .inter _ _ => by have impossible := pool.supported _ member; cases impossible
  | .pair left right =>
      .pair (pool.child _ member left (by simp [subterms]))
        (pool.child _ member right (by simp [subterms]))
  | .variant label payload => .variant label (pool.child _ member payload (by simp [subterms]))
  | .arrow input inputRow output outputRow =>
      .arrow (pool.child _ member input (by simp [subterms])) (rowEval empty join rows inputRow)
        (pool.child _ member output (by simp [subterms])) (rowEval empty join rows outputRow)
  | .emptyRecord => .record []
  | .record _ _ _ => .record (indexedFields pool _ member)

def graph (pool : Pool m) (empty : RowType) (join : RowType → RowType → RowType)
    (rows : Fin m → RowType) : NestedValueSolver.Graph pool.size RowType :=
  fun index => nodeOf pool empty join rows (pool.termAt index) (pool.at_mem index)

@[simp] theorem graph_reference (pool : Pool m) (empty : RowType) (join : RowType → RowType → RowType)
    (rows : Fin m → RowType) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    graph pool empty join rows (pool.reference term member) = nodeOf pool empty join rows term member := by
  simp only [graph, Pool.termAt_reference]

/-- Constructor meaning for an arbitrary inference model; neither a solver
result nor a structural-type representation occurs in this definition. -/
def recordMeaning (model : Model) (value : α → model.Ty) : List (Nat × α) → model.Ty
  | [] => model.emptyRecord
  | (label, field) :: rest => model.record label (value field) (recordMeaning model value rest)

def NodeMeaning (model : Model) (value : Fin n → model.Ty) (actual : model.Ty) :
    NestedValueSolver.Node n model.Row → Prop
  | .var => True
  | .base scalar => actual = model.base scalar
  | .bottom => actual = model.bottom
  | .top => actual = model.top
  | .pair left right => actual = model.pair (value left) (value right)
  | .variant label payload => actual = model.variant label (value payload)
  | .arrow input inputRow output outputRow =>
      actual = model.arrow (value input) inputRow (value output) outputRow
  | .record fields => actual = recordMeaning model value fields

def Realizes (model : Model) (graph : NestedValueSolver.Graph n model.Row) (value : Fin n → model.Ty) : Prop :=
  ∀ node, NodeMeaning model value (value node) (graph node)

def Satisfies (model : Model) (constraints : List (NestedValueSolver.Edge n))
    (value : Fin n → model.Ty) : Prop :=
  ∀ edge ∈ constraints, model.subTy (value edge.1) (value edge.2)

def GraphModels (model : Model) (graph : NestedValueSolver.Graph n model.Row)
    (constraints : List (NestedValueSolver.Edge n)) (value : Fin n → model.Ty) : Prop :=
  Realizes model graph value ∧ Satisfies model constraints value

/-- Every graph node receives the interpretation of its collected source term. -/
def extend (pool : Pool m) (model : Model) (rows : Fin m → model.Row) (input : Fin m → model.Ty) :
    Fin pool.size → model.Ty := fun index => evaluate model rows input (pool.termAt index)

@[simp] theorem extend_reference (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (input : Fin m → model.Ty) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    extend pool model rows input (pool.reference term member) = evaluate model rows input term := by
  simp only [extend, Pool.termAt_reference]

@[simp] theorem extend_input (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (input : Fin m → model.Ty) (index : Fin m) :
    extend pool model rows input (pool.input index) = input index := by
  simp [Pool.input, evaluate, TyTerm.eval]


/-- Interpreting flattened fields agrees with the original record syntax,
including hidden duplicate labels and the exact record-tail constructor chain. -/
theorem indexedFields_extend (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (input : Fin m → model.Ty) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : ValueBoundElimination.recordSpine term = true) :
    recordMeaning model (extend pool model rows input) (indexedFields pool term member) =
      evaluate model rows input term := by
  cases term with
  | emptyRecord => rfl
  | record label value rest =>
      simp only [indexedFields, recordMeaning, Pool.child, extend_reference]
      rw [indexedFields_extend pool model rows input rest _ shape]
      rfl
  | _ => cases shape
termination_by TypeSimplification.nodes term
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [TypeSimplification.nodes]
  all_goals omega

/-- The collector's canonical interpretation realizes every node, for every
input assignment in every inference model. -/
theorem nodeOf_evaluate (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (input : Fin m → model.Ty) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    NodeMeaning model (extend pool model rows input) (evaluate model rows input term)
      (nodeOf pool model.empty model.join rows term member) := by
  cases term with
  | union | inter => have impossible := pool.supported _ member; cases impossible
  | record label value rest =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ rigid value = true) ∧
          rigid rest = true := by
        simpa only [rigid, Bool.and_eq_true] using pool.supported _ member
      exact (indexedFields_extend pool model rows input _ member checks.1.1).symm
  | _ =>
      simp only [nodeOf, NodeMeaning, recordMeaning, Pool.child, extend_reference, evaluate, TyTerm.eval, ← rowEval_eq]

theorem extend_realizes (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (input : Fin m → model.Ty) :
    Realizes model (graph pool model.empty model.join rows) (extend pool model rows input) := by
  intro node
  exact nodeOf_evaluate pool model rows input (pool.termAt node) (pool.at_mem node)

theorem realizes_reference (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (value : Fin pool.size → model.Ty)
    (realizes : Realizes model (graph pool model.empty model.join rows) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    NodeMeaning model value (value (pool.reference term member))
      (nodeOf pool model.empty model.join rows term member) := by
  simpa only [graph_reference] using realizes (pool.reference term member)

theorem realizes_record (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (value : Fin pool.size → model.Ty)
    (realizes : Realizes model (graph pool model.empty model.join rows) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : ValueBoundElimination.recordSpine term = true) :
    value (pool.reference term member) = recordMeaning model value (indexedFields pool term member) := by
  cases term with
  | emptyRecord => exact realizes_reference pool model rows value realizes _ member
  | record => exact realizes_reference pool model rows value realizes _ member
  | _ => cases shape

/-- Every realizer, not only the constructed one, evaluates each reference as
the original term under the values of the shared input-variable nodes. -/
theorem realizes_evaluate (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (value : Fin pool.size → model.Ty)
    (realizes : Realizes model (graph pool model.empty model.join rows) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    value (pool.reference term member) = evaluate model rows (fun i => value (pool.input i)) term := by
  have interpreted := realizes_reference pool model rows value realizes term member
  cases term with
  | var index => rfl
  | union | inter => have impossible := pool.supported _ member; cases impossible
  | base | bottom | top | emptyRecord => exact interpreted
  | pair left right =>
      have leftEqual := realizes_evaluate pool model rows value realizes left
        (pool.closed _ member left (by simp [subterms]))
      have rightEqual := realizes_evaluate pool model rows value realizes right
        (pool.closed _ member right (by simp [subterms]))
      simpa only [nodeOf, NodeMeaning, Pool.child, leftEqual, rightEqual, evaluate, TyTerm.eval] using interpreted
  | variant label payload =>
      have payloadEqual := realizes_evaluate pool model rows value realizes payload
        (pool.closed _ member payload (by simp [subterms]))
      simpa only [nodeOf, NodeMeaning, Pool.child, payloadEqual, evaluate, TyTerm.eval] using interpreted
  | arrow input inputRow output outputRow =>
      have inputEqual := realizes_evaluate pool model rows value realizes input
        (pool.closed _ member input (by simp [subterms]))
      have outputEqual := realizes_evaluate pool model rows value realizes output
        (pool.closed _ member output (by simp [subterms]))
      simpa only [nodeOf, NodeMeaning, Pool.child, inputEqual, outputEqual, evaluate, TyTerm.eval,
        ← rowEval_eq] using interpreted
  | record label head rest =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ rigid head = true) ∧
          rigid rest = true := by
        simpa only [rigid, Bool.and_eq_true] using pool.supported _ member
      have headEqual := realizes_evaluate pool model rows value realizes head
        (pool.closed _ member head (by simp [subterms]))
      have restEqual := realizes_evaluate pool model rows value realizes rest
        (pool.closed _ member rest (by simp [subterms]))
      have fieldsEqual := realizes_record pool model rows value realizes rest
        (pool.closed _ member rest (by simp [subterms])) checks.1.1
      simpa only [nodeOf, NodeMeaning, indexedFields, recordMeaning, Pool.child,
        ← fieldsEqual, headEqual, restEqual, evaluate, TyTerm.eval] using interpreted
termination_by TypeSimplification.nodes term
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [TypeSimplification.nodes]
  all_goals omega

/-- Finite output data used directly by `NestedValueSolver.solve`. `source`
records the source term attached to each node and supports semantic lifting. -/
structure Compiled (m : Nat) (RowType : Type u) where
  size : Nat
  graph : NestedValueSolver.Graph size RowType
  constraints : List (NestedValueSolver.Edge size)
  input : Fin m → Fin size
  source : Fin size → TyTerm (Fin m)

def compiledEdges (problem : Problem m) (valid : RigidProblem problem) :
    List (NestedValueSolver.Edge (collect problem valid).size) :=
  problem.attach.map fun edge =>
    ((collect problem valid).reference edge.val.1 (collect_covers problem valid edge.val edge.property).1,
      (collect problem valid).reference edge.val.2 (collect_covers problem valid edge.val edge.property).2)

def build (empty : RowType) (join : RowType → RowType → RowType) (rows : Fin m → RowType)
    (problem : Problem m) (valid : RigidProblem problem) : Compiled m RowType where
  size := (collect problem valid).size
  graph := graph (collect problem valid) empty join rows
  constraints := compiledEdges problem valid
  input := (collect problem valid).input
  source := (collect problem valid).termAt

def Compiled.extend (model : Model) (compiled : Compiled m model.Row)
    (rows : Fin m → model.Row) (input : Fin m → model.Ty) : Fin compiled.size → model.Ty :=
  fun node => evaluate model rows input (compiled.source node)

def Compiled.restrict (compiled : Compiled m RowType) (value : Fin compiled.size → α) : Fin m → α :=
  fun index => value (compiled.input index)

/-- Once constructors are realized, each generated graph edge is exactly its
original inequality. The result quantifies over arbitrary graph values. -/
theorem compiledEdges_exact (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (valid : RigidProblem problem)
    (value : Fin (collect problem valid).size → model.Ty)
    (realizes : Realizes model (graph (collect problem valid) model.empty model.join rows) value) :
    Satisfies model (compiledEdges problem valid) value ↔
      Holds model rows (fun i => value ((collect problem valid).input i)) problem := by
  constructor
  · intro accepted edge member
    have generated := accepted _ (List.mem_map.mpr ⟨⟨edge, member⟩, by simp, rfl⟩)
    simpa only [realizes_evaluate _ _ _ _ realizes] using generated
  · intro accepted edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    simpa only [realizes_evaluate _ _ _ _ realizes] using accepted original.val original.property

theorem build_realizes (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (valid : RigidProblem problem) (input : Fin m → model.Ty) :
    Realizes model (build model.empty model.join rows problem valid).graph
      ((build model.empty model.join rows problem valid).extend model rows input) :=
  extend_realizes (collect problem valid) model rows input

@[simp] theorem build_restrict_extend (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (valid : RigidProblem problem) (input : Fin m → model.Ty) :
    (build model.empty model.join rows problem valid).restrict
      ((build model.empty model.join rows problem valid).extend model rows input) = input := by
  funext index
  exact extend_input (collect problem valid) model rows input index

theorem build_models_iff (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (valid : RigidProblem problem)
    (value : Fin (build model.empty model.join rows problem valid).size → model.Ty) :
    GraphModels model (build model.empty model.join rows problem valid).graph
        (build model.empty model.join rows problem valid).constraints value ↔
      Realizes model (build model.empty model.join rows problem valid).graph value ∧
        Holds model rows ((build model.empty model.join rows problem valid).restrict value) problem := by
  constructor
  · rintro ⟨realizes, accepted⟩
    exact ⟨realizes, (compiledEdges_exact model rows problem valid value realizes).mp accepted⟩
  · rintro ⟨realizes, accepted⟩
    exact ⟨realizes, (compiledEdges_exact model rows problem valid value realizes).mpr accepted⟩

theorem build_extend_exact (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (valid : RigidProblem problem) (input : Fin m → model.Ty) :
    GraphModels model (build model.empty model.join rows problem valid).graph
        (build model.empty model.join rows problem valid).constraints
        ((build model.empty model.join rows problem valid).extend model rows input) ↔
      Holds model rows input problem := by
  rw [build_models_iff, build_restrict_extend]
  exact and_iff_right (build_realizes model rows problem valid input)

/-- Failure is an unsupported graph representation. An inconsistent rigid
problem still compiles and is passed to the actual nested solver. -/
def compile (empty : RowType) (join : RowType → RowType → RowType) (rows : Fin m → RowType)
    (problem : Problem m) : Option (Compiled m RowType) :=
  match returned : splitProblem problem with
  | none => none
  | some normalized => some (build empty join rows normalized (splitProblem_some_rigid problem normalized returned))

theorem compile_some (empty : RowType) (join : RowType → RowType → RowType) (rows : Fin m → RowType)
    (problem : Problem m) (compiled : Compiled m RowType) (returned : compile empty join rows problem = some compiled) :
    ∃ normalized, ∃ split : splitProblem problem = some normalized,
      compiled = build empty join rows normalized (splitProblem_some_rigid problem normalized split) := by
  unfold compile at returned
  split at returned
  · cases returned
  · rename_i normalized split
    exact ⟨normalized, split, (Option.some.inj returned).symm⟩

/-- Semantic preservation for every graph realizer and every original model. -/
theorem compile_models_iff (model : Model) (laws : LatticeRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled)
    (value : Fin compiled.size → model.Ty) :
    GraphModels model compiled.graph compiled.constraints value ↔
      Realizes model compiled.graph value ∧ Holds model rows (compiled.restrict value) problem := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  rw [build_models_iff, splitProblem_some_exact model laws rows _ problem normalized split]

theorem compile_extend_exact (model : Model) (laws : LatticeRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    GraphModels model compiled.graph compiled.constraints (compiled.extend model rows input) ↔
      Holds model rows input problem := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  exact (build_extend_exact model rows normalized _ input).trans
    (splitProblem_some_exact model laws rows input problem normalized split)

/-- Every original input slot has one distinct node, regardless of how often
it occurs in nested types or constraints. -/
theorem compile_input_injective (empty : RowType) (join : RowType → RowType → RowType)
    (rows : Fin m → RowType) (problem : Problem m) (compiled : Compiled m RowType)
    (returned : compile empty join rows problem = some compiled) : Function.Injective compiled.input := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  exact Pool.input_injective _

theorem compile_restrict_extend (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    compiled.restrict (compiled.extend model rows input) = input := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  exact build_restrict_extend model rows normalized _ input

/-- Exact preservation at a fixed input assignment, with no assumption that a
solution exists and no supplied graph assignment needed for compilation. -/
theorem compile_assignment_exact (model : Model) (laws : LatticeRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    Holds model rows input problem ↔
      ∃ value : Fin compiled.size → model.Ty,
        GraphModels model compiled.graph compiled.constraints value ∧ compiled.restrict value = input := by
  constructor
  · intro accepted
    exact ⟨compiled.extend model rows input,
      (compile_extend_exact model laws rows problem compiled returned input).mpr accepted,
      compile_restrict_extend model rows problem compiled returned input⟩
  · rintro ⟨value, accepted, agrees⟩
    have original := ((compile_models_iff model laws rows problem compiled returned value).mp accepted).2
    simpa only [agrees] using original


/-- A graph realizer has no extra degrees of freedom beyond its original
input variables: interpreting the collected terms reconstructs it exactly. -/
theorem compile_retraction (model : Model) (rows : Fin m → model.Row)
    (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled)
    (value : Fin compiled.size → model.Ty) (realizes : Realizes model compiled.graph value) :
    compiled.extend model rows (compiled.restrict value) = value := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  funext node
  have same := realizes_evaluate (collect normalized (splitProblem_some_rigid problem normalized split))
    model rows value realizes _ ((collect normalized _).at_mem node)
  exact same.symm.trans (congrArg value (Pool.reference_termAt _ node))

/-! ## The actual nested solver entry point -/

theorem structuralLatticeRules (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) : LatticeRules (StructuralBase.model RowType empty join leRow) :=
  ⟨StructuralBase.union_is_join, StructuralBase.inter_is_meet⟩

theorem recordMeaning_structural (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (value : NestedValueSolver.Valuation n RowType)
    (fields : List (Nat × Fin n)) :
    recordMeaning (StructuralBase.model RowType empty join leRow) value fields =
      NestedValueSolver.recordType value fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => exact congrArg (StructuralBase.Ty.record field.1 (value field.2)) ih

theorem nodeMeaning_structural (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (value : NestedValueSolver.Valuation n RowType)
    (actual : StructuralBase.Ty RowType) (node : NestedValueSolver.Node n RowType) :
    NodeMeaning (StructuralBase.model RowType empty join leRow) value actual node ↔
      node.Holds value actual := by
  cases node with
  | record fields =>
      change (actual = recordMeaning (StructuralBase.model RowType empty join leRow) value fields) ↔ _
      rw [recordMeaning_structural empty join leRow value fields]
      rfl
  | _ => rfl

theorem graphModels_structural (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (graph : NestedValueSolver.Graph n RowType)
    (constraints : List (NestedValueSolver.Edge n)) (value : NestedValueSolver.Valuation n RowType) :
    GraphModels (StructuralBase.model RowType empty join leRow) graph constraints value ↔
      NestedValueSolver.Models leRow graph constraints value := by
  constructor
  · rintro ⟨realizes, accepted⟩
    exact ⟨fun node => (nodeMeaning_structural empty join leRow value (value node) (graph node)).mp
      (realizes node), accepted⟩
  · rintro ⟨realizes, accepted⟩
    exact ⟨fun node => (nodeMeaning_structural empty join leRow value (value node) (graph node)).mpr
      (realizes node), accepted⟩

/-- Flattening retains the exact lookup result of the original record,
including arbitrary duplicate labels; both sides select the first field. -/
theorem indexedFields_lookup_exact (pool : Pool m) (empty : RowType)
    (join : RowType → RowType → RowType) (leRow : RowType → RowType → Prop)
    (rows : Fin m → RowType) (input : Fin m → StructuralBase.Ty RowType)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (shape : ValueBoundElimination.recordSpine term = true) (label : Nat) :
    (evaluate (StructuralBase.model RowType empty join leRow) rows input term).lookup label =
      (NestedValueSolver.lookupField label (indexedFields pool term member)).map
        (extend pool (StructuralBase.model RowType empty join leRow) rows input) := by
  have same := indexedFields_extend pool (StructuralBase.model RowType empty join leRow) rows input term member shape
  have converted := recordMeaning_structural (n := pool.size) empty join leRow
    (extend pool (StructuralBase.model RowType empty join leRow) rows input) (indexedFields pool term member)
  have equal := converted.symm.trans same
  exact (congrArg (StructuralBase.Ty.lookup label) equal.symm).trans
    (NestedValueSolver.recordType_lookup _ _ label)

/-- The original type inequalities and the computed saturated cache have
exactly the same models, under the compiler's input-variable restriction. -/
theorem compile_saturate_models_iff (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin m → RowType) (problem : Problem m) (compiled : Compiled m RowType)
    (returned : compile empty join rows problem = some compiled)
    (value : NestedValueSolver.Valuation compiled.size RowType) :
    NestedValueSolver.Models leRow compiled.graph
        (NestedValueSolver.saturate compiled.graph compiled.constraints) value ↔
      Realizes (StructuralBase.model RowType empty join leRow) compiled.graph value ∧
        Holds (StructuralBase.model RowType empty join leRow) rows (compiled.restrict value) problem := by
  rw [NestedValueSolver.saturate_models_iff leRow rowRefl rowTrans]
  rw [← graphModels_structural empty join leRow]
  exact compile_models_iff _ (structuralLatticeRules empty join leRow) rows problem compiled returned value

inductive Status where
  | unsupported
  | rejected
  | saturated
  deriving DecidableEq, Repr

inductive Result (m : Nat) (RowType : Type u) where
  | unsupported
  | rejected
  | saturated (compiled : Compiled m RowType) (cache : List (NestedValueSolver.Edge compiled.size))

def Result.status : Result m RowType → Status
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .saturated _ _ => .saturated

/-- Compile actual inequalities, then run the existing finite nested solver.
A successful cache is not relabeled as a constructed principal solution. -/
def run (empty : RowType) (join : RowType → RowType → RowType)
    (rowCheck : RowType → RowType → Bool) (rows : Fin m → RowType) (problem : Problem m) : Result m RowType :=
  match compile empty join rows problem with
  | none => .unsupported
  | some compiled =>
      match NestedValueSolver.solve rowCheck compiled.graph compiled.constraints with
      | none => .rejected
      | some cache => .saturated compiled cache

theorem compile_none_iff (empty : RowType) (join : RowType → RowType → RowType)
    (rows : Fin m → RowType) (problem : Problem m) :
    compile empty join rows problem = none ↔ splitProblem problem = none := by
  unfold compile
  split
  · rename_i missing
    exact ⟨fun _ => missing, fun _ => rfl⟩
  · rename_i normalized found
    constructor
    · intro impossible; cases impossible
    · intro missing
      rw [found] at missing
      cases missing

theorem run_unsupported_iff (empty : RowType) (join : RowType → RowType → RowType)
    (rowCheck : RowType → RowType → Bool) (rows : Fin m → RowType) (problem : Problem m) :
    (run empty join rowCheck rows problem).status = .unsupported ↔ splitProblem problem = none := by
  rw [← compile_none_iff empty join rows problem]
  unfold run
  cases found : compile empty join rows problem with
  | none => simp [Result.status]
  | some output =>
      cases solved : NestedValueSolver.solve rowCheck output.graph output.constraints <;> simp [solved, Result.status]

/-- An accepted run exposes the exact constructed graph and a closed,
consistent cache produced by the real solver. -/
theorem run_saturated_closed (empty : RowType) (join : RowType → RowType → RowType)
    (rowCheck : RowType → RowType → Bool) (rows : Fin m → RowType) (problem : Problem m)
    (compiled : Compiled m RowType) (cache : List (NestedValueSolver.Edge compiled.size))
    (returned : run empty join rowCheck rows problem = .saturated compiled cache) :
    compile empty join rows problem = some compiled ∧
      NestedValueSolver.Closed compiled.graph compiled.constraints cache ∧
        NestedValueSolver.consistent rowCheck compiled.graph cache = true := by
  unfold run at returned
  split at returned
  · cases returned
  · rename_i actual found
    split at returned
    · cases returned
    · rename_i result solved
      cases returned
      exact ⟨found, NestedValueSolver.solve_closed rowCheck _ _ _ solved⟩

/-- A rejected run excludes every assignment to the original source variables.
The graph is built by the function above; no realizer is supplied as an input. -/
theorem run_rejects (empty : RowType) (join : RowType → RowType → RowType)
    (rowCheck : RowType → RowType → Bool) (leRow : RowType → RowType → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → RowType) (problem : Problem m)
    (rejected : (run empty join rowCheck rows problem).status = .rejected) :
    ¬ ∃ input : Fin m → StructuralBase.Ty RowType,
      Holds (StructuralBase.model RowType empty join leRow) rows input problem := by
  rintro ⟨input, accepted⟩
  cases returned : compile empty join rows problem with
  | none => simp [run, returned, Result.status] at rejected
  | some compiled =>
      cases solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints with
      | some cache => simp [run, returned, solved, Result.status] at rejected
      | none =>
          apply NestedValueSolver.solve_rejects rowCheck leRow rowRefl rowTrans rowExact
            compiled.graph compiled.constraints solved
          refine ⟨compiled.extend (StructuralBase.model RowType empty join leRow) rows input, ?_⟩
          apply (graphModels_structural empty join leRow _ _ _).mp
          exact (compile_extend_exact _ (structuralLatticeRules empty join leRow) rows
            problem compiled returned input).mpr accepted

end Yulang.TypeConstraintGraph
