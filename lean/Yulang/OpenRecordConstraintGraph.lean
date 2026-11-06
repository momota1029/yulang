import Yulang.RecordConstraintSupport

/-!
# Total finite constraint graphs retaining open record tails

This compiler collects the original value terms into a finite shared graph.
It retains union/intersection nodes and gives record extension two references:
the head value and the complete tail. In particular an unknown tail is never
flattened into the empty list of known fields. Arrow rows and explicit row
constraints keep the original computation-slot indices.

Constructor realization uses the operations of an arbitrary `Inference.Model`.
The compiler needs no subtype law, record law, model, assignment or successful
solver run. The exactness results cover all original assignments and output
instances. They certify this compilation stage, not a constraint solver or a
free-parameter principal scheme.
-/

namespace Yulang.OpenRecordConstraintGraph

open Inference
open TypeConstraintGraph (subterms self_mem_subterms subterms_trans unique mem_unique
  unique_nodup rawTerms evaluate rowEval rowEval_eq)

variable {m n : Nat}

/-- Unlike the fixed-spine solver graph, this representation retains the
tail child of every record, including unknown or compound tails. -/
inductive Node (inputs size : Nat) where
  | input : Fin inputs → Node inputs size
  | base : Base → Node inputs size
  | bottom : Node inputs size
  | top : Node inputs size
  | union : Fin size → Fin size → Node inputs size
  | inter : Fin size → Fin size → Node inputs size
  | pair : Fin size → Fin size → Node inputs size
  | emptyRecord : Node inputs size
  | recordExtend : Nat → Fin size → Fin size → Node inputs size
  | variant : Nat → Fin size → Node inputs size
  | arrow : Fin size → RowTerm (Fin inputs) → Fin size → RowTerm (Fin inputs) → Node inputs size
  deriving DecidableEq

abbrev Graph (inputs size : Nat) := Fin size → Node inputs size
abbrev Edge (size : Nat) := Fin size × Fin size

/-- Finite compiler output. `source` records node provenance; the graph
itself uses only constructor tags and finite child references. -/
structure Compiled (inputs : Nat) where
  size : Nat
  graph : Graph inputs size
  constraints : List (Edge size)
  rows : RowFlowSchemes.Problem inputs
  input : Fin inputs → Fin size
  source : Fin size → TyTerm (Fin inputs)

/-- Every input slot is present even if no constraint mentions it. -/
structure Pool (m : Nat) where
  terms : List (TyTerm (Fin m))
  distinct : terms.Nodup
  variables : ∀ index, .var index ∈ terms
  closed : ∀ term ∈ terms, ∀ part ∈ subterms term, part ∈ terms

def collect (problem : TypeConstraintGraph.Problem m) : Pool m where
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

theorem collect_covers (problem : TypeConstraintGraph.Problem m)
    (edge : TyTerm (Fin m) × TyTerm (Fin m)) (member : edge ∈ problem) :
    edge.1 ∈ (collect problem).terms ∧ edge.2 ∈ (collect problem).terms := by
  constructor <;> apply (mem_unique _ _).mpr <;> apply List.mem_append_right <;>
    apply List.mem_flatMap.mpr
  · exact ⟨edge, member, List.mem_append_left _ (self_mem_subterms _)⟩
  · exact ⟨edge, member, List.mem_append_right _ (self_mem_subterms _)⟩

namespace Pool

def size (pool : Pool m) : Nat := pool.terms.length

def termAt (pool : Pool m) (index : Fin pool.size) : TyTerm (Fin m) :=
  pool.terms[index.val]'index.isLt

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

def input (pool : Pool m) (index : Fin m) : Fin pool.size :=
  pool.reference (.var index) (pool.variables index)

theorem input_injective (pool : Pool m) : Function.Injective pool.input := by
  intro first second same
  have equal := congrArg pool.termAt same
  simpa only [input, termAt_reference, TyTerm.var.injEq] using equal

def child (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (part : TyTerm (Fin m)) (inside : part ∈ subterms term) : Fin pool.size :=
  pool.reference part (pool.closed term member part inside)

end Pool

def nodeOf (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : Node m pool.size :=
  match term with
  | .var index => .input index
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union left right =>
      .union (pool.child _ member left (by simp [subterms]))
        (pool.child _ member right (by simp [subterms]))
  | .inter left right =>
      .inter (pool.child _ member left (by simp [subterms]))
        (pool.child _ member right (by simp [subterms]))
  | .pair left right =>
      .pair (pool.child _ member left (by simp [subterms]))
        (pool.child _ member right (by simp [subterms]))
  | .emptyRecord => .emptyRecord
  | .record label head tail =>
      .recordExtend label (pool.child _ member head (by simp [subterms]))
        (pool.child _ member tail (by simp [subterms]))
  | .variant label payload => .variant label (pool.child _ member payload (by simp [subterms]))
  | .arrow input inputRow output outputRow =>
      .arrow (pool.child _ member input (by simp [subterms])) inputRow
        (pool.child _ member output (by simp [subterms])) outputRow

def graph (pool : Pool m) : Graph m pool.size :=
  fun index => nodeOf pool (pool.termAt index) (pool.at_mem index)

@[simp] theorem graph_reference (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    graph pool (pool.reference term member) = nodeOf pool term member := by
  simp only [graph, Pool.termAt_reference]

/-- Node interpretation depends only on the original model operations. -/
def Node.eval (model : Model) (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (value : Fin n → model.Ty) : Node m n → model.Ty
  | .input index => input index
  | .base scalar => model.base scalar
  | .bottom => model.bottom
  | .top => model.top
  | .union left right => model.union (value left) (value right)
  | .inter left right => model.inter (value left) (value right)
  | .pair left right => model.pair (value left) (value right)
  | .emptyRecord => model.emptyRecord
  | .recordExtend label head tail => model.record label (value head) (value tail)
  | .variant label payload => model.variant label (value payload)
  | .arrow arg argRow result resultRow =>
      model.arrow (value arg) (rowEval model.empty model.join rows argRow)
        (value result) (rowEval model.empty model.join rows resultRow)

def Realizes (model : Model) (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (nodes : Graph m n) (value : Fin n → model.Ty) : Prop :=
  ∀ index, value index = (nodes index).eval model input rows value

def Satisfies (model : Model) (constraints : List (Edge n)) (value : Fin n → model.Ty) : Prop :=
  ∀ edge ∈ constraints, model.subTy (value edge.1) (value edge.2)

def extend (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) : Fin pool.size → model.Ty :=
  fun index => evaluate model rows input (pool.termAt index)

@[simp] theorem extend_reference (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    extend pool model input rows (pool.reference term member) = evaluate model rows input term := by
  simp only [extend, Pool.termAt_reference]

@[simp] theorem extend_input (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) (index : Fin m) :
    extend pool model input rows (pool.input index) = input index := by
  simp only [Pool.input, extend_reference, evaluate, TyTerm.eval]

theorem extend_nodeOf (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    evaluate model rows input term =
      (nodeOf pool term member).eval model input rows (extend pool model input rows) := by
  cases term <;> simp only [nodeOf, Node.eval, Pool.child, extend_reference,
    evaluate, TyTerm.eval, rowEval_eq model rows input]

theorem extend_realizes (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) :
    Realizes model input rows (graph pool) (extend pool model input rows) := by
  intro index
  exact extend_nodeOf pool model input rows (pool.termAt index) (pool.at_mem index)

/-- Every graph realization is the original term evaluation, including
the complete tail of a record extension. -/
theorem realizes_evaluate (pool : Pool m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) (value : Fin pool.size → model.Ty)
    (realizes : Realizes model input rows (graph pool) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    value (pool.reference term member) = evaluate model rows input term := by
  have interpreted := realizes (pool.reference term member)
  rw [graph_reference] at interpreted
  cases term with
  | var | base | bottom | top | emptyRecord => exact interpreted
  | union left right | inter left right | pair left right | record _ left right =>
      simpa only [nodeOf, Node.eval, Pool.child, evaluate, TyTerm.eval,
        realizes_evaluate pool model input rows value realizes left,
        realizes_evaluate pool model input rows value realizes right] using interpreted
  | variant label payload =>
      simpa only [nodeOf, Node.eval, Pool.child, evaluate, TyTerm.eval,
        realizes_evaluate pool model input rows value realizes payload] using interpreted
  | arrow arg argRow result resultRow =>
      simpa only [nodeOf, Node.eval, Pool.child, evaluate, TyTerm.eval, rowEval_eq model rows input,
        realizes_evaluate pool model input rows value realizes arg,
        realizes_evaluate pool model input rows value realizes result] using interpreted
termination_by TypeSimplification.nodes term
decreasing_by all_goals simp_all [TypeSimplification.nodes] <;> omega

def compiledEdges (problem : TypeConstraintGraph.Problem m) : List (Edge (collect problem).size) :=
  problem.attach.map fun edge =>
    ((collect problem).reference edge.val.1 (collect_covers problem edge.val edge.property).1,
      (collect problem).reference edge.val.2 (collect_covers problem edge.val edge.property).2)

/-- Total compilation. No syntactic support check or semantic oracle is an
input, and a conflicting problem is still represented exactly. -/
def compile (problem : ConstraintProblems.Problem m) : Compiled m where
  size := (collect problem.types).size
  graph := graph (collect problem.types)
  constraints := compiledEdges problem.types
  rows := problem.rows
  input := (collect problem.types).input
  source := (collect problem.types).termAt

def Compiled.extend (compiled : Compiled m) (model : Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) : Fin compiled.size → model.Ty :=
  fun index => evaluate model rows input (compiled.source index)

def Compiled.restrict (compiled : Compiled m) (value : Fin compiled.size → α) : Fin m → α :=
  fun index => value (compiled.input index)

def Compiled.Models (compiled : Compiled m) (model : Model)
    (value : Fin compiled.size → model.Ty) (rows : Fin m → model.Row) : Prop :=
  Realizes model (compiled.restrict value) rows compiled.graph value ∧
    Satisfies model compiled.constraints value ∧ ConstraintProblems.RowHolds model rows compiled.rows

def Compiled.Instance (compiled : Compiled m) (model : Model) (output : Fin m)
    (target : Comp model) : Prop :=
  ∃ value rows, compiled.Models model value rows ∧
    Comp.le model (value (compiled.input output), rows output) target

theorem compile_input_injective (problem : ConstraintProblems.Problem m) :
    Function.Injective (compile problem).input := Pool.input_injective _

@[simp] theorem compile_restrict_extend (model : Model) (problem : ConstraintProblems.Problem m)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row) :
    (compile problem).restrict ((compile problem).extend model input rows) = input := by
  funext index
  exact extend_input _ model input rows index

theorem compile_realizes (model : Model) (problem : ConstraintProblems.Problem m)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row) :
    Realizes model input rows (compile problem).graph ((compile problem).extend model input rows) :=
  extend_realizes _ model input rows

theorem compiledEdges_exact (model : Model) (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (problem : TypeConstraintGraph.Problem m) (value : Fin (collect problem).size → model.Ty)
    (realizes : Realizes model input rows (graph (collect problem)) value) :
    Satisfies model (compiledEdges problem) value ↔ TypeConstraintGraph.Holds model rows input problem := by
  constructor
  · intro accepted edge member
    have generated := accepted _ (List.mem_map.mpr ⟨⟨edge, member⟩, by simp, rfl⟩)
    simpa only [realizes_evaluate _ _ _ _ _ realizes] using generated
  · intro accepted edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    simpa only [realizes_evaluate _ _ _ _ _ realizes] using accepted original.val original.property

/-- Exactness at every graph assignment, with constructor realization stated
explicitly rather than hidden inside an assumed successful solve. -/
theorem compile_models_iff (model : Model) (problem : ConstraintProblems.Problem m)
    (value : Fin (compile problem).size → model.Ty) (rows : Fin m → model.Row) :
    (compile problem).Models model value rows ↔
      Realizes model ((compile problem).restrict value) rows (compile problem).graph value ∧
        problem.Holds model ((compile problem).restrict value) rows := by
  unfold Compiled.Models ConstraintProblems.Problem.Holds
  apply and_congr_right
  intro realizes
  exact and_congr_left (fun _ => compiledEdges_exact model _ rows problem.types value realizes)

/-- The compiler constructs the unique graph extension of each original
assignment. No satisfiability premise is required to construct it. -/
theorem compile_extend_exact (model : Model) (problem : ConstraintProblems.Problem m)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row) :
    (compile problem).Models model ((compile problem).extend model input rows) rows ↔
      problem.Holds model input rows := by
  rw [compile_models_iff, compile_restrict_extend]
  exact and_iff_right (compile_realizes model problem input rows)

theorem compile_retraction (model : Model) (problem : ConstraintProblems.Problem m)
    (value : Fin (compile problem).size → model.Ty) (rows : Fin m → model.Row)
    (realizes : Realizes model ((compile problem).restrict value) rows (compile problem).graph value) :
    (compile problem).extend model ((compile problem).restrict value) rows = value := by
  funext index
  have same := realizes_evaluate (collect problem.types) model _ rows value realizes _
    ((collect problem.types).at_mem index)
  exact same.symm.trans (congrArg value (Pool.reference_termAt _ index))

theorem compile_assignment_exact (model : Model) (problem : ConstraintProblems.Problem m)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row) :
    problem.Holds model input rows ↔
      ∃ value : Fin (compile problem).size → model.Ty,
        (compile problem).Models model value rows ∧ (compile problem).restrict value = input := by
  constructor
  · intro held
    exact ⟨(compile problem).extend model input rows,
      (compile_extend_exact model problem input rows).mpr held,
      compile_restrict_extend model problem input rows⟩
  · rintro ⟨value, modeled, agrees⟩
    have original := ((compile_models_iff model problem value rows).mp modeled).2
    simpa only [agrees] using original

/-- All target instances are preserved, for every inference model, original
problem and output slot. The statement invokes the actual total compiler. -/
theorem compile_instances_exact (model : Model) (problem : ConstraintProblems.Problem m)
    (output : Fin m) (target : Comp model) :
    (compile problem).Instance model output target ↔ problem.Instance model output target := by
  constructor
  · rintro ⟨value, rows, modeled, bounded⟩
    exact ⟨(compile problem).restrict value, rows,
      ((compile_models_iff model problem value rows).mp modeled).2, bounded⟩
  · rintro ⟨input, rows, held, bounded⟩
    refine ⟨(compile problem).extend model input rows, rows,
      (compile_extend_exact model problem input rows).mpr held, ?_⟩
    change Comp.le model ((compile problem).restrict
      ((compile problem).extend model input rows) output, rows output) target
    rw [compile_restrict_extend]
    exact bounded

/-! ## Actual graph grammar for the prepared source core -/

/-- Each record node really retains both original children, with the tail's
complete source term as its provenance. No tail normalization is performed. -/
theorem compile_record_children (problem : ConstraintProblems.Problem m)
    (index : Fin (compile problem).size) (label : Nat) (head tail : TyTerm (Fin m))
    (source : (compile problem).source index = .record label head tail) :
    ∃ headRef tailRef, (compile problem).graph index = .recordExtend label headRef tailRef ∧
      (compile problem).source headRef = head ∧ (compile problem).source tailRef = tail := by
  change Fin (collect problem.types).size at index
  change (collect problem.types).termAt index = .record label head tail at source
  have member := (collect problem.types).at_mem index
  rw [source] at member
  let headRef := (collect problem.types).child _ member head (by simp [subterms])
  let tailRef := (collect problem.types).child _ member tail (by simp [subterms])
  refine ⟨headRef, tailRef, ?_, ?_, ?_⟩
  · change graph (collect problem.types) index = _
    have reference : (collect problem.types).reference (.record label head tail) member = index := by
      simpa only [source] using (collect problem.types).reference_termAt index
    rw [← reference, graph_reference]
    rfl
  · exact Pool.termAt_reference _ head _
  · exact Pool.termAt_reference _ tail _

private theorem sourceHead_subterms (source part : TyTerm (Fin m))
    (good : RecordConstraintSupport.sourceHead source = true) (inside : part ∈ subterms source) :
    RecordConstraintSupport.sourceHead part = true := by
  by_cases same : part = source
  · subst part
    exact good
  · exact RecordConstraintSupport.demand_implies_head
      (RecordConstraintSupport.sourceHead_proper_subterm source part good inside same)

/-- Preparation needs only the graph grammar already generated by the
source core: rigid demand terms and possibly an outer open record extension. -/
theorem compile_prepared_node_grammar (problem : ConstraintProblems.Problem m)
    (prepared : RecordConstraintSupport.PreparedTypes problem.types)
    (index : Fin (compile problem).size) :
    RecordConstraintSupport.sourceHead ((compile problem).source index) = true := by
  have member := (mem_unique _ _).mp ((collect problem.types).at_mem index)
  rcases List.mem_append.mp member with fromVars | fromProblem
  · obtain ⟨input, _, same⟩ := List.mem_map.mp fromVars
    change RecordConstraintSupport.sourceHead ((collect problem.types).termAt index) = true
    rw [← same]
    rfl
  · obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp fromProblem
    rcases List.mem_append.mp inside with fromSource | fromTarget
    · exact sourceHead_subterms _ _ (prepared edge present).1 fromSource
    · exact RecordConstraintSupport.demand_implies_head
        (SourceConstraintSupport.simpleTy_subterms _ _ (prepared edge present).2 fromTarget)

theorem compile_prepared_upper_grammar (problem : ConstraintProblems.Problem m)
    (prepared : RecordConstraintSupport.PreparedTypes problem.types)
    (edge : Edge (compile problem).size) (member : edge ∈ (compile problem).constraints) :
    RecordConstraintSupport.demandTy ((compile problem).source edge.2) = true := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  simpa only [compile, Pool.termAt_reference] using (prepared original.val original.property).2

/-- Every graph node with an open record tail is the lower root of an
actual original constraint. This holds independently of satisfiability. -/
theorem compile_prepared_open_roots (problem : ConstraintProblems.Problem m)
    (prepared : RecordConstraintSupport.PreparedTypes problem.types)
    (index : Fin (compile problem).size)
    (opened : RecordConstraintSupport.openRecord ((compile problem).source index) = true) :
    ∃ edge ∈ (compile problem).constraints, edge.1 = index := by
  change Fin (collect problem.types).size at index
  change RecordConstraintSupport.openRecord ((collect problem.types).termAt index) = true at opened
  have member := (mem_unique _ _).mp ((collect problem.types).at_mem index)
  rcases List.mem_append.mp member with fromVars | fromProblem
  · obtain ⟨input, _, same⟩ := List.mem_map.mp fromVars
    rw [← same] at opened
    cases opened
  · obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp fromProblem
    rcases List.mem_append.mp inside with fromSource | fromTarget
    · have same := RecordConstraintSupport.sourceHead_open_subterm _ _
        (prepared edge present).1 fromSource opened
      refine ⟨_, List.mem_map.mpr ⟨⟨edge, present⟩, by simp, rfl⟩, ?_⟩
      change (collect problem.types).reference edge.1 (collect_covers problem.types edge present).1 = index
      simpa only [same] using (collect problem.types).reference_termAt index
    · have absent := RecordConstraintSupport.demand_no_open_subterm _ _
        (prepared edge present).2 fromTarget
      rw [opened] at absent
      cases absent

/-! ## One total compilation entry from every original closed core expression -/

structure SourceAlternative where
  inputs : Nat
  compiled : Compiled inputs
  output : Fin inputs

def compileClause (clause : ConstraintNormalForm.Clause (Option Empty)) : SourceAlternative :=
  ⟨clause.locals + 1, compile (RecordConstraintSupport.prepare (ConstraintProblems.split clause.pack)),
    Fin.last clause.locals⟩

def compileSource (expression : Expr) : List SourceAlternative :=
  (ConstraintNormalForm.normalise (principal ([] : SchemeEnv Empty) expression)).map compileClause

def SourceAlternative.Instance (model : Model) (alternative : SourceAlternative)
    (target : Comp model) : Prop := alternative.compiled.Instance model alternative.output target

def SourceInstance (model : Model) (alternatives : List SourceAlternative) (target : Comp model) : Prop :=
  ∃ alternative ∈ alternatives, alternative.Instance model target

/-- The original closed judgment is exactly the finite family of compiled
graph models, for all source constructors including record extension. Graph
constraints remain to be solved; this is not a free-parameter scheme theorem. -/
theorem compileSource_instances_exact (model : Model)
    (unionIsJoin : RecordConstraintSupport.UnionIsJoin model)
    (tyRefl : ∀ type, model.subTy type type)
    (tyTrans : ∀ {a b c}, model.subTy a b → model.subTy b c → model.subTy a c)
    (rowRefl : ∀ row, model.subRow row row)
    (rowTrans : ∀ {a b c}, model.subRow a b → model.subRow b c → model.subRow a c)
    (expression : Expr) (target : Comp model) :
    SourceInstance model (compileSource expression) target ↔ Typing model [] expression target := by
  rw [RecordConstraintSupport.closed_prepared_typing_exact model unionIsJoin
    tyRefl tyTrans rowRefl rowTrans expression target]
  constructor
  · rintro ⟨alternative, member, accepted⟩
    obtain ⟨clause, present, rfl⟩ := List.mem_map.mp member
    exact ⟨clause, present, (compile_instances_exact model _ _ _).mp accepted⟩
  · rintro ⟨clause, present, accepted⟩
    exact ⟨compileClause clause, List.mem_map.mpr ⟨clause, present, rfl⟩,
      (compile_instances_exact model _ _ _).mpr accepted⟩

theorem compileSource_node_grammar (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (index : Fin alternative.compiled.size) :
    RecordConstraintSupport.sourceHead (alternative.compiled.source index) = true := by
  obtain ⟨clause, present, rfl⟩ := List.mem_map.mp member
  exact compile_prepared_node_grammar _
    (RecordConstraintSupport.closed_prepared_polar expression clause present).1 index

theorem compileSource_upper_grammar (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (edge : Edge alternative.compiled.size)
    (present : edge ∈ alternative.compiled.constraints) :
    RecordConstraintSupport.demandTy (alternative.compiled.source edge.2) = true := by
  obtain ⟨clause, chosen, rfl⟩ := List.mem_map.mp member
  exact compile_prepared_upper_grammar _
    (RecordConstraintSupport.closed_prepared_polar expression clause chosen).1 edge present

theorem compileSource_open_roots (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (index : Fin alternative.compiled.size)
    (opened : RecordConstraintSupport.openRecord (alternative.compiled.source index) = true) :
    ∃ edge ∈ alternative.compiled.constraints, edge.1 = index := by
  obtain ⟨clause, chosen, rfl⟩ := List.mem_map.mp member
  exact compile_prepared_open_roots _
    (RecordConstraintSupport.closed_prepared_polar expression clause chosen).1 index opened

end Yulang.OpenRecordConstraintGraph
