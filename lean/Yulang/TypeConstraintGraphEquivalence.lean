import Yulang.TypeConstraintGraph

/-!
# Reflecting semantically realized type-constraint graphs

A recursive solver can realize a constructor up to mutual subtyping instead
of literal equality. The finite source compiler still reflects every such
graph solution: each collected source term evaluates to an equivalent node
value under the shared input-variable assignment.

The required constructor laws preserve child equivalence. Records use only
one fixed finite field list on both sides; no congruence of arbitrary record
tails, quotient of malformed tails, or new constructor distribution is assumed.
The source compiler's supported syntax and front decomposition are unchanged.
-/

namespace Yulang.TypeConstraintGraphEquivalence

open Inference TypeConstraintGraph

variable {m n : Nat}

def Equivalent (model : Model) (left right : model.Ty) : Prop :=
  model.subTy left right ∧ model.subTy right left

/-- Only the constructor laws needed for supported collected source terms.
Record congruence compares values along the same known finite field spine. -/
structure CongruenceRules (model : Model) : Prop where
  refl : ∀ value, model.subTy value value
  trans : ∀ {a b c}, model.subTy a b → model.subTy b c → model.subTy a c
  pair : ∀ {a b c d}, Equivalent model a b → Equivalent model c d →
    Equivalent model (model.pair a c) (model.pair b d)
  variant : ∀ label {a b}, Equivalent model a b →
    Equivalent model (model.variant label a) (model.variant label b)
  arrow : ∀ {a b c d} inputRow outputRow,
    Equivalent model a b → Equivalent model c d →
      Equivalent model (model.arrow a inputRow c outputRow) (model.arrow b inputRow d outputRow)
  record : ∀ {size : Nat} (fields : List (Nat × Fin size)) (left right : Fin size → model.Ty),
    (∀ field ∈ fields, Equivalent model (left field.2) (right field.2)) →
      Equivalent model (recordMeaning model left fields) (recordMeaning model right fields)

theorem Equivalent.refl (rules : CongruenceRules model) (value : model.Ty) :
    Equivalent model value value := ⟨rules.refl _, rules.refl _⟩

theorem Equivalent.symm (equivalent : Equivalent model left right) :
    Equivalent model right left := ⟨equivalent.2, equivalent.1⟩

theorem Equivalent.trans (rules : CongruenceRules model)
    (first : Equivalent model a b) (last : Equivalent model b c) : Equivalent model a c :=
  ⟨rules.trans first.1 last.1, rules.trans last.2 first.2⟩

def SemanticNodeMeaning (model : Model) (value : Fin n → model.Ty) (actual : model.Ty) :
    NestedValueSolver.Node n model.Row → Prop
  | .var => True
  | .base scalar => Equivalent model actual (model.base scalar)
  | .bottom => Equivalent model actual model.bottom
  | .top => Equivalent model actual model.top
  | .pair left right => Equivalent model actual (model.pair (value left) (value right))
  | .variant label payload => Equivalent model actual (model.variant label (value payload))
  | .arrow input inputRow output outputRow =>
      Equivalent model actual (model.arrow (value input) inputRow (value output) outputRow)
  | .record fields => Equivalent model actual (recordMeaning model value fields)

def SemanticRealizes (model : Model) (graph : NestedValueSolver.Graph n model.Row)
    (value : Fin n → model.Ty) : Prop :=
  ∀ node, SemanticNodeMeaning model value (value node) (graph node)

def SemanticGraphModels (model : Model) (graph : NestedValueSolver.Graph n model.Row)
    (constraints : List (NestedValueSolver.Edge n)) (value : Fin n → model.Ty) : Prop :=
  SemanticRealizes model graph value ∧ Satisfies model constraints value

theorem semanticNodeMeaning_of_exact (model : Model) (rules : CongruenceRules model)
    (value : Fin n → model.Ty) (actual : model.Ty) (node : NestedValueSolver.Node n model.Row)
    (exact : NodeMeaning model value actual node) : SemanticNodeMeaning model value actual node := by
  cases node with
  | var => trivial
  | _ =>
      change actual = _ at exact
      subst actual
      exact Equivalent.refl rules _

theorem semanticRealizes_of_exact (model : Model) (rules : CongruenceRules model)
    (graph : NestedValueSolver.Graph n model.Row) (value : Fin n → model.Ty)
    (exact : Realizes model graph value) : SemanticRealizes model graph value :=
  fun node => semanticNodeMeaning_of_exact model rules value (value node) (graph node) (exact node)

theorem semanticGraphModels_of_exact (model : Model) (rules : CongruenceRules model)
    (graph : NestedValueSolver.Graph n model.Row) (constraints : List (NestedValueSolver.Edge n))
    (value : Fin n → model.Ty) (exact : GraphModels model graph constraints value) :
    SemanticGraphModels model graph constraints value :=
  ⟨semanticRealizes_of_exact model rules graph value exact.1, exact.2⟩

theorem realizes_reference (pool : Pool m) (model : Model) (rows : Fin m → model.Row)
    (value : Fin pool.size → model.Ty)
    (realizes : SemanticRealizes model (graph pool model.empty model.join rows) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    SemanticNodeMeaning model value (value (pool.reference term member))
      (nodeOf pool model.empty model.join rows term member) := by
  simpa only [graph_reference] using realizes (pool.reference term member)

/-- Every referenced record field is a proper source subterm. This measure
also handles fields reached through an arbitrarily long fixed record spine. -/
theorem indexedFields_smaller (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (field : Nat × Fin pool.size) (present : field ∈ indexedFields pool term member) :
    TypeSimplification.nodes (pool.termAt field.2) < TypeSimplification.nodes term := by
  cases term with
  | record label head rest =>
      rcases List.mem_cons.mp present with same | present
      · subst field
        simp only [Pool.child, Pool.termAt_reference, TypeSimplification.nodes]
        omega
      · have smaller := indexedFields_smaller pool rest _ field present
        simp only [TypeSimplification.nodes]
        omega
  | _ => cases present
termination_by TypeSimplification.nodes term
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [TypeSimplification.nodes]
  all_goals omega

/-- Constructor realization up to subtyping is enough to recover source
evaluation up to subtyping. All original unknowns retain one shared value. -/
theorem realizes_evaluate (pool : Pool m) (model : Model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (value : Fin pool.size → model.Ty)
    (realizes : SemanticRealizes model (graph pool model.empty model.join rows) value)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Equivalent model (value (pool.reference term member))
      (evaluate model rows (fun i => value (pool.input i)) term) := by
  have interpreted := realizes_reference pool model rows value realizes term member
  cases term with
  | var index => exact Equivalent.refl rules _
  | union | inter => have impossible := pool.supported _ member; cases impossible
  | base | bottom | top | emptyRecord => exact interpreted
  | pair left right =>
      have leftEquivalent := realizes_evaluate pool model rules rows value realizes left
        (pool.closed _ member left (by simp [subterms]))
      have rightEquivalent := realizes_evaluate pool model rules rows value realizes right
        (pool.closed _ member right (by simp [subterms]))
      exact Equivalent.trans rules interpreted (rules.pair leftEquivalent rightEquivalent)
  | variant label payload =>
      have payloadEquivalent := realizes_evaluate pool model rules rows value realizes payload
        (pool.closed _ member payload (by simp [subterms]))
      exact Equivalent.trans rules interpreted (rules.variant label payloadEquivalent)
  | arrow input inputRow output outputRow =>
      have inputEquivalent := realizes_evaluate pool model rules rows value realizes input
        (pool.closed _ member input (by simp [subterms]))
      have outputEquivalent := realizes_evaluate pool model rules rows value realizes output
        (pool.closed _ member output (by simp [subterms]))
      have converted := rules.arrow (rowEval model.empty model.join rows inputRow)
        (rowEval model.empty model.join rows outputRow) inputEquivalent outputEquivalent
      simpa only [evaluate, TyTerm.eval, Pool.child, ← rowEval_eq] using
        Equivalent.trans rules interpreted converted
  | record label head rest =>
      have checks : (ValueBoundElimination.recordSpine rest = true ∧ rigid head = true) ∧
          rigid rest = true := by
        simpa only [rigid, Bool.and_eq_true] using pool.supported _ member
      have fieldsEquivalent := rules.record (indexedFields pool (.record label head rest) member)
        value (TypeConstraintGraph.extend pool model rows (fun i => value (pool.input i))) (by
          intro field present
          have equivalent := realizes_evaluate pool model rules rows value realizes
            (pool.termAt field.2) (pool.at_mem field.2)
          simpa only [Pool.reference_termAt, TypeConstraintGraph.extend] using equivalent)
      have converted := Equivalent.trans rules interpreted fieldsEquivalent
      rw [indexedFields_extend pool model rows (fun i => value (pool.input i))
        (.record label head rest) member checks.1.1] at converted
      exact converted
termination_by TypeSimplification.nodes term
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [TypeSimplification.nodes]
  all_goals try omega
  all_goals
    simpa only [TypeSimplification.nodes] using
      indexedFields_smaller pool (.record label head rest) member field present

/-- Every generated edge is equivalent to its original source inequality
under any semantic realizer, including noncanonical recursive solutions. -/
theorem compiledEdges_exact (model : Model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (valid : RigidProblem problem)
    (value : Fin (collect problem valid).size → model.Ty)
    (realizes : SemanticRealizes model (graph (collect problem valid) model.empty model.join rows) value) :
    Satisfies model (compiledEdges problem valid) value ↔
      Holds model rows (fun i => value ((collect problem valid).input i)) problem := by
  constructor
  · intro accepted edge member
    have generated := accepted _ (List.mem_map.mpr ⟨⟨edge, member⟩, by simp, rfl⟩)
    have source := realizes_evaluate (collect problem valid) model rules rows value realizes
      edge.1 (collect_covers problem valid edge member).1
    have target := realizes_evaluate (collect problem valid) model rules rows value realizes
      edge.2 (collect_covers problem valid edge member).2
    exact rules.trans source.2 (rules.trans generated target.1)
  · intro accepted edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    have source := realizes_evaluate (collect problem valid) model rules rows value realizes
      original.val.1 (collect_covers problem valid original.val original.property).1
    have target := realizes_evaluate (collect problem valid) model rules rows value realizes
      original.val.2 (collect_covers problem valid original.val original.property).2
    exact rules.trans source.1 (rules.trans (accepted original.val original.property) target.2)

theorem build_models_iff (model : Model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (valid : RigidProblem problem)
    (value : Fin (build model.empty model.join rows problem valid).size → model.Ty) :
    SemanticGraphModels model (build model.empty model.join rows problem valid).graph
        (build model.empty model.join rows problem valid).constraints value ↔
      SemanticRealizes model (build model.empty model.join rows problem valid).graph value ∧
        Holds model rows ((build model.empty model.join rows problem valid).restrict value) problem := by
  constructor
  · rintro ⟨realizes, accepted⟩
    exact ⟨realizes, (compiledEdges_exact model rules rows problem valid value realizes).mp accepted⟩
  · rintro ⟨realizes, accepted⟩
    exact ⟨realizes, (compiledEdges_exact model rules rows problem valid value realizes).mpr accepted⟩

/-- The original inequalities are recovered from a semantic graph model.
The lattice rules serve only the existing exact front decomposition. -/
theorem compile_models_iff (model : Model) (lattice : LatticeRules model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled)
    (value : Fin compiled.size → model.Ty) :
    SemanticGraphModels model compiled.graph compiled.constraints value ↔
      SemanticRealizes model compiled.graph value ∧ Holds model rows (compiled.restrict value) problem := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  rw [build_models_iff model rules, splitProblem_some_exact model lattice rows _ problem normalized split]

theorem compile_extend_realizes (model : Model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    SemanticRealizes model compiled.graph (compiled.extend model rows input) := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  exact semanticRealizes_of_exact model rules _ _ (build_realizes model rows normalized _ input)

/-- Canonical extension remains an exact forward interpretation; permitting
semantic realizers does not require weakening any source constraint. -/
theorem compile_extend_exact (model : Model) (lattice : LatticeRules model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    SemanticGraphModels model compiled.graph compiled.constraints (compiled.extend model rows input) ↔
      Holds model rows input problem := by
  rw [compile_models_iff model lattice rules rows problem compiled returned,
    compile_restrict_extend model rows problem compiled returned input]
  exact and_iff_right (compile_extend_realizes model rules rows problem compiled returned input)

/-- Restriction followed by canonical extension recovers every semantic
realizer pointwise up to mutual subtyping, without quotienting its carrier. -/
theorem compile_retraction (model : Model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled)
    (value : Fin compiled.size → model.Ty) (realizes : SemanticRealizes model compiled.graph value) :
    ∀ node, Equivalent model (compiled.extend model rows (compiled.restrict value) node) (value node) := by
  obtain ⟨normalized, split, rfl⟩ := compile_some _ _ _ _ _ returned
  intro node
  have equivalent := realizes_evaluate (collect normalized (splitProblem_some_rigid problem normalized split))
    model rules rows value realizes _ ((collect normalized _).at_mem node)
  have same := congrArg value (Pool.reference_termAt
    (collect normalized (splitProblem_some_rigid problem normalized split)) node)
  rw [same] at equivalent
  exact equivalent.symm

/-- Fixed-assignment exactness, with arbitrary semantic graph models on the
right. The shared input values themselves are preserved by literal equality. -/
theorem compile_assignment_exact (model : Model) (lattice : LatticeRules model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled) (input : Fin m → model.Ty) :
    Holds model rows input problem ↔
      ∃ value : Fin compiled.size → model.Ty,
        SemanticGraphModels model compiled.graph compiled.constraints value ∧ compiled.restrict value = input := by
  constructor
  · intro accepted
    exact ⟨compiled.extend model rows input,
      (compile_extend_exact model lattice rules rows problem compiled returned input).mpr accepted,
      compile_restrict_extend model rows problem compiled returned input⟩
  · rintro ⟨value, accepted, agrees⟩
    have original := ((compile_models_iff model lattice rules rows problem compiled returned value).mp accepted).2
    simpa only [agrees] using original

/-- Source output variables are the same shared input-node values. This
compares all upward instances, not only satisfiability or a single witness. -/
theorem compile_output_instances_exact (model : Model) (lattice : LatticeRules model) (rules : CongruenceRules model)
    (rows : Fin m → model.Row) (problem : Problem m) (compiled : Compiled m model.Row)
    (returned : compile model.empty model.join rows problem = some compiled)
    (output : Fin m) (expected : model.Ty) :
    (∃ input, Holds model rows input problem ∧ model.subTy (input output) expected) ↔
      ∃ value, SemanticGraphModels model compiled.graph compiled.constraints value ∧
        model.subTy (value (compiled.input output)) expected := by
  constructor
  · rintro ⟨input, accepted, below⟩
    obtain ⟨value, graphModel, agrees⟩ :=
      (compile_assignment_exact model lattice rules rows problem compiled returned input).mp accepted
    refine ⟨value, graphModel, ?_⟩
    rw [← agrees] at below
    exact below
  · rintro ⟨value, accepted, below⟩
    exact ⟨compiled.restrict value,
      ((compile_models_iff model lattice rules rows problem compiled returned value).mp accepted).2, below⟩

end Yulang.TypeConstraintGraphEquivalence
