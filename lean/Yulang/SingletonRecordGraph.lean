import Yulang.SingletonRecordDemands
import Yulang.OpenRecordConstraintGraph
import Yulang.RigidRecordFields

/-!
# Singleton demands and erasure inside the actual source graph

Every upper endpoint and every proper constructor subterm in the original
compiled source graphs satisfies the singleton-demand invariant. Erasing a
label from a rigid demand therefore selects the original node or its existing
empty-record tail. No new masked-demand node or extra source slot is needed.

These are grammar and representation theorems. They neither solve the graph
nor alter how its unknown slots, including open record tails, are interpreted.
-/

namespace Yulang.SingletonRecordGraph

open Inference OpenRecordConstraintGraph
open TypeConstraintGraph (subterms mem_unique)
open SingletonRecordDemands (demandTy sourceHead PreparedTypes)

variable {m : Nat}

theorem compile_prepared_node_grammar (problem : ConstraintProblems.Problem m)
    (prepared : PreparedTypes problem.types) (index : Fin (compile problem).size) :
    sourceHead ((compile problem).source index) = true := by
  have member := (mem_unique _ _).mp ((collect problem.types).at_mem index)
  rcases List.mem_append.mp member with fromVars | fromProblem
  · obtain ⟨input, _, same⟩ := List.mem_map.mp fromVars
    change sourceHead ((collect problem.types).termAt index) = true
    rw [← same]
    rfl
  · obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp fromProblem
    rcases List.mem_append.mp inside with fromSource | fromTarget
    · exact SingletonRecordDemands.sourceHead_subterms _ _ (prepared edge present).1 fromSource
    · exact SingletonRecordDemands.demand_implies_head
        (SingletonRecordDemands.demandTy_subterms _ _ (prepared edge present).2 fromTarget)

theorem compile_prepared_upper_grammar (problem : ConstraintProblems.Problem m)
    (prepared : PreparedTypes problem.types) (edge : Edge (compile problem).size)
    (member : edge ∈ (compile problem).constraints) :
    demandTy ((compile problem).source edge.2) = true := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  simpa only [compile, Pool.termAt_reference] using (prepared original.val original.property).2

/-- Whole-core support; there is no `RecordFree`, typability, or successful
solver premise. Open constructions remain allowed as lower roots. -/
theorem compileSource_node_grammar (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (index : Fin alternative.compiled.size) :
    sourceHead (alternative.compiled.source index) = true := by
  obtain ⟨clause, present, rfl⟩ := List.mem_map.mp member
  exact compile_prepared_node_grammar _
    (SingletonRecordDemands.closed_prepared_polar expression clause present).1 index

theorem compileSource_upper_grammar (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (edge : Edge alternative.compiled.size)
    (present : edge ∈ alternative.compiled.constraints) :
    demandTy (alternative.compiled.source edge.2) = true := by
  obtain ⟨clause, chosen, rfl⟩ := List.mem_map.mp member
  exact compile_prepared_upper_grammar _
    (SingletonRecordDemands.closed_prepared_polar expression clause chosen).1 edge present

theorem compileSource_upper_subterm (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (edge : Edge alternative.compiled.size)
    (present : edge ∈ alternative.compiled.constraints) (part : TyTerm (Fin alternative.inputs))
    (inside : part ∈ subterms (alternative.compiled.source edge.2)) : demandTy part = true :=
  SingletonRecordDemands.demandTy_subterms _ _
    (compileSource_upper_grammar expression alternative member edge present) inside

/-- In particular, constructor children exposed by decomposition are demands.
This also applies to the tail child of an open-record lower root. -/
theorem compileSource_proper_subterm (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (index : Fin alternative.compiled.size)
    (part : TyTerm (Fin alternative.inputs))
    (inside : part ∈ subterms (alternative.compiled.source index))
    (different : part ≠ alternative.compiled.source index) : demandTy part = true :=
  SingletonRecordDemands.sourceHead_proper_subterm _ _
    (compileSource_node_grammar expression alternative member index) inside different

/-- An explicit record at any original upper endpoint has exactly an empty
syntactic tail. Its field payload may contain arbitrary unknown slots. -/
theorem compileSource_upper_record_shape (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (edge : Edge alternative.compiled.size)
    (present : edge ∈ alternative.compiled.constraints) (label : Nat)
    (value rest : TyTerm (Fin alternative.inputs))
    (source : alternative.compiled.source edge.2 = .record label value rest) :
    rest = .emptyRecord ∧ demandTy value = true := by
  have good := compileSource_upper_grammar expression alternative member edge present
  rw [source] at good
  exact (SingletonRecordDemands.demand_record_iff label value rest).mp good

/-! ## Exact erasure without extending the finite reference universe -/

/-- Syntactic counterpart of `RigidRecordFields.erase`; field payloads are
never changed, and only the record spine is traversed. -/
def eraseDemand (label : Nat) : TyTerm α → TyTerm α
  | .record name value rest =>
      if label = name then eraseDemand label rest else .record name value (eraseDemand label rest)
  | term => term

@[simp] theorem eraseDemand_empty (label : Nat) :
    eraseDemand label (.emptyRecord : TyTerm α) = .emptyRecord := rfl

@[simp] theorem eraseDemand_singleton (label name : Nat) (value : TyTerm α) :
    eraseDemand label (.record name value .emptyRecord) =
      if label = name then .emptyRecord else .record name value .emptyRecord := by
  simp only [eraseDemand]

theorem eraseDemand_eq_self_or_empty (label : Nat) (target : TyTerm α)
    (good : demandTy target = true)
    (rigid : ValueBoundElimination.recordSpine target = true) :
    eraseDemand label target = target ∨ eraseDemand label target = .emptyRecord := by
  rcases SingletonRecordDemands.demand_record_shape target good rigid with rfl | ⟨name, value, rfl, _⟩
  · exact Or.inl rfl
  · by_cases same : label = name
    · exact Or.inr (by simp [same])
    · exact Or.inl (by simp [same])

theorem eraseDemand_is_subterm (label : Nat) (target : TyTerm (Fin m))
    (good : demandTy target = true)
    (rigid : ValueBoundElimination.recordSpine target = true) :
    eraseDemand label target ∈ subterms target := by
  rcases SingletonRecordDemands.demand_record_shape target good rigid with rfl | ⟨name, value, rfl, _⟩
  · exact TypeConstraintGraph.self_mem_subterms _
  · by_cases same : label = name <;> simp [same, subterms]

/-- Under the stated demand shape, syntactic erasure is exactly the existing
raw-type erasure after every original value/row assignment. -/
theorem eraseDemand_evaluate (Row : Type) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (rows : Fin m → Row) (values : Fin m → StructuralBase.Ty Row)
    (label : Nat) (target : TyTerm (Fin m)) (good : demandTy target = true)
    (rigid : ValueBoundElimination.recordSpine target = true) :
    TypeConstraintGraph.evaluate (StructuralBase.model Row empty join leRow) rows values
      (eraseDemand label target) =
    RigidRecordFields.erase label
      (TypeConstraintGraph.evaluate (StructuralBase.model Row empty join leRow) rows values target) := by
  rcases SingletonRecordDemands.demand_record_shape target good rigid with rfl | ⟨name, value, rfl, _⟩
  · rfl
  · by_cases same : label = name <;>
      simp [eraseDemand, same, TypeConstraintGraph.evaluate, TyTerm.eval,
        StructuralBase.model, RigidRecordFields.erase]

/-- The residual is an existing reference in the original compiler output.
The certificates check representation only, not subtype satisfiability. -/
def maskReference (problem : ConstraintProblems.Problem m) (label : Nat)
    (target : Fin (compile problem).size)
    (good : demandTy ((compile problem).source target) = true)
    (rigid : ValueBoundElimination.recordSpine ((compile problem).source target) = true) :
    Fin (compile problem).size :=
  (collect problem.types).reference (eraseDemand label ((compile problem).source target))
    ((collect problem.types).closed _ ((collect problem.types).at_mem target) _
      (eraseDemand_is_subterm label _ good rigid))

@[simp] theorem maskReference_source (problem : ConstraintProblems.Problem m) (label : Nat)
    (target : Fin (compile problem).size)
    (good : demandTy ((compile problem).source target) = true)
    (rigid : ValueBoundElimination.recordSpine ((compile problem).source target) = true) :
    (compile problem).source (maskReference problem label target good rigid) =
      eraseDemand label ((compile problem).source target) :=
  Pool.termAt_reference _ _ _

theorem maskReference_eq_or_empty (problem : ConstraintProblems.Problem m) (label : Nat)
    (target : Fin (compile problem).size)
    (good : demandTy ((compile problem).source target) = true)
    (rigid : ValueBoundElimination.recordSpine ((compile problem).source target) = true) :
    maskReference problem label target good rigid = target ∨
      (compile problem).source (maskReference problem label target good rigid) = .emptyRecord := by
  rcases eraseDemand_eq_self_or_empty label _ good rigid with same | empty
  · left
    unfold maskReference
    change eraseDemand label ((collect problem.types).termAt target) =
      (collect problem.types).termAt target at same
    change (collect problem.types).reference
      (eraseDemand label ((collect problem.types).termAt target)) _ = target
    simpa only [same] using (collect problem.types).reference_termAt target
  · exact Or.inr ((maskReference_source problem label target good rigid).trans empty)

/-- The actual source compiler's demand erasure never needs a new graph node. -/
theorem compileSource_erasure_closed (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (label : Nat)
    (target : Fin alternative.compiled.size)
    (good : demandTy (alternative.compiled.source target) = true)
    (rigid : ValueBoundElimination.recordSpine (alternative.compiled.source target) = true) :
    ∃ residual : Fin alternative.compiled.size,
      alternative.compiled.source residual = eraseDemand label (alternative.compiled.source target) ∧
        (residual = target ∨ alternative.compiled.source residual = .emptyRecord) := by
  obtain ⟨clause, _, rfl⟩ := List.mem_map.mp member
  exact ⟨maskReference _ label target good rigid, maskReference_source _ label target good rigid,
    maskReference_eq_or_empty _ label target good rigid⟩

end Yulang.SingletonRecordGraph
