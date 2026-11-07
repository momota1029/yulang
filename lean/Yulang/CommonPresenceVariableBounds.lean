import Yulang.CommonBoundCoalescing
import Yulang.CommonPresenceClauseFamily

/-!
# Elimination of variable edges in actual presence constraint graphs

The input is the actual shared pool constructed from presence atoms. Every
edge is classified by whether its endpoints are original variable nodes.
Finite bound coalescing replaces those variable equations with shared
parameter expressions, retaining the original constructor nodes and IDs.
The existing common regular equation solver then closes the resulting graph.

`eliminate_variable_edges_exact` leaves only the finite comparisons between
rigid nodes produced by bound propagation. All variable edges and all
definition witnesses have been eliminated. Parameters may be arbitrary
common types, including regular graphs and negative arrow children.

The simultaneous corollary also eliminates all explicit source row constraints.
Here a bound reads another unknown graph node. After the graph is solved,
that node's value can depend on every parameter family. The remaining rigid
comparisons therefore still restrict the parameters; this is not yet an
unconstrained source-inference family. Their symbolic decomposition and finite
saturation are not performed here; in particular a concrete comparison of
already-instantiated types is not an inference-time checker.
-/

namespace Yulang.CommonPresenceVariableBounds

open Common (Ty Row Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (EdgesHold Realizes restrict)
open LayerBoundTemplates (Constraint Problem)

variable {m : Nat}

def inputAt (pool : Pool m) (slot : Fin pool.size) : Option (Fin m) :=
  match pool.termAt slot with
  | .var index => some index
  | _ => none

@[simp] theorem variable_input (pool : Pool m) (index : Fin m) :
    inputAt pool (pool.input index) = some index := by
  simp only [inputAt, Pool.input, Pool.termAt_reference]

theorem variable_some_iff (pool : Pool m) (slot : Fin pool.size) (index : Fin m) :
    inputAt pool slot = some index ↔ slot = pool.input index := by
  constructor
  · intro found
    unfold inputAt at found
    cases term : pool.termAt slot <;> simp only [term] at found
    case var actual =>
      have same : actual = index := Option.some.inj found
      subst actual
      have reference := Pool.reference_termAt pool slot
      exact (by simpa only [term, Pool.input] using reference : pool.input index = slot).symm
    all_goals cases found
  · intro same
    subst slot
    exact variable_input pool index

def classify (pool : Pool m) (edge : Fin pool.size × Fin pool.size) : Constraint m (Fin pool.size) :=
  match inputAt pool edge.1, inputAt pool edge.2 with
  | some source, some target => .flow source target
  | none, some target => .lower edge.1 target
  | some source, none => .upper source edge.2
  | none, none => .check edge.1 edge.2

def template (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) :
    Problem m (Fin pool.size) := edges.map (classify pool)

def mixed (pool : Pool m) (rigid : Fin pool.size → Ty) (values : Fin m → Ty) : Fin pool.size → Ty :=
  fun slot => match inputAt pool slot with
    | some index => values index
    | none => rigid slot

theorem classify_exact (pool : Pool m) (rigid : Fin pool.size → Ty) (values : Fin m → Ty)
    (edge : Fin pool.size × Fin pool.size) :
    CommonBoundCoalescing.Holds rigid values (classify pool edge) ↔
      Common.Subtype (mixed pool rigid values edge.1) (mixed pool rigid values edge.2) := by
  cases first : inputAt pool edge.1 <;> cases last : inputAt pool edge.2 <;>
    simp only [classify, mixed, first, last, CommonBoundCoalescing.Holds]

theorem template_models_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rigid : Fin pool.size → Ty) (values : Fin m → Ty) :
    CommonBoundCoalescing.Models rigid (template pool edges) values ↔
      EdgesHold edges (mixed pool rigid values) := by
  simp only [CommonBoundCoalescing.Models, template, List.forall_mem_map, classify_exact, EdgesHold]

@[simp] theorem mixed_restrict (pool : Pool m) (values : Fin pool.size → Ty) :
    mixed pool values (restrict pool values) = values := by
  funext slot
  cases found : inputAt pool slot with
  | none => simp only [mixed, found]
  | some index =>
      have same := (variable_some_iff pool slot index).mp found
      simp only [mixed, found, restrict]
      exact congrArg values same.symm

theorem models_of_edges (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (values : Fin pool.size → Ty) (valid : EdgesHold edges values) :
    CommonBoundCoalescing.Models values (template pool edges) (restrict pool values) := by
  rw [template_models_exact, mixed_restrict]
  exact valid

def RigidConstraint (pool : Pool m) : Constraint m (Fin pool.size) → Prop
  | .lower bound _ | .upper _ bound => inputAt pool bound = none
  | .flow _ _ => True
  | .check first last => inputAt pool first = none ∧ inputAt pool last = none

theorem template_rigid (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraint : Constraint m (Fin pool.size)) (member : constraint ∈ template pool edges) :
    RigidConstraint pool constraint := by
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
  cases first : inputAt pool edge.1 <;> cases last : inputAt pool edge.2 <;>
    simp only [classify, first, last, RigidConstraint, and_true]

/-- Both endpoints really are constructor nodes in the original source pool. -/
theorem residuals_rigid (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (comparison : Fin pool.size × Fin pool.size)
    (member : comparison ∈ CommonBoundCoalescing.rigidComparisons (template pool edges)) :
    inputAt pool comparison.1 = none ∧ inputAt pool comparison.2 = none := by
  obtain ⟨constraint, originalMember, contributed⟩ := List.mem_flatMap.mp member
  have rigid := template_rigid pool edges constraint originalMember
  cases constraint with
  | lower | flow => cases contributed
  | upper source bound =>
      obtain ⟨lowerBound, lowerMember, rfl⟩ := List.mem_map.mp contributed
      obtain ⟨start, seed, _⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds (template pool edges) source lowerBound).mp lowerMember
      exact ⟨template_rigid pool edges (.lower lowerBound start) seed, rigid⟩
  | check first last =>
      have same : comparison = (first, last) := List.mem_singleton.mp contributed
      subst comparison
      exact rigid

abbrev Body (pool : Pool m) :=
  CommonPresenceTailLayers.Body pool.size 0 (CommonPresenceTailRegular.Payload pool.size)

def joinBodies (pool : Pool m) : List (Body pool) → Body pool
  | [] => .atom .bottom
  | body :: rest => .union body (joinBodies pool rest)

def meetBodies (pool : Pool m) : List (Body pool) → Body pool
  | [] => .atom .top
  | body :: rest => .inter body (meetBodies pool rest)

def bodyEval (pool : Pool m) (values : Fin pool.size → Ty) (body : Body pool) : Ty :=
  (body.quote (CommonPresenceTailRegular.payload values)).eval values

theorem joinBodies_eval (pool : Pool m) (values : Fin pool.size → Ty) (bodies : List (Body pool)) :
    bodyEval pool values (joinBodies pool bodies) =
      CommonBoundCoalescing.joinTypes (bodies.map (bodyEval pool values)) := by
  induction bodies with
  | nil => rfl
  | cons body rest ih =>
      change CommonSyntax.Layer.union _ (bodyEval pool values (joinBodies pool rest)) = _
      rw [ih]
      rfl

theorem meetBodies_eval (pool : Pool m) (values : Fin pool.size → Ty) (bodies : List (Body pool)) :
    bodyEval pool values (meetBodies pool bodies) =
      CommonBoundCoalescing.meetTypes (bodies.map (bodyEval pool values)) := by
  induction bodies with
  | nil => rfl
  | cons body rest ih =>
      change CommonSyntax.Layer.inter _ (bodyEval pool values (meetBodies pool rest)) = _
      rw [ih]
      rfl

def expandBody (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (parameters : Fin m → Ty) (target : Fin m) : Body pool :=
  .union (joinBodies pool ((LayerBoundTemplates.lowerBounds (template pool edges) target).map .ref))
    (joinBodies pool ((LayerBoundTemplates.ancestors (template pool edges) target).map fun source =>
      .inter (.atom ((parameters source).map Sum.inr))
        (meetBodies pool ((LayerBoundTemplates.upperBounds (template pool edges) source).map .ref))))

private theorem join_map_congr {α : Type} (entries : List α) (first last : α → Ty)
    (same : ∀ entry ∈ entries, Equivalent (first entry) (last entry)) :
    Equivalent (CommonBoundCoalescing.joinTypes (entries.map first))
      (CommonBoundCoalescing.joinTypes (entries.map last)) := by
  induction entries with
  | nil => exact Common.equivalent_refl _
  | cons entry rest ih =>
      have head := same entry (by simp)
      have tail := ih (fun item member => same item (List.mem_cons_of_mem entry member))
      exact ⟨Common.common_union_mono head.1 tail.1, Common.common_union_mono head.2 tail.2⟩

/-- Bound expressions use references to the original rigid node IDs. -/
theorem expandBody_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty) (target : Fin m) :
    Equivalent (bodyEval pool values (expandBody pool edges parameters target))
      (CommonBoundCoalescing.expand values (template pool edges) parameters target) := by
  have refs (slot : Fin pool.size) : bodyEval pool values (.ref slot) = values slot := rfl
  have atoms (index : Fin m) : Equivalent
      (bodyEval pool values (.atom ((parameters index).map Sum.inr))) (parameters index) :=
    CommonPresenceTailRegular.quoted_parameters_equivalent values (fun _ => parameters index) (pool.input index)
  have left : bodyEval pool values
      (joinBodies pool ((LayerBoundTemplates.lowerBounds (template pool edges) target).map .ref)) =
        CommonBoundCoalescing.lower values (template pool edges) target := by
    simp only [joinBodies_eval, List.map_map, Function.comp_def, refs, CommonBoundCoalescing.lower]
  have upper (source : Fin m) : bodyEval pool values
      (meetBodies pool ((LayerBoundTemplates.upperBounds (template pool edges) source).map .ref)) =
        CommonBoundCoalescing.upper values (template pool edges) source := by
    simp only [meetBodies_eval, List.map_map, Function.comp_def, refs, CommonBoundCoalescing.upper]
  have right : Equivalent
      (bodyEval pool values
        (joinBodies pool ((LayerBoundTemplates.ancestors (template pool edges) target).map fun source =>
          .inter (.atom ((parameters source).map Sum.inr))
            (meetBodies pool ((LayerBoundTemplates.upperBounds (template pool edges) source).map .ref)))))
      (CommonBoundCoalescing.variablePart values (template pool edges) parameters target) := by
    rw [joinBodies_eval]
    simp only [List.map_map, Function.comp_def, CommonBoundCoalescing.variablePart]
    apply join_map_congr
    intro source _
    change Equivalent (.inter _ (bodyEval pool values (meetBodies pool _))) _
    rw [upper]
    exact ⟨Common.common_inter_mono (atoms source).1 (Common.subtype_refl _),
      Common.common_inter_mono (atoms source).2 (Common.subtype_refl _)⟩
  have leftSame : Equivalent
      (bodyEval pool values
        (joinBodies pool ((LayerBoundTemplates.lowerBounds (template pool edges) target).map .ref)))
      (CommonBoundCoalescing.lower values (template pool edges) target) := by
    rw [left]
    exact Common.equivalent_refl _
  exact ⟨Common.common_union_mono leftSame.1 right.1,
    Common.common_union_mono leftSame.2 right.2⟩

def coalescedGraph (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) : CommonPresenceTailRegular.Graph pool.size 0 :=
  fun slot => match inputAt pool slot with
    | some index => expandBody pool edges parameters index
    | none => (CommonPresenceConstraintGraph.graph pool slot).atRows rows

theorem graph_input (pool : Pool m) (index : Fin m) :
    CommonPresenceConstraintGraph.graph pool (pool.input index) = .ref (pool.input index) := by
  simp only [Pool.input, CommonPresenceConstraintGraph.graph_reference,
    CommonPresenceConstraintGraph.lowerNode]

/-- The coalesced equations retain exactly the original constructor definitions. -/
theorem coalesced_models_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty) :
    CommonPresenceTailRegular.Models (coalescedGraph pool edges rows parameters) values ↔
      Realizes pool rows values ∧
        ∀ index, Equivalent (CommonBoundCoalescing.expand values (template pool edges) parameters index)
          (restrict pool values index) := by
  constructor
  · intro model
    constructor
    · intro slot
      cases found : inputAt pool slot with
      | none =>
          have valid := model slot
          simpa only [coalescedGraph, found, CommonRowTailInference.Body.eval_atRows] using valid
      | some index =>
          have same := (variable_some_iff pool slot index).mp found
          rw [same, graph_input]
          exact Common.equivalent_refl _
    · intro index
      have valid := model (pool.input index)
      change Equivalent (bodyEval pool values (coalescedGraph pool edges rows parameters (pool.input index))) _ at valid
      rw [coalescedGraph, variable_input] at valid
      exact Common.equivalent_trans (Common.equivalent_symm (expandBody_exact pool edges parameters values index)) valid
  · rintro ⟨realizes, expanded⟩ slot
    cases found : inputAt pool slot with
    | none =>
        simpa only [coalescedGraph, found, CommonRowTailInference.Body.eval_atRows] using realizes slot
    | some index =>
        have same := (variable_some_iff pool slot index).mp found
        change Equivalent (bodyEval pool values (coalescedGraph pool edges rows parameters slot)) _
        rw [coalescedGraph, found]
        exact Common.equivalent_trans (expandBody_exact pool edges parameters values index)
          (by simpa only [restrict, same] using expanded index)

theorem coalesced_satisfies_edges (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (coalescedGraph pool edges rows parameters) values)
    (consistent : CommonBoundCoalescing.Consistent values (template pool edges)) :
    EdgesHold edges values := by
  have expanded := ((coalesced_models_exact pool edges rows parameters values).mp model).2
  have valid := (template_models_exact pool edges values _).mp
    (CommonBoundCoalescing.expand_satisfies consistent parameters)
  apply (CommonPresenceConstraintGraph.edgesHold_congr edges _ values ?_).mp valid
  intro slot
  cases found : inputAt pool slot with
  | none => simpa only [mixed, found] using Common.equivalent_refl (values slot)
  | some index =>
      have same := (variable_some_iff pool slot index).mp found
      simp only [mixed, found]
      simpa only [restrict, same] using expanded index

theorem coalesced_recovers_model (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) :
    CommonPresenceTailRegular.Models (coalescedGraph pool edges rows (restrict pool values)) values :=
  (coalesced_models_exact pool edges rows (restrict pool values) values).mpr
    ⟨realizes, CommonBoundCoalescing.expand_retraction (models_of_edges pool edges values valid)⟩

def solve (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) : Fin pool.size → Ty :=
  CommonPresenceTailRegular.solveBlock (coalescedGraph pool edges rows parameters) recursiveParameters

theorem solve_realizes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) :
    Realizes pool rows (solve pool edges rows parameters recursiveParameters) :=
  ((coalesced_models_exact pool edges rows parameters _).mp
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters)).1

theorem solve_edges (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty)
    (consistent : CommonBoundCoalescing.Consistent
      (solve pool edges rows parameters recursiveParameters) (template pool edges)) :
    EdgesHold edges (solve pool edges rows parameters recursiveParameters) :=
  coalesced_satisfies_edges pool edges rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) consistent

theorem solve_retract (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) (slot : Fin pool.size) :
    Equivalent (solve pool edges rows (restrict pool values) values slot) (values slot) :=
  CommonPresenceTailRegular.solveBlock_retract _ values
    (coalesced_recovers_model pool edges rows values realizes valid) slot

theorem realizes_congr (pool : Pool m) (rows : Fin m → Row) (first last : Fin pool.size → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) :
    Realizes pool rows first ↔ Realizes pool rows last := by
  have exactFirst : Realizes pool rows first ↔ CommonPresenceTailRegular.Models
      (fun slot => (CommonPresenceConstraintGraph.graph pool slot).atRows rows) first := by
    simp only [Realizes, CommonPresenceTailRegular.Models, CommonRowTailInference.Body.eval_atRows]
  have exactLast : Realizes pool rows last ↔ CommonPresenceTailRegular.Models
      (fun slot => (CommonPresenceConstraintGraph.graph pool slot).atRows rows) last := by
    simp only [Realizes, CommonPresenceTailRegular.Models, CommonRowTailInference.Body.eval_atRows]
  rw [exactFirst, exactLast]
  exact CommonPresenceTailRegular.models_congr _ first last same

/-- No original variable edge or definition witness remains. Both parameter
families range over all common types; the displayed rigid comparisons can
still restrict their simultaneous instantiations. -/
theorem eliminate_variable_edges_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (values : Fin pool.size → Ty) :
    Realizes pool rows values ∧ EdgesHold edges values ↔
      ∃ parameters : Fin m → Ty, ∃ recursiveParameters : Fin pool.size → Ty,
        EdgesHold (CommonBoundCoalescing.rigidComparisons (template pool edges))
          (solve pool edges rows parameters recursiveParameters) ∧
        ∀ index, Equivalent (solve pool edges rows parameters recursiveParameters index) (values index) := by
  constructor
  · rintro ⟨realizes, valid⟩
    have same := solve_retract pool edges rows values realizes valid
    refine ⟨restrict pool values, values, ?_, same⟩
    have consistent : EdgesHold (CommonBoundCoalescing.rigidComparisons (template pool edges)) values :=
      (CommonBoundCoalescing.consistent_iff_satisfiable values (template pool edges)).mpr
        ⟨restrict pool values, models_of_edges pool edges values valid⟩
    exact (CommonPresenceConstraintGraph.edgesHold_congr _ _ _ same).mpr consistent
  · rintro ⟨parameters, recursiveParameters, consistent, same⟩
    exact ⟨(realizes_congr pool rows _ values same).mp (solve_realizes pool edges rows parameters recursiveParameters),
      (CommonPresenceConstraintGraph.edgesHold_congr edges _ values same).mp
        (solve_edges pool edges rows parameters recursiveParameters consistent)⟩

/-- This corollary consumes the actual packed source atoms, with every
original row ID retained and their independent row constraints explicit. -/
theorem compiled_elimination_exact (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (rows : Fin m → Row) (values : Fin (CommonPresenceConstraintGraph.compile atoms).size → Ty) :
    (CommonPresenceConstraintGraph.compile atoms).Models rows values ↔
      CommonPresenceConstraintGraph.RowsHold (CommonPresenceConstraintGraph.splitAtoms atoms).rows rows ∧
      ∃ parameters : Fin m → Ty,
      ∃ recursiveParameters : Fin (CommonPresenceConstraintGraph.compile atoms).size → Ty,
        EdgesHold (CommonBoundCoalescing.rigidComparisons
          (template (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges))
          (solve (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges rows parameters recursiveParameters) ∧
        ∀ index, Equivalent
          (solve (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges rows parameters recursiveParameters index)
          (values index) := by
  have exactBounds := eliminate_variable_edges_exact
    (CommonPresenceConstraintGraph.splitAtoms atoms).pool
    (CommonPresenceConstraintGraph.compile atoms).edges rows values
  constructor
  · rintro ⟨realizes, valid, rowConstraints⟩
    exact ⟨rowConstraints, exactBounds.mp ⟨realizes, valid⟩⟩
  · rintro ⟨rowConstraints, parameters⟩
    obtain ⟨realizes, valid⟩ := exactBounds.mpr parameters
    exact ⟨realizes, valid, rowConstraints⟩

def solveRows (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms) (parameters : Fin m → Row) : Fin m → Row :=
  RowFlowSchemes.instantiate Common.rowAlgebra
    (CommonRowTailInference.rowScheme (CommonPresenceClauseFamily.declareRows atoms good)) parameters

/-- Actual source atoms, simultaneous row substitution, and elimination of
variable edges share their original IDs. The only semantic condition on the
instantiated family is the displayed finite list of rigid comparisons. -/
theorem compiled_joint_elimination_exact (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (CommonPresenceConstraintGraph.compile atoms).size → Ty) :
    (CommonPresenceConstraintGraph.compile atoms).Models rows values ↔
      ∃ rowParameters : Fin m → Row, ∃ parameters : Fin m → Ty,
      ∃ recursiveParameters : Fin (CommonPresenceConstraintGraph.compile atoms).size → Ty,
        solveRows atoms good rowParameters = rows ∧
        EdgesHold (CommonBoundCoalescing.rigidComparisons
          (template (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges))
          (solve (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges
            (solveRows atoms good rowParameters) parameters recursiveParameters) ∧
        ∀ index, Equivalent
          (solve (CommonPresenceConstraintGraph.splitAtoms atoms).pool
            (CommonPresenceConstraintGraph.compile atoms).edges
            (solveRows atoms good rowParameters) parameters recursiveParameters index)
          (values index) := by
  constructor
  · intro models
    have rowSame : solveRows atoms good rows = rows :=
      CommonRowTailInference.rowScheme_retract (CommonPresenceClauseFamily.declareRows atoms good) rows
        ((CommonPresenceClauseFamily.declared_rows_models_exact atoms good rows).mpr models.2.2)
    obtain ⟨_, parameters, recursiveParameters, consistent, same⟩ :=
      (compiled_elimination_exact atoms rows values).mp models
    refine ⟨rows, parameters, recursiveParameters, rowSame, ?_, ?_⟩
    · simpa only [rowSame] using consistent
    · simpa only [rowSame] using same
  · rintro ⟨rowParameters, parameters, recursiveParameters, rowSame, consistent, same⟩
    apply (compiled_elimination_exact atoms rows values).mpr
    have rowModel : CommonPresenceConstraintGraph.RowsHold
        (CommonPresenceConstraintGraph.splitAtoms atoms).rows (solveRows atoms good rowParameters) :=
      (CommonPresenceClauseFamily.declared_rows_models_exact atoms good _).mp
        (CommonRowTailInference.rowScheme_models (CommonPresenceClauseFamily.declareRows atoms good) rowParameters)
    refine ⟨by simpa only [rowSame] using rowModel, parameters, recursiveParameters, ?_, ?_⟩
    · simpa only [rowSame] using consistent
    · simpa only [rowSame] using same

end Yulang.CommonPresenceVariableBounds
