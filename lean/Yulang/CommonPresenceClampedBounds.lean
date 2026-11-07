import Yulang.CommonPresenceVariableBounds

/-!
# An upper-clamped variant of the independent common equation family

The whole variable expansion is intersected with its propagated upper bound,
including contributions from same-depth recursive lower bounds. This removes
the unconstrained recursive fixed points exhibited by
`CommonSameDepthUpperObstruction`. Constructor nodes retain their original
equations and IDs, and every original model is still recovered.

Every row, type and recursive parameter remains unrestricted. Upper constraints
hold for every resulting assignment, without a consistency premise. Lower and
rigid comparisons are not proved here for arbitrary parameters; their symbolic
closure and same-depth interaction remain separate obligations. The original
equation family and its existing statements are unchanged.
-/

namespace Yulang.CommonPresenceClampedBounds

open Common (Ty Row Subtype Equivalent)
open LayerBoundTemplates (Problem)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes EdgesHold restrict)
open CommonPresenceVariableBounds (template inputAt Body bodyEval meetBodies)

universe u
variable {m n : Nat} {Bound : Type u}

def expand (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (target : Fin n) : Ty :=
  .inter (CommonBoundCoalescing.expand evaluate problem parameters target)
    (CommonBoundCoalescing.upper evaluate problem target)

/-- Clamping includes the recursive lower contribution, not only the fresh
type-parameter contribution. No consistency premise is used. -/
theorem expand_below_upper (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (source : Fin n) :
    Subtype (expand evaluate problem parameters source) (CommonBoundCoalescing.upper evaluate problem source) :=
  CommonBoundCoalescing.inter_le_right _ _

theorem expand_below_bound (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (source : Fin n) (bound : Bound)
    (member : bound ∈ LayerBoundTemplates.upperBounds problem source) :
    Subtype (expand evaluate problem parameters source) (evaluate bound) :=
  ((CommonBoundCoalescing.le_upper_iff evaluate problem source _).mp
    (expand_below_upper evaluate problem parameters source)) bound member

theorem lower_along_path (evaluate : Bound → Ty) (problem : Problem n Bound)
    {source target : Fin n} (path : LayerBoundTemplates.Reaches problem source target) :
    Subtype (CommonBoundCoalescing.lower evaluate problem source)
      (CommonBoundCoalescing.lower evaluate problem target) := by
  apply (CommonBoundCoalescing.lower_le_iff evaluate problem source _).mpr
  intro bound member
  obtain ⟨start, seed, before⟩ := (PresenceBoundCoalescing.mem_lowerBounds problem source bound).mp member
  apply CommonBoundCoalescing.member_le_joinTypes
  exact List.mem_map.mpr ⟨bound,
    (PresenceBoundCoalescing.mem_lowerBounds problem target bound).mpr ⟨start, seed, before.append path⟩, rfl⟩

theorem upper_along_path (evaluate : Bound → Ty) (problem : Problem n Bound)
    {source target : Fin n} (path : LayerBoundTemplates.Reaches problem source target) :
    Subtype (CommonBoundCoalescing.upper evaluate problem source)
      (CommonBoundCoalescing.upper evaluate problem target) := by
  apply (CommonBoundCoalescing.le_upper_iff evaluate problem target _).mpr
  intro bound member
  obtain ⟨finish, seed, after⟩ := (PresenceBoundCoalescing.mem_upperBounds problem target bound).mp member
  apply CommonBoundCoalescing.meetTypes_le_member
  exact List.mem_map.mpr ⟨bound,
    (PresenceBoundCoalescing.mem_upperBounds problem source bound).mpr ⟨finish, seed, path.append after⟩, rfl⟩

theorem unclamped_expand_along_path (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) {source target : Fin n}
    (path : LayerBoundTemplates.Reaches problem source target) :
    Subtype (CommonBoundCoalescing.expand evaluate problem parameters source)
      (CommonBoundCoalescing.expand evaluate problem parameters target) := by
  apply (Common.common_union_is_join _ _ _).mpr
  constructor
  · exact Common.subtype_trans (lower_along_path evaluate problem path) (CommonBoundCoalescing.le_union_left _ _)
  · apply (CommonBoundCoalescing.variablePart_le_iff _ _ _ _ _).mpr
    intro start before
    apply Common.subtype_trans (last := CommonBoundCoalescing.expand evaluate problem parameters target)
      (middle := CommonBoundCoalescing.variablePart evaluate problem parameters target)
    · apply CommonBoundCoalescing.member_le_joinTypes
      exact List.mem_map.mpr ⟨start,
        (LayerBoundTemplates.mem_ancestors problem start target).mpr (before.append path), rfl⟩
    · exact CommonBoundCoalescing.le_union_right _ _

theorem expand_along_path (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) {source target : Fin n}
    (path : LayerBoundTemplates.Reaches problem source target) :
    Subtype (expand evaluate problem parameters source) (expand evaluate problem parameters target) :=
  Common.common_inter_mono (unclamped_expand_along_path evaluate problem parameters path)
    (upper_along_path evaluate problem path)

/-- Every genuine original solution is fixed by the clamped expansion. -/
theorem expand_retraction {evaluate : Bound → Ty} {problem : Problem n Bound}
    {values : Fin n → Ty} (model : CommonBoundCoalescing.Models evaluate problem values) (index : Fin n) :
    Equivalent (expand evaluate problem values index) (values index) := by
  have same := CommonBoundCoalescing.expand_retraction model index
  exact ⟨Common.subtype_trans (CommonBoundCoalescing.inter_le_left _ _) same.1,
    (Common.common_inter_is_meet _ _ _).mpr ⟨same.2, CommonBoundCoalescing.upper_above model index⟩⟩

def upperBody (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) (index : Fin m) : Body pool :=
  meetBodies pool ((LayerBoundTemplates.upperBounds (template pool edges) index).map .ref)

theorem upperBody_eval (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (values : Fin pool.size → Ty) (index : Fin m) :
    bodyEval pool values (upperBody pool edges index) =
      CommonBoundCoalescing.upper values (template pool edges) index := by
  simp only [upperBody, CommonPresenceVariableBounds.meetBodies_eval,
    List.map_map, Function.comp_def, CommonBoundCoalescing.upper]
  rfl

def expandBody (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (parameters : Fin m → Ty) (index : Fin m) : Body pool :=
  .inter (CommonPresenceVariableBounds.expandBody pool edges parameters index) (upperBody pool edges index)

theorem expandBody_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (parameters : Fin m → Ty) (values : Fin pool.size → Ty) (index : Fin m) :
    Equivalent (bodyEval pool values (expandBody pool edges parameters index))
      (expand values (template pool edges) parameters index) := by
  change Equivalent (.inter _ (bodyEval pool values (upperBody pool edges index))) _
  rw [upperBody_eval]
  have before := CommonPresenceVariableBounds.expandBody_exact pool edges parameters values index
  exact ⟨Common.common_inter_mono before.1 (Common.subtype_refl _),
    Common.common_inter_mono before.2 (Common.subtype_refl _)⟩

def graph (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) : CommonPresenceTailRegular.Graph pool.size 0 :=
  fun slot => match inputAt pool slot with
    | some index => expandBody pool edges parameters index
    | none => (CommonPresenceConstraintGraph.graph pool slot).atRows rows

/-- The independent clamped equations preserve every original constructor
equation. Only original variable identities receive a new right-hand side. -/
theorem models_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty) :
    CommonPresenceTailRegular.Models (graph pool edges rows parameters) values ↔
      Realizes pool rows values ∧
        ∀ index, Equivalent (expand values (template pool edges) parameters index) (restrict pool values index) := by
  constructor
  · intro model
    constructor
    · intro slot
      cases found : inputAt pool slot with
      | none =>
          have valid := model slot
          simpa only [graph, found, CommonRowTailInference.Body.eval_atRows] using valid
      | some index =>
          have same := (CommonPresenceVariableBounds.variable_some_iff pool slot index).mp found
          rw [same, CommonPresenceVariableBounds.graph_input]
          exact Common.equivalent_refl _
    · intro index
      have valid := model (pool.input index)
      change Equivalent (bodyEval pool values (graph pool edges rows parameters (pool.input index))) _ at valid
      rw [graph, CommonPresenceVariableBounds.variable_input] at valid
      exact Common.equivalent_trans (Common.equivalent_symm (expandBody_exact pool edges parameters values index)) valid
  · rintro ⟨realizes, expanded⟩ slot
    cases found : inputAt pool slot with
    | none =>
        simpa only [graph, found, CommonRowTailInference.Body.eval_atRows] using realizes slot
    | some index =>
        have same := (CommonPresenceVariableBounds.variable_some_iff pool slot index).mp found
        change Equivalent (bodyEval pool values (graph pool edges rows parameters slot)) _
        rw [graph, found]
        exact Common.equivalent_trans (expandBody_exact pool edges parameters values index)
          (by simpa only [restrict, same] using expanded index)

theorem models_below_bound (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (graph pool edges rows parameters) values)
    (source : Fin m) (bound : Fin pool.size)
    (member : bound ∈ LayerBoundTemplates.upperBounds (template pool edges) source) :
    Subtype (values (pool.input source)) (values bound) := by
  have expanded := ((models_exact pool edges rows parameters values).mp model).2 source
  exact Common.subtype_trans expanded.2 (expand_below_bound values (template pool edges) parameters source bound member)

theorem models_along_path (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin pool.size → Ty)
    (model : CommonPresenceTailRegular.Models (graph pool edges rows parameters) values)
    {source target : Fin m} (path : LayerBoundTemplates.Reaches (template pool edges) source target) :
    Subtype (values (pool.input source)) (values (pool.input target)) := by
  have expanded := ((models_exact pool edges rows parameters values).mp model).2
  exact Common.subtype_trans (expanded source).2
    (Common.subtype_trans (expand_along_path values (template pool edges) parameters path) (expanded target).1)

theorem recovers_original_model (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) :
    CommonPresenceTailRegular.Models (graph pool edges rows (restrict pool values)) values :=
  (models_exact pool edges rows (restrict pool values) values).mpr
    ⟨realizes, expand_retraction (CommonPresenceVariableBounds.models_of_edges pool edges values valid)⟩

def solve (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) : Fin pool.size → Ty :=
  CommonPresenceTailRegular.solveBlock (graph pool edges rows parameters) recursiveParameters

theorem solve_realizes (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) (rows : Fin m → Row)
    (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) :
    Realizes pool rows (solve pool edges rows parameters recursiveParameters) :=
  ((models_exact pool edges rows parameters _).mp
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters)).1

/-- All type and recursive parameters are arbitrary. Every propagated upper
bound holds, even along same-depth recursive tails. -/
theorem all_parameters_below_bound (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty)
    (source : Fin m) (bound : Fin pool.size)
    (member : bound ∈ LayerBoundTemplates.upperBounds (template pool edges) source) :
    Subtype (solve pool edges rows parameters recursiveParameters (pool.input source))
      (solve pool edges rows parameters recursiveParameters bound) :=
  models_below_bound pool edges rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) source bound member

theorem all_parameters_along_path (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty)
    {source target : Fin m} (path : LayerBoundTemplates.Reaches (template pool edges) source target) :
    Subtype (solve pool edges rows parameters recursiveParameters (pool.input source))
      (solve pool edges rows parameters recursiveParameters (pool.input target)) :=
  models_along_path pool edges rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) path

theorem solve_retract (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (valid : EdgesHold edges values) (slot : Fin pool.size) :
    Equivalent (solve pool edges rows (restrict pool values) values slot) (values slot) :=
  CommonPresenceTailRegular.solveBlock_retract _ values (recovers_original_model pool edges rows values realizes valid) slot

end Yulang.CommonPresenceClampedBounds
