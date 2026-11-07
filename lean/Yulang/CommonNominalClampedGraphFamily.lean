import Yulang.CommonNominalOpenTailSolver
import Yulang.CommonNominalTypeBounds

/-!
# Clamped node families for general mixed constructor graphs

Every original node ID is retained. `none` definitions are flexible type slots;
defined nodes keep their original mixed guarded/same-depth constructor body.
Ordinary subtype edges are classified into flexible flows, lower bounds,
upper bounds and rigid comparisons. The family clamps flexible slots and
closes the whole shared graph using the actual mixed equation solver.

This is the equation-family/retraction stage. Soundness of all parameters for
lower and rigid comparisons still requires a completed nominal-aware finite
inspection/saturation algorithm; it is not assumed from family construction.
-/

namespace Yulang.CommonNominalClampedGraphFamily

open CommonNominalCarrier
open CommonNominalTypeFlow (Edge joinTypes)
open CommonNominalTypeBounds (meetTypes)
open CommonNominalPresenceTailRegular (Payload)

abbrev OpenBody (nodes labels rows : Nat) := CommonNominalOpenTailSolver.Body nodes labels rows (Payload nodes)
abbrev ConcreteBody (nodes labels : Nat) := CommonNominalPresenceTailLayers.Body nodes labels (Payload nodes)

structure Pool (nodes labels rows : Nat) where
  definition : Fin nodes → Option (OpenBody nodes labels rows)

def flexible (pool : Pool nodes labels rows) (index : Fin nodes) : Bool := (pool.definition index).isNone

def flows (pool : Pool nodes labels rows) (edges : List (Edge nodes)) : List (Edge nodes) :=
  edges.filter fun edge => flexible pool edge.1 && flexible pool edge.2

/-- Pairs are (flexible target, fixed-bound node). -/
def lowerPointers (pool : Pool nodes labels rows) (edges : List (Edge nodes)) : List (Edge nodes) :=
  (edges.filter fun edge => !flexible pool edge.1 && flexible pool edge.2).map Prod.swap

/-- Pairs are (flexible source, fixed-bound node). -/
def upperPointers (pool : Pool nodes labels rows) (edges : List (Edge nodes)) : List (Edge nodes) :=
  edges.filter fun edge => flexible pool edge.1 && !flexible pool edge.2

def bounds (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (values : Fin nodes → Ty) :
    CommonNominalTypeBounds.Problem nodes :=
  ⟨flows pool edges, (lowerPointers pool edges).map fun pair => (pair.1, values pair.2),
    (upperPointers pool edges).map fun pair => (pair.1, values pair.2)⟩

def lowerSources (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (index : Fin nodes) : List (Fin nodes) :=
  ((lowerPointers pool edges).filter fun pair => CastGraph.reachable (flows pool edges) pair.1 index).map Prod.snd

def upperTargets (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (index : Fin nodes) : List (Fin nodes) :=
  ((upperPointers pool edges).filter fun pair => CastGraph.reachable (flows pool edges) index pair.1).map Prod.snd

theorem lower_at_exact (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (values : Fin nodes → Ty) (index : Fin nodes) :
    CommonNominalTypeBounds.lowerAt (bounds pool edges values) index = (lowerSources pool edges index).map values := by
  simp only [CommonNominalTypeBounds.lowerAt, bounds, lowerSources, List.filter_map, List.map_map]
  rfl

theorem upper_at_exact (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (values : Fin nodes → Ty) (index : Fin nodes) :
    CommonNominalTypeBounds.upperAt (bounds pool edges values) index = (upperTargets pool edges index).map values := by
  simp only [CommonNominalTypeBounds.upperAt, bounds, upperTargets, List.filter_map, List.map_map]
  rfl

def joinRefs : List (Fin nodes) → ConcreteBody nodes labels
  | [] => .atom .bottom
  | first :: rest => .union (.ref first) (joinRefs rest)

def meetRefs : List (Fin nodes) → ConcreteBody nodes labels
  | [] => .atom .top
  | first :: rest => .inter (.ref first) (meetRefs rest)

def evaluate (values : Fin nodes → Ty) (body : ConcreteBody nodes labels) : Ty :=
  (body.quote (CommonNominalPresenceTailRegular.payload values)).eval values

theorem join_refs_eval (values : Fin nodes → Ty) (references : List (Fin nodes)) :
    evaluate values (joinRefs (labels := labels) references) = joinTypes (references.map values) := by
  induction references <;> simp_all [evaluate, joinRefs, joinTypes, CommonNominalPresenceTailLayers.Body.quote,
    CommonNominalPresenceTailElimination.Body.eval, CommonNominalPresenceTailLayers.quoteLayer, CommonNominalSyntax.Layer.map]

theorem meet_refs_eval (values : Fin nodes → Ty) (references : List (Fin nodes)) :
    evaluate values (meetRefs (labels := labels) references) = meetTypes (references.map values) := by
  induction references <;> simp_all [evaluate, meetRefs, meetTypes, CommonNominalPresenceTailLayers.Body.quote,
    CommonNominalPresenceTailElimination.Body.eval, CommonNominalPresenceTailLayers.quoteLayer, CommonNominalSyntax.Layer.map]

def parameterBody (type : Ty) : ConcreteBody nodes labels := .atom (type.map Sum.inr)

theorem parameter_body_eval (values : Fin nodes → Ty) (type : Ty) :
    Equivalent (evaluate values (parameterBody (labels := labels) type)) type := by
  change Equivalent (CommonNominalPresenceTailLayers.quoteLayer
    (CommonNominalPresenceTailRegular.payload values) (type.map Sum.inr)) type
  rw [CommonNominalPresenceTailLayers.quoteLayer_map]
  exact equivalent_symm (by
    simpa [CommonNominalPresenceTailRegular.payload, Function.comp_def] using
      CommonNominalPresenceTailRegular.map_quote_equivalent type id)

def clampBody (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (parameters : Fin nodes → Ty)
    (index : Fin nodes) : ConcreteBody nodes labels :=
  let upper := meetRefs (upperTargets pool edges index)
  .inter (.union (joinRefs (lowerSources pool edges index))
    (.inter (parameterBody (CommonNominalTypeFlow.instantiate (flows pool edges) parameters index)) upper)) upper

def fullClamp (problem : CommonNominalTypeBounds.Problem nodes) (parameters : Fin nodes → Ty) (index : Fin nodes) : Ty :=
  .inter (CommonNominalTypeBounds.instantiate problem parameters index)
    (meetTypes (CommonNominalTypeBounds.upperAt problem index))

theorem clamp_body_eval (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (parameters values : Fin nodes → Ty) (index : Fin nodes) :
    Equivalent (evaluate values (clampBody pool edges parameters index))
      (fullClamp (bounds pool edges values) parameters index) := by
  have param := parameter_body_eval (labels := labels) values
    (CommonNominalTypeFlow.instantiate (flows pool edges) parameters index)
  change Equivalent
    (.inter (.union (evaluate values (joinRefs (lowerSources pool edges index)))
      (.inter (evaluate values (parameterBody _)) (evaluate values (meetRefs (upperTargets pool edges index)))))
      (evaluate values (meetRefs (upperTargets pool edges index)))) _
  rw [join_refs_eval, meet_refs_eval]
  simp only [fullClamp, CommonNominalTypeBounds.instantiate, lower_at_exact, upper_at_exact]
  exact ⟨common_inter_mono (common_union_mono (subtype_refl _)
      (common_inter_mono param.1 (subtype_refl _))) (subtype_refl _),
    common_inter_mono (common_union_mono (subtype_refl _)
      (common_inter_mono param.2 (subtype_refl _))) (subtype_refl _)⟩

def originalGraph (pool : Pool nodes labels rows) (rowValues : Fin rows → Row) : CommonNominalPresenceTailRegular.Graph nodes labels :=
  fun index => match pool.definition index with
    | none => .ref index
    | some body => body.atRows rowValues

def clampedGraph (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters : Fin nodes → Ty) : CommonNominalPresenceTailRegular.Graph nodes labels :=
  fun index => match pool.definition index with
    | none => clampBody pool edges parameters index
    | some body => body.atRows rowValues

def Realizes (pool : Pool nodes labels rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty) : Prop :=
  CommonNominalPresenceTailRegular.Models (originalGraph pool rowValues) values

def EdgesHold (edges : List (Edge nodes)) (values : Fin nodes → Ty) : Prop := CommonNominalTypeFlow.Models edges values

theorem bounds_models (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (values : Fin nodes → Ty)
    (models : EdgesHold edges values) : CommonNominalTypeBounds.Models (bounds pool edges values) values := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge present
    exact models edge (List.mem_filter.mp present).1
  · intro bound present
    obtain ⟨pointer, pointerPresent, rfl⟩ := List.mem_map.mp present
    obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp pointerPresent
    exact models edge (List.mem_filter.mp edgePresent).1
  · intro bound present
    obtain ⟨pointer, pointerPresent, rfl⟩ := List.mem_map.mp present
    exact models pointer (List.mem_filter.mp pointerPresent).1

private theorem inter_left (first last : Ty) : Subtype (.inter first last) first :=
  (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1
private theorem inter_right (first last : Ty) : Subtype (.inter first last) last :=
  (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.2

theorem full_clamp_retraction (problem : CommonNominalTypeBounds.Problem nodes) (values : Fin nodes → Ty)
    (model : CommonNominalTypeBounds.Models problem values) (index : Fin nodes) :
    Equivalent (fullClamp problem values index) (values index) := by
  have same := CommonNominalTypeBounds.model_retraction problem values model index
  constructor
  · exact subtype_trans (inter_left _ _) same.1
  · apply (common_inter_is_meet _ _ _).mpr
    refine ⟨same.2, ?_⟩
    apply (CommonNominalTypeBounds.below_meet_types _ _).mpr
    intro type present
    obtain ⟨upper, selected, rfl⟩ := List.mem_map.mp present
    obtain ⟨original, reached⟩ := List.mem_filter.mp selected
    exact subtype_trans
      (CommonNominalTypeFlow.path_below problem.edges values model.1 _ _ ((CastGraph.reachable_exact _ _ _).mp reached))
      (model.2.2 upper original)

theorem full_clamp_flow (problem : CommonNominalTypeBounds.Problem nodes) (parameters : Fin nodes → Ty)
    (edge : Edge nodes) (member : edge ∈ problem.edges) :
    Subtype (fullClamp problem parameters edge.1) (fullClamp problem parameters edge.2) :=
  common_inter_mono
    (common_union_mono (CommonNominalTypeBounds.lower_mono problem edge member)
      (common_inter_mono (CommonNominalTypeFlow.all_parameters_models problem.edges parameters edge member)
        (CommonNominalTypeBounds.upper_mono problem edge member)))
    (CommonNominalTypeBounds.upper_mono problem edge member)

theorem original_model_clamped (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (realizes : Realizes pool rowValues values) (valid : EdgesHold edges values) :
    CommonNominalPresenceTailRegular.Models (clampedGraph pool edges rowValues values) values := by
  intro index
  cases found : pool.definition index with
  | some body => simpa only [clampedGraph, originalGraph, found] using realizes index
  | none =>
      simp only [clampedGraph, found]
      change Equivalent (evaluate values (clampBody pool edges values index)) (values index)
      exact equivalent_trans (clamp_body_eval pool edges values values index)
        (full_clamp_retraction (bounds pool edges values) values (bounds_models pool edges values valid) index)

theorem clamped_models_realizes (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models (clampedGraph pool edges rowValues parameters) values) :
    Realizes pool rowValues values := by
  intro index
  cases found : pool.definition index with
  | some body => simpa only [originalGraph, clampedGraph, found] using model index
  | none =>
      simpa only [originalGraph, found, CommonNominalPresenceTailLayers.Body.quote,
        CommonNominalPresenceTailElimination.Body.eval] using equivalent_refl (values index)

theorem flexible_clamped (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models (clampedGraph pool edges rowValues parameters) values)
    (index : Fin nodes) (unbound : pool.definition index = none) :
    Equivalent (fullClamp (bounds pool edges values) parameters index) (values index) := by
  have equation := model index
  change Equivalent (evaluate values ((clampedGraph pool edges rowValues parameters) index)) (values index) at equation
  rw [clampedGraph, unbound] at equation
  exact equivalent_trans (equivalent_symm (clamp_body_eval pool edges parameters values index)) equation

/-- Upper constraints and flexible flows hold for all clamped models,
without assuming lower/rigid consistency. Rigid sources remain to inspect. -/
theorem flexible_source_below (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models (clampedGraph pool edges rowValues parameters) values)
    (edge : Edge nodes) (member : edge ∈ edges) (sourceFree : pool.definition edge.1 = none) :
    Subtype (values edge.1) (values edge.2) := by
  have sourceSame := flexible_clamped pool edges rowValues parameters values model edge.1 sourceFree
  cases target : pool.definition edge.2 with
  | none =>
      have targetSame := flexible_clamped pool edges rowValues parameters values model edge.2 target
      have flow : edge ∈ flows pool edges := List.mem_filter.mpr ⟨member, by simp [flexible, sourceFree, target]⟩
      exact subtype_trans sourceSame.2
        (subtype_trans (full_clamp_flow (bounds pool edges values) parameters edge flow) targetSame.1)
  | some body =>
      have pointer : edge ∈ upperPointers pool edges := List.mem_filter.mpr ⟨member, by simp [flexible, sourceFree, target]⟩
      have direct : (edge.1, values edge.2) ∈ (bounds pool edges values).upper := List.mem_map.mpr ⟨edge, pointer, rfl⟩
      have included : values edge.2 ∈ CommonNominalTypeBounds.upperAt (bounds pool edges values) edge.1 :=
        List.mem_map.mpr ⟨(edge.1, values edge.2), List.mem_filter.mpr
          ⟨direct, (CastGraph.reachable_exact _ _ _).mpr (.seed (by simp))⟩, rfl⟩
      exact subtype_trans sourceSame.2 (subtype_trans (inter_right _ _)
        (CommonNominalTypeBounds.meet_below_member _ _ included))

def instantiate (pool : Pool nodes labels rows) (edges : List (Edge nodes)) (rowValues : Fin rows → Row)
    (parameters nodeParameters : Fin nodes → Ty) : Fin nodes → Ty :=
  CommonNominalPresenceTailRegular.solveBlock (clampedGraph pool edges rowValues parameters) nodeParameters

theorem all_parameters_realizes (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters nodeParameters : Fin nodes → Ty) :
    Realizes pool rowValues (instantiate pool edges rowValues parameters nodeParameters) :=
  clamped_models_realizes pool edges rowValues parameters _ (CommonNominalPresenceTailRegular.solveBlock_models _ nodeParameters)

theorem all_parameters_flexible_edges (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (parameters nodeParameters : Fin nodes → Ty)
    (edge : Edge nodes) (member : edge ∈ edges) (sourceFree : pool.definition edge.1 = none) :
    Subtype (instantiate pool edges rowValues parameters nodeParameters edge.1)
      (instantiate pool edges rowValues parameters nodeParameters edge.2) :=
  flexible_source_below pool edges rowValues parameters _
    (CommonNominalPresenceTailRegular.solveBlock_models _ nodeParameters) edge member sourceFree

/-- Every original full edge/constructor model is recovered at every node.
This direction has no source-grammar, saturation or bound-support premise.
The opposite all-edge soundness direction is not claimed by this theorem. -/
theorem all_models_retraction (pool : Pool nodes labels rows) (edges : List (Edge nodes))
    (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (realizes : Realizes pool rowValues values) (valid : EdgesHold edges values) :
    ∀ index, Equivalent (instantiate pool edges rowValues values values index) (values index) :=
  CommonNominalPresenceTailRegular.solveBlock_retract _ values (original_model_clamped pool edges rowValues values realizes valid)

end Yulang.CommonNominalClampedGraphFamily
