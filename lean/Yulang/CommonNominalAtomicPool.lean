import Yulang.CommonNominalAtomicGraph

/-!
# Actual packed field/source atoms as one shared mixed bound pool

The computed pool contains all original ambient type slots and every node of
every original ordinary/full-template term. Original rows keep their packed
IDs. Independent pool models read back every original packed computation,
with literal rows and the same whole-type ambient values.

This closes graph generation, not arbitrary-bound solving or executable
runtime casts. No original atom/formula predicate is stored in a pool model.
-/

namespace Yulang.CommonNominalAtomicPool

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)
open CommonNominalFieldNormalForm (Atom All)
open CommonNominalAtomicGraph (Graph)

def pool (graph : Graph inputs) := CommonNominalTemplateLowering.pool graph.template

def edges (graph : Graph inputs) : List (CommonNominalTypeFlow.Edge (graph.template.nodes + inputs)) :=
  graph.edges.map (Prod.map CommonNominalTemplateLowering.index CommonNominalTemplateLowering.index)

def Models (graph : Graph inputs) (rows : Fin inputs → Row) (values : Fin (graph.template.nodes + inputs) → Ty) : Prop :=
  CommonNominalClampedGraphFamily.Realizes (pool graph) rows values ∧
    CommonNominalTypeFlow.Models (edges graph) values ∧ CommonNominalTemplateRowPatterns.Models graph.rows rows

def readback (graph : Graph inputs) (rows : Fin inputs → Row) (values : Fin (graph.template.nodes + inputs) → Ty) :
    Fin inputs → Comp model := fun index => (values (Fin.natAdd graph.template.nodes index), rows index)

theorem models_graph_exact (graph : Graph inputs) (assignment : Fin inputs → Comp model)
    (internal : Fin graph.template.nodes → Ty) :
    Models graph (fun index => (assignment index).2)
        (CommonNominalTemplateLowering.values internal (fun index => (assignment index).1)) ↔
      graph.Models assignment internal := by
  let arguments : Fin inputs → Ty := fun index => (assignment index).1
  let rows : Fin inputs → Row := fun index => (assignment index).2
  have constructorExact := CommonNominalTemplateLowering.pool_models_exact graph.template rows internal arguments
  have edgesExact : CommonNominalTypeFlow.Models (edges graph) (CommonNominalTemplateLowering.values internal arguments) ↔
      CommonNominalAtomicGraph.EdgeModels graph.edges arguments internal := by
    simp only [CommonNominalTypeFlow.Models, edges, List.forall_mem_map, Prod.map,
      CommonNominalTemplateLowering.value_index, CommonNominalAtomicGraph.EdgeModels]
  constructor
  · rintro ⟨constructors, comparisons, rowModel⟩
    exact ⟨constructorExact.mp constructors, edgesExact.mp comparisons, rowModel⟩
  · rintro ⟨constructors, comparisons, rowModel⟩
    exact ⟨constructorExact.mpr constructors, edgesExact.mpr comparisons, rowModel⟩

theorem readback_original (graph : Graph inputs) (assignment : Fin inputs → Comp model)
    (internal : Fin graph.template.nodes → Ty) :
    readback graph (fun index => (assignment index).2)
      (CommonNominalTemplateLowering.values internal (fun index => (assignment index).1)) = assignment := by
  funext index
  apply Prod.ext
  · exact CommonNominalTemplateLowering.value_parameter internal (fun index => (assignment index).1) index
  · rfl

theorem arbitrary_pool_model (graph : Graph inputs) (rows : Fin inputs → Row)
    (values : Fin (graph.template.nodes + inputs) → Ty) (model : Models graph rows values) :
    ∃ internal, graph.Models (readback graph rows values) internal := by
  let internal : Fin graph.template.nodes → Ty := values ∘ Fin.castAdd inputs
  let arguments : Fin inputs → Ty := values ∘ Fin.natAdd graph.template.nodes
  have same : CommonNominalTemplateLowering.values internal arguments = values := CommonNominalTemplateLowering.merged_eta values
  apply Exists.intro internal
  apply (models_graph_exact graph (readback graph rows values) internal).mp
  refine ⟨?_, ?_, model.2.2⟩
  · exact Eq.mpr (congrArg (CommonNominalClampedGraphFamily.Realizes (pool graph) rows) same) model.1
  · exact Eq.mpr (congrArg (CommonNominalTypeFlow.Models (edges graph)) same) model.2.1

/-- Every original packed model extends with the same original whole-type
and row components. No old-carrier or source-shape restriction is used. -/
theorem compile_atoms_exact (atoms : List (Atom (Fin inputs))) (assignment : Fin inputs → Comp model) :
    All assignment atoms ↔ ∃ internal,
      Models (CommonNominalAtomicGraph.compile atoms) (fun index => (assignment index).2)
        (CommonNominalTemplateLowering.values internal (fun index => (assignment index).1)) := by
  exact (CommonNominalAtomicGraph.compile_atoms_exact atoms assignment).trans
    (exists_congr fun internal => (models_graph_exact _ assignment internal).symm)

theorem all_pool_models_recover (atoms : List (Atom (Fin inputs))) (rows : Fin inputs → Row)
    (values : Fin ((CommonNominalAtomicGraph.compile atoms).template.nodes + inputs) → Ty)
    (model : Models (CommonNominalAtomicGraph.compile atoms) rows values) :
    All (readback (CommonNominalAtomicGraph.compile atoms) rows values) atoms := by
  obtain ⟨internal, actual⟩ := arbitrary_pool_model (CommonNominalAtomicGraph.compile atoms) rows values model
  exact (CommonNominalAtomicGraph.compile_atoms_exact atoms _).mpr ⟨internal, actual⟩

end Yulang.CommonNominalAtomicPool
