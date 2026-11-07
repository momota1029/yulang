import Yulang.CommonNominalPresenceTailRegular
import Yulang.CommonNominalTemplateRowSolver
import Yulang.CommonNominalTypeFlow

/-!
# Solved rows, shared free type flows and full mixed same-depth equations

Symbolic rows remain finite syntax. The same node IDs occur in positive
same-depth refs and guarded payloads, including nominal invariant arguments
and negative arrow inputs. Every returned scheme is finite syntax and all
row, free-type and recursive-node parameters are unrestricted.

The problem does not yet include arbitrary subtype edges between constructed
nodes, or equations equating a free type with such a node. Full source-bound
saturation remains a separate obligation.
-/

namespace Yulang.CommonNominalOpenTailSolver

open CommonNominalCarrier
open CommonNominalFieldTemplates (TemplateRow rowsLayer)
open CommonNominalTypeFlow (Edge)
open PresenceTailElimination (Mask)

inductive Body (nodes labels rows : Nat) (Index : Type) where
  | atom : CommonNominalSyntax.Layer (TemplateRow rows) Index → Body nodes labels rows Index
  | ref : Fin nodes → Body nodes labels rows Index
  | union : Body nodes labels rows Index → Body nodes labels rows Index → Body nodes labels rows Index
  | inter : Body nodes labels rows Index → Body nodes labels rows Index → Body nodes labels rows Index
  | mask : Mask labels → Body nodes labels rows Index → Body nodes labels rows Index
  | record : Nat → Index → Body nodes labels rows Index → Body nodes labels rows Index
  | recordDefault : Nat → Body nodes labels rows Index → Index → Body nodes labels rows Index

def Body.atRows (rowValues : Fin rows → Row) : Body nodes labels rows Index → CommonNominalPresenceTailLayers.Body nodes labels Index
  | .atom layer => .atom (rowsLayer rowValues layer)
  | .ref index => .ref index
  | .union first last => .union (first.atRows rowValues) (last.atRows rowValues)
  | .inter first last => .inter (first.atRows rowValues) (last.atRows rowValues)
  | .mask hidden source => .mask hidden (source.atRows rowValues)
  | .record label payload tail => .record label payload (tail.atRows rowValues)
  | .recordDefault label source fallback => .recordDefault label (source.atRows rowValues) fallback

abbrev Bodies (nodes labels types rows : Nat) := Fin nodes → Body nodes labels rows (Fin nodes ⊕ Fin types)

def graph (body : Bodies nodes labels types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) : CommonNominalPresenceTailRegular.Graph nodes labels :=
  fun index => ((body index).atRows rowValues).map
    (Sum.map id (fun parameter => CommonNominalSyntax.State.node (typeValues parameter)))

theorem graph_models_types_congr (body : Bodies nodes labels types rows) (rowValues : Fin rows → Row)
    (first last : Fin types → Ty) (same : ∀ index, Equivalent (first index) (last index)) (values : Fin nodes → Ty) :
    CommonNominalPresenceTailRegular.Models (graph body rowValues first) values ↔
      CommonNominalPresenceTailRegular.Models (graph body rowValues last) values := by
  have equations (index : Fin nodes) : Equivalent
      (((graph body rowValues first index).quote (CommonNominalPresenceTailRegular.payload values)).eval values)
      (((graph body rowValues last index).quote (CommonNominalPresenceTailRegular.payload values)).eval values) := by
    simp only [graph, CommonNominalPresenceTailLayers.Body.quote_map]
    apply CommonNominalPresenceTailRegular.Body.quote_eval_congr
    · intro reference
      cases reference with
      | inl index => exact equivalent_refl _
      | inr parameter => exact same parameter
    · exact fun _ => equivalent_refl _
  constructor
  · intro model index
    exact equivalent_trans (equivalent_symm (equations index)) (model index)
  · intro model index
    exact equivalent_trans (equations index) (model index)

structure Problem (nodes labels types rows : Nat) where
  body : Bodies nodes labels types rows
  rowConstraints : CommonNominalTemplateRowPatterns.Problem rows
  typeEdges : List (Edge types)

def Problem.Models (problem : Problem nodes labels types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) : Prop :=
  CommonNominalTemplateRowPatterns.Models problem.rowConstraints rowValues ∧
    CommonNominalTypeFlow.Models problem.typeEdges typeValues ∧
    CommonNominalPresenceTailRegular.Models (graph problem.body rowValues typeValues) nodeValues

structure Scheme (nodes labels types rows : Nat) where
  body : Bodies nodes labels types rows
  rowSolution : CommonNominalTemplateRowSolver.Scheme rows
  typeEdges : List (Edge types)

abbrev Scheme.Parameters (_scheme : Scheme nodes labels types rows) :=
  CommonNominalRowCells.Parameters rows × ((Fin types → Ty) × (Fin nodes → Ty))

def Scheme.instantiateRows (scheme : Scheme nodes labels types rows) (parameters : scheme.Parameters) : Fin rows → Row :=
  scheme.rowSolution.instantiate parameters.1

def Scheme.instantiateTypes (scheme : Scheme nodes labels types rows) (parameters : scheme.Parameters) : Fin types → Ty :=
  CommonNominalTypeFlow.instantiate scheme.typeEdges parameters.2.1

def Scheme.instantiateValues (scheme : Scheme nodes labels types rows) (parameters : scheme.Parameters) : Fin nodes → Ty :=
  CommonNominalPresenceTailRegular.solveBlock
    (graph scheme.body (scheme.instantiateRows parameters) (scheme.instantiateTypes parameters)) parameters.2.2

def solve (problem : Problem nodes labels types rows) : List (Scheme nodes labels types rows) :=
  (CommonNominalTemplateRowSolver.solve problem.rowConstraints).map fun rowScheme =>
    ⟨problem.body, rowScheme, problem.typeEdges⟩

theorem all_parameters_models (problem : Problem nodes labels types rows) (scheme : Scheme nodes labels types rows)
    (member : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    problem.Models (scheme.instantiateRows parameters) (scheme.instantiateTypes parameters) (scheme.instantiateValues parameters) := by
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp member
  exact ⟨CommonNominalTemplateRowSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1,
    CommonNominalTypeFlow.all_parameters_models problem.typeEdges parameters.2.1,
    CommonNominalPresenceTailRegular.solveBlock_models _ parameters.2.2⟩

/-- All original rows and all original free/constructed node values, even
with same-depth cycles and negative or invariant guarded dependencies. -/
theorem solve_all_instances_exact (problem : Problem nodes labels types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) :
    problem.Models rowValues typeValues nodeValues ↔
      ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows parameters = rowValues ∧
        (∀ index, Equivalent (scheme.instantiateTypes parameters index) (typeValues index)) ∧
        ∀ index, Equivalent (scheme.instantiateValues parameters index) (nodeValues index) := by
  constructor
  · rintro ⟨rowModel, typeModel, nodeModel⟩
    obtain ⟨rowScheme, rowReturned, rowParameters, rowsSame⟩ :=
      (CommonNominalTemplateRowSolver.solve_all_instances_exact problem.rowConstraints rowValues).mp rowModel
    let scheme : Scheme nodes labels types rows := ⟨problem.body, rowScheme, problem.typeEdges⟩
    have typesSame := CommonNominalTypeFlow.model_retraction problem.typeEdges typeValues typeModel
    have changedModel := (graph_models_types_congr problem.body rowValues _ typeValues typesSame nodeValues).mpr nodeModel
    refine ⟨scheme, List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩,
      ⟨rowParameters, typeValues, nodeValues⟩, rowsSame, typesSame, ?_⟩
    intro index
    change Equivalent (CommonNominalPresenceTailRegular.solveBlock
      (graph problem.body (rowScheme.instantiate rowParameters) (CommonNominalTypeFlow.instantiate problem.typeEdges typeValues))
      nodeValues index) (nodeValues index)
    rw [rowsSame]
    exact CommonNominalPresenceTailRegular.solveBlock_retract _ nodeValues changedModel index
  · rintro ⟨scheme, member, parameters, rowsSame, typesSame, nodesSame⟩
    obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp member
    have rowModel := CommonNominalTemplateRowSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1
    have actualRows : rowScheme.instantiate parameters.1 = rowValues := rowsSame
    refine ⟨by simpa only [actualRows] using rowModel,
      CommonNominalTypeFlow.models_of_recovered problem.typeEdges parameters.2.1 typeValues typesSame, ?_⟩
    apply (graph_models_types_congr problem.body rowValues _ typeValues typesSame nodeValues).mp
    have original := CommonNominalPresenceTailRegular.solveBlock_models
      (graph problem.body (rowScheme.instantiate parameters.1) (CommonNominalTypeFlow.instantiate problem.typeEdges parameters.2.1))
      parameters.2.2
    have moved := (CommonNominalPresenceTailRegular.models_congr _ _ nodeValues nodesSame).mp original
    simpa only [actualRows, Scheme.instantiateTypes] using moved

end Yulang.CommonNominalOpenTailSolver
