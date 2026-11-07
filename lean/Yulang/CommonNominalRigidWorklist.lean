import Yulang.CommonNominalPlainInspection
import Yulang.FiniteBranchingWorklist
import Yulang.CommonNominalTemplateRowPatterns

/-!
# Actual finite shared-node saturation for nominal/structural rigid heads

Every original node ID is retained. Flexible nodes have no definition;
defined nodes use the finite rigid-head syntax, with arbitrary recursive
shared children and symbolic rows. All reachable defined-node pairs are
inspected, so flexible paths propagate lower/upper comparisons as well.

The worklist has a proved finite inventory, no caller fuel, and exact
independent-model preservation. All-parameter clamped-family soundness and
extension to record/default/lattice source nodes are separate obligations.
-/

namespace Yulang.CommonNominalRigidWorklist

open CommonNominalCarrier (Ty Row Equivalent Subtype)
open CommonNominalRigidInspection (Node)
open CommonNominalPlainInspection (Check)
open CommonNominalFieldTemplates (TemplateRow)
open CommonNominalTypeFlow (Edge)

structure Pool (nodes rows : Nat) where
  definition : Fin nodes → Option (Node (TemplateRow rows) (Fin nodes))

def Realizes (pool : Pool nodes rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty) : Prop :=
  ∀ index node, pool.definition index = some node →
    Equivalent (node.eval (TemplateRow.eval rowValues) values) (values index)

abbrev RowEdge (rows : Nat) := TemplateRow rows × TemplateRow rows
abbrev Branch (nodes rows : Nat) := FiniteBranchingWorklist.Branch (Edge nodes) (RowEdge rows)
abbrev State (nodes rows : Nat) := FiniteBranchingWorklist.State (Edge nodes) (RowEdge rows)

def split : List (Check (TemplateRow rows) (Fin nodes)) → Branch nodes rows
  | [] => ⟨[], []⟩
  | .type first last :: rest =>
      let after := split rest
      ⟨(first, last) :: after.children, after.aux⟩
  | .row first last :: rest =>
      let after := split rest
      ⟨after.children, (first, last) :: after.aux⟩

def rowHolds (rowValues : Fin rows → Row) (edge : RowEdge rows) : Prop :=
  Common.rowLe (edge.1.eval rowValues) (edge.2.eval rowValues)

def edgeHolds (values : Fin nodes → Ty) (edge : Edge nodes) : Prop :=
  Subtype (values edge.1) (values edge.2)

theorem split_models (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (checks : List (Check (TemplateRow rows) (Fin nodes))) :
    (split checks).Models (edgeHolds values) (rowHolds rowValues) ↔
      ∀ check ∈ checks, check.Holds (TemplateRow.eval rowValues) values := by
  induction checks with
  | nil => simp [split, FiniteBranchingWorklist.Branch.Models]
  | cons check rest ih =>
      cases check <;>
        simp only [split, FiniteBranchingWorklist.Branch.Models, List.mem_cons, forall_eq_or_imp,
          CommonNominalPlainInspection.Check.Holds] at *
      all_goals
        simp only [rowHolds, edgeHolds, and_assoc, and_left_comm, and_congr_right_iff]
        intro _
        simpa only [rowHolds, edgeHolds] using ih

def inventory (nodes : Nat) : List (Edge nodes) :=
  (List.finRange nodes).flatMap fun source => (List.finRange nodes).map fun target => (source, target)

@[simp] theorem mem_inventory (edge : Edge nodes) : edge ∈ inventory nodes := by
  rcases edge with ⟨source, target⟩
  simp [inventory]

def rigid (pool : Pool nodes rows) (edges : List (Edge nodes)) : List (Edge nodes) :=
  (inventory nodes).filter fun edge =>
    (pool.definition edge.1).isSome && (pool.definition edge.2).isSome &&
      CastGraph.reachable edges edge.1 edge.2

def inspect (pool : Pool nodes rows) (edge : Edge nodes) : List (Branch nodes rows) :=
  match pool.definition edge.1, pool.definition edge.2 with
  | some source, some target =>
      match CommonNominalPlainInspection.inspect source target with
      | none => []
      | some checks => [split checks]
  | _, _ => []

def run (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows)) : List (State nodes rows) :=
  FiniteBranchingWorklist.run (inventory nodes) (rigid pool) (inspect pool) edges rowEdges

theorem rigid_sound (pool : Pool nodes rows) (edges : List (Edge nodes)) (values : Fin nodes → Ty)
    (model : ∀ edge ∈ edges, edgeHolds values edge) :
    ∀ edge ∈ rigid pool edges, edgeHolds values edge := by
  intro edge member
  have selected := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true] at selected
  have reached : CastGraph.reachable edges edge.1 edge.2 = true := selected.2
  exact CommonNominalTypeFlow.path_below edges values model _ _ ((CastGraph.reachable_exact _ _ _).mp reached)

theorem inspect_exact (pool : Pool nodes rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (realizes : Realizes pool rowValues values) (edges : List (Edge nodes)) (edge : Edge nodes)
    (active : edge ∈ rigid pool edges) :
    edgeHolds values edge ↔
      ∃ branch ∈ inspect pool edge, branch.Models (edgeHolds values) (rowHolds rowValues) := by
  cases sourceFound : pool.definition edge.1 with
  | none => simp [rigid, sourceFound] at active
  | some source =>
      cases targetFound : pool.definition edge.2 with
      | none => simp [rigid, targetFound] at active
      | some target =>
          have first := realizes edge.1 source sourceFound
          have last := realizes edge.2 target targetFound
          have comparison : edgeHolds values edge ↔ Subtype
              (source.eval (TemplateRow.eval rowValues) values) (target.eval (TemplateRow.eval rowValues) values) := by
            constructor
            · intro below
              exact CommonNominalCarrier.subtype_trans first.1 (CommonNominalCarrier.subtype_trans below last.2)
            · intro below
              exact CommonNominalCarrier.subtype_trans first.2 (CommonNominalCarrier.subtype_trans below last.1)
          rw [comparison, ← CommonNominalPlainInspection.inspect_exact (TemplateRow.eval rowValues) values source target]
          cases checked : CommonNominalPlainInspection.inspect source target <;>
            simp [inspect, sourceFound, targetFound, checked, CommonNominalPlainInspection.Satisfied, split_models]

/-- Every original independent full model extends to a returned saturation
state, and every returned state's full model restricts to the original one.
The fixed original constructor equations remain outside the algorithm. -/
theorem run_models_exact (pool : Pool nodes rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (realizes : Realizes pool rowValues values) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows)) :
    ((∀ edge ∈ edges, edgeHolds values edge) ∧ ∀ edge ∈ rowEdges, rowHolds rowValues edge) ↔
      ∃ state ∈ run pool edges rowEdges,
        state.Models (edgeHolds values) (rowHolds rowValues) := by
  exact FiniteBranchingWorklist.run_models_exact_selected (inventory nodes) (rigid pool) (inspect pool)
    (edgeHolds values) (rowHolds rowValues) (fun edges model => rigid_sound pool edges values model)
    (fun edges edge _ active => inspect_exact pool rowValues values realizes edges edge active) edges rowEdges

theorem run_closed (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows))
    (state : State nodes rows) (returned : state ∈ run pool edges rowEdges) :
    FiniteBranchingWorklist.Closed (rigid pool) (inspect pool) state := by
  exact FiniteBranchingWorklist.run_closed (inventory nodes) (rigid pool) (inspect pool) edges rowEdges
    (fun edge _ => mem_inventory edge) (fun _ _ _ _ child _ => mem_inventory child)
    (fun _ _ edge _ => mem_inventory edge) state returned

theorem run_retains (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows))
    (state : State nodes rows) (returned : state ∈ run pool edges rowEdges) :
    edges ⊆ state.edges ∧ rowEdges ⊆ state.aux :=
  FiniteBranchingWorklist.run_retains (inventory nodes) (rigid pool) (inspect pool) edges rowEdges state returned

theorem inventory_length (nodes : Nat) : (inventory nodes).length = nodes * nodes := by
  simp [inventory, List.map_const', List.sum_replicate_nat]

theorem run_bound (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows))
    (state : State nodes rows) (returned : state ∈ run pool edges rowEdges) :
    state.trace.length ≤ nodes * nodes := by
  simpa only [inventory_length] using
    (FiniteBranchingWorklist.run_bound (inventory nodes) (rigid pool) (inspect pool) edges rowEdges
      (fun edge _ => mem_inventory edge) (fun _ _ _ _ child _ => mem_inventory child) state returned).2.2.2.2

end Yulang.CommonNominalRigidWorklist
