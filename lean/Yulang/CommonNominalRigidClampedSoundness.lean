import Yulang.CommonNominalRigidWorklist
import Yulang.CommonNominalClampedFiniteEdges

/-!
# Closed nominal rigid worklists imply all clamped edges

The local constructor inspections use only preceding-depth children. Every
ordinary child and row check comes from the actual closed worklist. Lower
edges reduce to the same source against propagated rigid targets; simultaneous
depth induction discharges them without a full-subtype circular hypothesis.

This covers arbitrary cyclic rigid-head pools. The remaining root grammar
extension (records/defaults/lattices) is not assumed or claimed here.
-/

namespace Yulang.CommonNominalRigidClampedSoundness

open CommonNominalCarrier
open CommonNominalRigidInspection (Node)
open CommonNominalRigidWorklist (Pool State Realizes rowHolds edgeHolds)
open CommonNominalFieldTemplates (TemplateRow)
open CommonNominalTypeFlow (Edge)
open CommonNominalFiniteRigidInspection (BelowAt GuardedAt)
open CommonNominalPlainInspection (Check)

def Node.layer : Node (TemplateRow rows) (Fin nodes) →
    CommonNominalSyntax.Layer (TemplateRow rows) (CommonNominalPresenceTailRegular.Payload nodes)
  | .bottom => .bottom
  | .top => .top
  | .float => .float
  | .base scalar => .base scalar
  | .pair first last => .pair (.inl first) (.inl last)
  | .variant label payload => .variant label (.inl payload)
  | .arrow input incoming output outgoing => .arrow (.inl input) incoming (.inl output) outgoing
  | .nominal name args => .nominal name (args.map (Sum.map Sum.inl id))

def clampedPool (pool : Pool nodes rows) : CommonNominalClampedGraphFamily.Pool nodes 0 rows :=
  ⟨fun index => (pool.definition index).map fun node => .atom (Node.layer node)⟩

@[simp] theorem clamped_free_iff (pool : Pool nodes rows) (index : Fin nodes) :
    (clampedPool pool).definition index = none ↔ pool.definition index = none := by
  simp [clampedPool]

theorem body_eval (rowValues : Fin rows → Row) (values : Fin nodes → Ty)
    (node : Node (TemplateRow rows) (Fin nodes)) :
    CommonNominalClampedGraphFamily.evaluate (labels := 0) values
      ((CommonNominalOpenTailSolver.Body.atom (Node.layer node)).atRows rowValues) =
        node.eval (TemplateRow.eval rowValues) values := by
  cases node <;>
    simp only [CommonNominalClampedGraphFamily.evaluate, CommonNominalOpenTailSolver.Body.atRows,
      CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
      CommonNominalPresenceTailLayers.quoteLayer, Node.layer, CommonNominalFieldTemplates.rowsLayer,
      CommonNominalSyntax.Layer.map, CommonNominalPresenceTailRegular.payload, Sum.elim_inl, Node.eval,
      CommonNominalCarrier.pair, CommonNominalCarrier.variant, CommonNominalCarrier.arrow,
      CommonNominalCarrier.nominal, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  cases argument <;> rfl

theorem realizes_exact (pool : Pool nodes rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty) :
    CommonNominalClampedGraphFamily.Realizes (clampedPool pool) rowValues values ↔
      Realizes pool rowValues values := by
  constructor
  · intro model index node found
    have atIndex := model index
    change Equivalent (CommonNominalClampedGraphFamily.evaluate values
      (CommonNominalClampedGraphFamily.originalGraph (clampedPool pool) rowValues index)) _ at atIndex
    simp only [CommonNominalClampedGraphFamily.originalGraph, clampedPool, found, Option.map_some] at atIndex
    simpa only [body_eval] using atIndex
  · intro model index
    cases found : pool.definition index with
    | none =>
        change Equivalent (CommonNominalClampedGraphFamily.evaluate values
          (CommonNominalClampedGraphFamily.originalGraph (clampedPool pool) rowValues index)) _
        simpa [CommonNominalClampedGraphFamily.originalGraph, clampedPool, found,
          CommonNominalClampedGraphFamily.evaluate, CommonNominalPresenceTailLayers.Body.quote,
          CommonNominalPresenceTailElimination.Body.eval] using equivalent_refl (values index)
    | some node =>
        change Equivalent (CommonNominalClampedGraphFamily.evaluate values
          (CommonNominalClampedGraphFamily.originalGraph (clampedPool pool) rowValues index)) _
        simp only [CommonNominalClampedGraphFamily.originalGraph, clampedPool, found, Option.map_some, body_eval]
        exact model index node found

theorem split_type_iff (checks : List (Check (TemplateRow rows) (Fin nodes))) (first last : Fin nodes) :
    (first, last) ∈ (CommonNominalRigidWorklist.split checks).children ↔ .type first last ∈ checks := by
  induction checks with
  | nil => simp [CommonNominalRigidWorklist.split]
  | cons check rest ih => cases check <;> simp [CommonNominalRigidWorklist.split, ih]

theorem split_row_iff (checks : List (Check (TemplateRow rows) (Fin nodes))) (first last : TemplateRow rows) :
    (first, last) ∈ (CommonNominalRigidWorklist.split checks).aux ↔ .row first last ∈ checks := by
  induction checks with
  | nil => simp [CommonNominalRigidWorklist.split]
  | cons check rest ih => cases check <;> simp [CommonNominalRigidWorklist.split, ih]

theorem rigid_at_of_guarded (depth : Nat) (pool : Pool nodes rows) (state : State nodes rows)
    (closed : FiniteBranchingWorklist.Closed (CommonNominalRigidWorklist.rigid pool)
      (CommonNominalRigidWorklist.inspect pool) state)
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models
      (CommonNominalClampedGraphFamily.clampedGraph (clampedPool pool) state.edges rowValues parameters) values)
    (rowModel : ∀ edge ∈ state.aux, rowHolds rowValues edge)
    (guarded : ∀ edge ∈ state.edges, GuardedAt depth (values edge.1) (values edge.2)) :
    ∀ edge ∈ CommonNominalRigidWorklist.rigid pool state.edges,
      BelowAt depth (values edge.1) (values edge.2) := by
  have original : Realizes pool rowValues values := (realizes_exact pool rowValues values).mp
    (CommonNominalClampedGraphFamily.clamped_models_realizes _ _ _ _ _ model)
  intro edge active
  obtain ⟨branch, returned, _, children, auxiliaries⟩ := closed edge active
  cases firstFound : pool.definition edge.1 with
  | none => simp [CommonNominalRigidWorklist.inspect, firstFound] at returned
  | some first =>
      cases lastFound : pool.definition edge.2 with
      | none => simp [CommonNominalRigidWorklist.inspect, lastFound] at returned
      | some last =>
          cases checked : CommonNominalPlainInspection.inspect first last with
          | none => simp [CommonNominalRigidWorklist.inspect, firstFound, lastFound, checked] at returned
          | some checks =>
              have branchSame : branch = CommonNominalRigidWorklist.split checks := by
                simpa only [CommonNominalRigidWorklist.inspect, firstFound, lastFound, checked,
                  List.mem_singleton] using returned
              subst branch
              have inspected := CommonNominalPlainInspection.inspect_at_sound depth
                (TemplateRow.eval rowValues) values first last checks checked (by
                  intro check member
                  cases check with
                  | type source target =>
                      exact guarded (source, target) (children ((split_type_iff checks source target).mpr member))
                  | row source target =>
                      exact rowModel (source, target) (auxiliaries ((split_row_iff checks source target).mpr member)))
              exact CommonNominalFinite.producerLe_trans ((original edge.1 first firstFound).2 depth)
                (CommonNominalFinite.producerLe_trans inspected ((original edge.2 last lastFound).1 depth))

theorem finite_edges (pool : Pool nodes rows) (state : State nodes rows)
    (closed : FiniteBranchingWorklist.Closed (CommonNominalRigidWorklist.rigid pool)
      (CommonNominalRigidWorklist.inspect pool) state)
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models
      (CommonNominalClampedGraphFamily.clampedGraph (clampedPool pool) state.edges rowValues parameters) values)
    (rowModel : ∀ edge ∈ state.aux, rowHolds rowValues edge) (depth : Nat) :
    ∀ edge ∈ state.edges, BelowAt depth (values edge.1) (values edge.2) := by
  have step (depth : Nat) (guarded : ∀ edge ∈ state.edges, GuardedAt depth (values edge.1) (values edge.2)) :
      ∀ edge ∈ state.edges, BelowAt depth (values edge.1) (values edge.2) := by
    have rigid := rigid_at_of_guarded depth pool state closed rowValues parameters values model rowModel guarded
    intro edge member
    cases firstFound : pool.definition edge.1 with
    | none =>
        exact CommonNominalClampedGraphFamily.flexible_source_below _ _ _ _ _ model edge member
          ((clamped_free_iff pool edge.1).mpr firstFound) depth
    | some first =>
        apply CommonNominalClampedFiniteEdges.edge_at_of_rigid_source depth _ _ _ _ _ model edge member
        intro target notFree path
        apply rigid (edge.1, target)
        cases lastFound : pool.definition target with
        | none => exact False.elim (notFree ((clamped_free_iff pool target).mpr lastFound))
        | some last =>
            apply List.mem_filter.mpr
            exact ⟨CommonNominalRigidWorklist.mem_inventory _, by
              simp [firstFound, lastFound, (CastGraph.reachable_exact _ _ _).mpr path]⟩
  induction depth with
  | zero => exact step 0 (fun edge _ => CommonNominalFiniteRigidInspection.guarded_zero _ _)
  | succ depth ih => exact step (depth + 1) (fun edge member => ih edge member)

/-- All original final edges hold in every clamped model with the actual
final row constraints. No regular subtype edge is an extra premise. -/
theorem returned_clamped_sound (pool : Pool nodes rows) (edges : List (Edge nodes))
    (rowEdges : List (CommonNominalRigidWorklist.RowEdge rows)) (state : State nodes rows)
    (returned : state ∈ CommonNominalRigidWorklist.run pool edges rowEdges)
    (rowValues : Fin rows → Row) (parameters values : Fin nodes → Ty)
    (model : CommonNominalPresenceTailRegular.Models
      (CommonNominalClampedGraphFamily.clampedGraph (clampedPool pool) state.edges rowValues parameters) values)
    (rowModel : ∀ edge ∈ state.aux, rowHolds rowValues edge) :
    ∀ edge ∈ state.edges, edgeHolds values edge := by
  intro edge member depth
  exact finite_edges pool state (CommonNominalRigidWorklist.run_closed pool edges rowEdges state returned)
    rowValues parameters values model rowModel depth edge member

end Yulang.CommonNominalRigidClampedSoundness
