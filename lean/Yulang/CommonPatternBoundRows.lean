import Yulang.CommonPatternBoundWorklist
import Yulang.CommonBoundRefRowDeclarations

/-! The pattern dispatcher preserves original row IDs and emits only
declarable simple-row checks or literal true auxiliaries. -/

namespace Yulang.CommonPatternBoundRows

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonGeneratedPoolRows (AllSimpleRows)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource)
open CommonBoundRefInspection (Ref InputCheck)
open CommonBoundRefWorklist (Edge Aux State)
open CommonPatternBoundWorklist (run inspect)
open CommonBoundRefRows (SourceRows OutputRows)
open CommonSymbolicRowConstraints (AllRows)
open PresenceSourceConstraintSupport (simpleRow simpleTyRows)

variable {m : Nat}

theorem dispatchOriginal_rows (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (first : SourceRows (fun row => simpleRow row = true) source) (last : simpleTyRows target = true) :
    OutputRows (fun row => simpleRow row = true)
      (CommonPatternBoundInspection.dispatchOriginal pool sourceRef source target member targetRef) := by
  unfold CommonPatternBoundInspection.dispatchOriginal
  split
  · exact CommonBoundRefRows.rigid_rows _ source _ targetRef first trivial
  · exact CommonBoundRefRows.optional_rows _ source _ _
  · exact CommonBoundRefRows.dispatchOriginal_rows pool sourceRef source _ _ targetRef first last

theorem dispatch_rows (pool : Pool m) (good : AllSimpleRows pool)
    (sourceRef : Ref pool) (source : PoolSource pool) (target : Ref pool)
    (first : SourceRows (fun row => simpleRow row = true) source) :
    OutputRows (fun row => simpleRow row = true)
      (CommonPatternBoundInspection.dispatch pool sourceRef source target) := by
  cases target with
  | original index => exact dispatchOriginal_rows pool sourceRef source _ _ _ first (good index)
  | _ =>
      simp only [CommonPatternBoundInspection.dispatch]
      exact CommonBoundRefRows.dispatch_rows pool good sourceRef source _ first

theorem inspect_rows (pool : Pool m) (good : AllSimpleRows pool) (source target : Ref pool)
    (branch : List (InputCheck pool)) (returned : branch ∈ CommonPatternBoundInspection.inspect pool source target) :
    AllRows (fun row => simpleRow row = true) branch := by
  have original := CommonBoundRefInspection.mem_prune _ branch returned
  cases found : CommonBoundRefInspection.sourceLayer pool source with
  | none => simp only [found, List.not_mem_nil] at original
  | some layer =>
      exact dispatch_rows pool good source layer target
        (CommonBoundRefRows.sourceLayer_rows pool good source layer found) branch
        (by simpa only [found] using original)

theorem inspect_aux_origin (pool : Pool m) (edge : Edge pool) (branch : CommonBoundRefWorklist.Branch pool)
    (returned : branch ∈ inspect pool edge) (item : Aux pool) (present : item ∈ branch.aux) :
    ∃ original ∈ CommonPatternBoundInspection.inspect pool edge.1.val edge.2.val, item ∈ original := by
  obtain ⟨⟨original, included⟩, _, rfl⟩ := List.mem_map.mp returned
  exact ⟨original, included,
    CommonBoundRefBranches.splitBranch_aux_origin pool _ original _ item present⟩

theorem inspect_row_or_true (pool : Pool m) (edge : Edge pool) (branch : CommonBoundRefWorklist.Branch pool)
    (returned : branch ∈ inspect pool edge) (item : Aux pool) (present : item ∈ branch.aux) :
    CommonBoundRefWorklist.RowOrTrue item := by
  have auxiliary : CommonBoundRefBranches.Auxiliary item := by
    obtain ⟨⟨original, _⟩, _, rfl⟩ := List.mem_map.mp returned
    exact CommonBoundRefBranches.splitBranch_auxiliary pool _ original _ item present
  obtain ⟨original, included, emitted⟩ := inspect_aux_origin pool edge branch returned item present
  cases item with
  | rowBelow => trivial
  | flag expression =>
      cases expression with
      | literal value =>
          cases value with
          | true => rfl
          | false =>
              have alive := CommonBoundRefInspection.prune_unblocked _ original included _ emitted
              cases alive
      | _ => cases auxiliary
  | _ => cases auxiliary

theorem run_aux_origin (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) (item : Aux pool) (present : item ∈ final.aux) :
    ∃ edge branch, branch ∈ inspect pool edge ∧ item ∈ branch.aux := by
  have origin := FiniteBranchingWorklist.run_aux_origin (CommonBoundRefWorklist.inventory pool)
    (CommonBoundRefWorklist.rigid pool) (inspect pool) edges [] final returned item present
  exact origin.elim (fun impossible => False.elim (List.not_mem_nil impossible)) id

theorem run_all_rows (pool : Pool m) (good : AllSimpleRows pool)
    (edges : List (Edge pool)) (final : State pool) (returned : final ∈ run pool edges) :
    AllRows (fun row => simpleRow row = true) final.aux := by
  intro item present
  obtain ⟨edge, branch, included, emitted⟩ := run_aux_origin pool edges final returned item present
  obtain ⟨original, inspected, contained⟩ := inspect_aux_origin pool edge branch included item emitted
  exact inspect_rows pool good edge.1.val edge.2.val original inspected item contained

theorem run_row_or_true (pool : Pool m) (edges : List (Edge pool)) (final : State pool)
    (returned : final ∈ run pool edges) (item : Aux pool) (present : item ∈ final.aux) :
    CommonBoundRefWorklist.RowOrTrue item := by
  obtain ⟨edge, branch, included, emitted⟩ := run_aux_origin pool edges final returned item present
  exact inspect_row_or_true pool edge branch included item emitted

theorem run_declare_checks_some (pool : Pool m) (good : AllSimpleRows pool)
    (edges : List (Edge pool)) (final : State pool) (returned : final ∈ run pool edges) :
    ∃ declared, CommonRowDeclarations.declareChecks final.aux = some declared :=
  CommonRowDeclarations.declare_checks_some final.aux (run_all_rows pool good edges final returned)
    (fun item member => (CommonBoundRefRowDeclarations.row_or_true_iff pool item).mpr
      (run_row_or_true pool edges final returned item member))

end Yulang.CommonPatternBoundRows
