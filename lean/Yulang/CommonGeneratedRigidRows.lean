import Yulang.CommonGeneratedRigidInspection
import Yulang.CommonGeneratedPoolRows
import Yulang.CommonSymbolicRowConstraints

/-!
# Every generated symbolic branch has solvable row syntax

The actual rigid dispatcher copies only the two compared arrow annotations.
The source-generation invariant covers all collected subterms, so both
directions of the contravariant/covariant row comparisons remain variable or
empty rows. Static branch discharge does not introduce row syntax.

The final source/Core theorems discharge the row grammar internally for
every actual generated clause and every returned symbolic branch. They do
not assert that the remaining value/profile constraints have been solved.
-/

namespace Yulang.CommonGeneratedRigidRows

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (splitAtoms compile)
open CommonGeneratedRigidInspection (Checks RigidNode inspectSource inspect inspectSlot saturate)
open CommonSymbolicRowConstraints (AllRows CheckRows NodeRows)
open PresenceSourceConstraintSupport (simpleTyRows simpleRow)

variable {m : Nat}

theorem inspectSource_rows (pool : Pool m) (source : TyTerm (Fin m))
    (member : source ∈ pool.terms) (target : RigidNode pool) (targetSlot : Fin pool.size)
    (first : simpleTyRows source = true)
    (last : NodeRows (fun row => simpleRow row = true) target) :
    AllRows (fun row => simpleRow row = true) (inspectSource pool source member target targetSlot) := by
  cases source with
  | var | union | inter =>
      simp [inspectSource, CommonSymbolicRigidInspection.unionLeft, AllRows, CheckRows]
  | bottom | top | base | pair | variant =>
      cases target <;> simp [inspectSource, CommonSymbolicRigidInspection.inspect, AllRows, CheckRows]
  | arrow input incoming output outgoing =>
      apply CommonSymbolicRowConstraints.inspect_preserves_rows _ _ _ _ last
      have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
          simpleTyRows output = true) ∧ simpleRow outgoing = true := by
        simpa only [simpleTyRows, Bool.and_eq_true] using first
      exact ⟨parts.1.1.2, parts.2⟩
  | emptyRecord | exactEmpty | required | record | recordDefault =>
      cases target <;> simp [inspectSource, AllRows, CheckRows]

theorem inspect_rows (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (first : simpleTyRows source = true) (last : simpleTyRows target = true) :
    AllRows (fun row => simpleRow row = true) (inspect pool source target sourceMember targetMember) := by
  cases target with
  | var | emptyRecord | required | union | inter | exactEmpty | record | recordDefault | top =>
      simp [inspect, CommonSymbolicRigidInspection.interRight, AllRows, CheckRows]
  | bottom | base | pair | variant => exact inspectSource_rows pool source sourceMember _ _ first trivial
  | arrow input incoming output outgoing =>
      apply inspectSource_rows pool source sourceMember _ _ first
      have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
          simpleTyRows output = true) ∧ simpleRow outgoing = true := by
        simpa only [simpleTyRows, Bool.and_eq_true] using last
      exact ⟨parts.1.1.2, parts.2⟩

theorem inspect_slot_rows (pool : Pool m) (good : CommonGeneratedPoolRows.AllSimpleRows pool)
    (edge : Fin pool.size × Fin pool.size) :
    AllRows (fun row => simpleRow row = true) (inspectSlot pool edge) :=
  inspect_rows pool _ _ _ _ (good edge.1) (good edge.2)

theorem saturate_rows (pool : Pool m) (good : CommonGeneratedPoolRows.AllSimpleRows pool)
    (edges : List (Fin pool.size × Fin pool.size)) (branch : Checks pool)
    (member : branch ∈ saturate pool edges) :
    AllRows (fun row => simpleRow row = true) branch := by
  apply CommonSymbolicRowConstraints.discharge_preserves_rows _ _ _ branch member
  intro check present
  obtain ⟨edge, _, included⟩ := List.mem_flatMap.mp present
  exact inspect_slot_rows pool good edge check included

/-- Every source clause and every emitted branch are covered. No syntax
checker result or solver-success proof is supplied by the caller. -/
theorem generated_rows_supported (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : Checks (splitAtoms clause.pack).pool)
    (emitted : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges))) :
    RowFlowSchemes.supported (CommonSymbolicRowConstraints.emittedRows branch) = true :=
  CommonSymbolicRowConstraints.emitted_rows_supported branch
    (saturate_rows _ (CommonGeneratedPoolRows.generated_pool_rows expression clause member) _ branch emitted)

theorem generated_core_rows_supported (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : Checks (splitAtoms clause.pack).pool)
    (emitted : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges))) :
    RowFlowSchemes.supported (CommonSymbolicRowConstraints.emittedRows branch) = true :=
  CommonSymbolicRowConstraints.emitted_rows_supported branch
    (saturate_rows _ (CommonGeneratedPoolRows.generated_core_pool_rows expression clause member) _ branch emitted)

end Yulang.CommonGeneratedRigidRows
