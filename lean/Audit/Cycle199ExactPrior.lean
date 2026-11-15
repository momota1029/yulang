import Yulang.GeneralDictionaryMatPriorConflict199
import Lean
open Yulang
example : ¬ B4SkeletonV5.EvidenceNode (B4TargetV6.prior
  (GeneralNominalCenteredHeadMatStepBoundary.boundary GeneralDictionaryMatPriorConflictSource199.roles)) :=
  GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode
#print axioms GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode
#print GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode
#print axioms GeneralDictionaryMatPriorConflict199.output_conflict
#print axioms GeneralDictionaryMatPriorConflict199.rejected
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Yulang.GeneralDictionaryMatPriorConflictSource199, `Yulang.GeneralDictionaryMatPriorConflictLocal199, `Yulang.GeneralDictionaryMatPriorConflict199]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if modules.contains e.header.moduleNames[i.toNat]! then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"

-- Explicit nonvacuous witness: every exact field premise, plus actual V6 rejection.
open Yulang.GeneralDictionaryMatPriorConflictSource199 in
example :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Checked registry ∧
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Initial registry root start ∧
    B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start ∧
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Models start model ∧
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Stable registry start root ∧
    B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry start root ∧
    B4TargetV6.Unique (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry start root 37 [] ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence
        registry start model child dictionary) [] [] ∧
    ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry start model root (.node 37 []) := by
  refine ⟨⟨rfl,checked⟩,initial_source,reachable,inhabited,GeneralDictionaryMatPriorConflict199.stable,
    GeneralDictionaryMatPriorConflictLocal199.safe,?_,.nil,GeneralDictionaryMatPriorConflict199.no_evidence⟩
  change GeneralNominalCenteredHeadCandidates.Unique registry context root 37 []
  simpa only [GeneralDictionaryMatPriorConflict199.children_empty] using GeneralDictionaryMatPriorConflictLocal199.unique
