import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalPrincipalClosure
/-! Complete originating-module type and axiom audit of the exact source
census and the conditional solution-set separation. It does not assert a
complete original SourceJudgment or a native source-to-store correspondence.
Build `+YulangClosure.OriginalPrincipalClosure` before running this file. -/
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false
set_option pp.maxSteps 1000000
open Lean Elab Command
run_cmd do
  let moduleName := `YulangClosure.OriginalPrincipalClosure
  let roots : Array Name := #[
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.complete_call_census,
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.original_complete_apps,
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.output_keeps_both_return_telescopes,
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.actual_output_boundaries,
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.f_use_binder,
    `YulangClosure.OriginalPrincipalClosure.ObservedReplay.direct_receivers_after_all_frames,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.complete_call_census,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.direct_return_keeps_both_calls,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.written_boundary_telescope,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.direct_receivers_after_all_frames,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.shared_binder_census,
    `YulangClosure.OriginalPrincipalClosure.DirectReturn.formal_shared_evidence_present,
    `YulangClosure.OriginalPrincipalClosure.DirectReturnInterfaces.recursive_call,
    `YulangClosure.OriginalPrincipalClosure.DirectReturnInterfaces.integer_instance,
    `YulangClosure.OriginalPrincipalClosure.DirectReturnInterfaces.boolean_instance,
    `YulangClosure.OriginalPrincipalClosure.DirectReturnInterfaces.closed_interfaces_rename_fixed,
    `YulangClosure.OriginalPrincipalClosure.TwoUses.sub_preserves_atomView,
    `YulangClosure.OriginalPrincipalClosure.TwoUses.distinct_atoms_not_sub,
    `YulangClosure.OriginalPrincipalClosure.TwoUses.ordinary_joint_solution,
    `YulangClosure.OriginalPrincipalClosure.TwoUses.intruded_no_joint_solution,
    `YulangClosure.OriginalPrincipalClosure.TwoUses.solution_set_separation,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.occurs_structural,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.occurs_union,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.occurs_intersection,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.union_lookup,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.intersection_lookup,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.nodeRel_preserves_view,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.layer_preserves_atom,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.distinct_atoms_not_regular_sub,
    `YulangClosure.OriginalPrincipalClosure.RegularSeparation.shared_use_observations_impossible
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "module not imported: {moduleName}"
  let mut targets : Array Name := #[]
  let mut theorems : Array Name := #[]
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      targets := targets.push name
      match info with
      | .thmInfo _ => theorems := theorems.push name
      | .axiomInfo _ => throwError "project axiom: {name}"
      | _ => pure ()
  if targets.isEmpty then throwError "empty originating inventory"
  for root in roots do
    unless theorems.contains root do
      throwError "required root is not an originating theorem: {root}"
  for name in targets do
    logInfo m!"CLOSURE_BEGIN {name}"
    let id := mkIdent name
    elabCommand (← `(#check @$id))
    elabCommand (← `(#print axioms $id))
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "unapproved axiom in {name}: {ax}"
    logInfo m!"CLOSURE_END {name}"
  logInfo m!"CLOSURE_CENSUS declarations={targets.size} theorems={theorems.size} publicRoots={roots.size}"
