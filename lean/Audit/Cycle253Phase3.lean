import Yulang.GeneralDeclarationProducerRank253
import Yulang.GeneralDeclarationOutputDepth253
import Yulang.GeneralNominalPublicBasis253
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let names := #[``Yulang.GeneralDeclarationProducerRank253.mass,
  ``Yulang.GeneralDeclarationProducerRank253.Child,
  ``Yulang.GeneralDeclarationProducerRank253.child_mass,
  ``Yulang.GeneralDeclarationProducerRank253.accessible,
  ``Yulang.GeneralDeclarationProducerRank253.calls_wellFounded,
  ``Yulang.GeneralDeclarationProducerRank253.child_inputs_independent,
  ``Yulang.GeneralDeclarationProducerRank253.binder_producer,
  ``Yulang.GeneralDeclarationOutputDepth253.subst_supported,
  ``Yulang.GeneralDeclarationOutputDepth253.associated_bound,
  ``Yulang.GeneralDeclarationOutputDepth253.produced_bound,
  ``Yulang.GeneralDeclarationOutputDepth253.associated_from_children,
  ``Yulang.GeneralNominalPublicBasis253.privateName,
  ``Yulang.GeneralNominalPublicBasis253.private_not_ports,
  ``Yulang.GeneralNominalPublicBasis253.private_not_names,
  ``Yulang.GeneralNominalPublicBasis253.basis,
  ``Yulang.GeneralNominalPublicBasis253.basis_separated,
  ``Yulang.GeneralNominalPublicBasis253.lower_private_free,
  ``Yulang.GeneralNominalPublicBasis253.upper_private_free,
  ``Yulang.GeneralNominalPublicBasis253.lower_safe,
  ``Yulang.GeneralNominalPublicBasis253.upper_safe]
 for name in names do
  unless environment.contains name do throwError "Missing declaration {name}"
  for dependency in ← collectAxioms name do
   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
 logInfo m!"CYCLE253-PHASE3-PASS: {names.size} explicit declarations in 3 modules"
