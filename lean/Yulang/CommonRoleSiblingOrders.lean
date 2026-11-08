import Yulang.CommonRoleStatefulParentExample

namespace Yulang.CommonRoleSiblingOrders
open CommonRoleStatefulParentExample
open CommonRoleStatefulIndexSweep
open CommonRoleOrdinaryKnownness
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def forwardEdges : List (Edge 3) := [⟨0, 1⟩, ⟨1, 2⟩]

theorem forward_sweep : sweep forwardEdges s0 = ([true, true], s2) := by
  have known0 : detect s0.atoms (0 : Fin 3) = some .str := explicit_pair_detected _ _
  have known1 : detect s1.atoms (1 : Fin 3) = some .str := by
    simp [s1, s0, extend, CommonRoleCandidateStateFrontier.equality,
      detect, candidates, upper, lower, upperHead, lowerHead, State.empty]
  have first := index_from_detected_str s0 0 1 known0
  have second := index_from_detected_str s1 1 2 known1
  change produceIndex (extend s0 (1 : Fin 3) .str) (1 : Fin 3) (2 : Fin 3) =
    some (extend s1 (2 : Fin 3) .str) at second
  simp only [forwardEdges, sweep, visit, first, second]
  rfl

theorem forward_models (values : Fin 3 → Comp Common.model) :
    All Common.model values s2.atoms ↔
      Common.Equivalent (values (0 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (values (1 : Fin 3)).1 (.base .str) ∧
      Common.Equivalent (values (2 : Fin 3)).1 (.base .str) := by
  simp only [s2, s1, s0, CommonRoleCandidateStateFrontier.extend_exact]
  simp [State.empty, All, and_assoc]

/-- Both scheduling orders have identical final models, not identical atom lists. -/
theorem orders_models (values : Fin 3 → Comp Common.model) :
    All Common.model values (sweep forwardEdges s0).2.atoms ↔
      All Common.model values (sweep reverseEdges (sweep reverseEdges s0).2).2.atoms := by
  rw [forward_sweep, first_sweep]
  change All Common.model values s2.atoms ↔ All Common.model values (sweep reverseEdges s1).2.atoms
  rw [second_sweep]
  exact (forward_models values).trans (final_models values).symm

theorem forward_consistent : CommonRoleOpenPropagation.consistent s2 = true := by
  apply (CommonRoleOpenPropagation.consistent_exact _).mpr
  refine ⟨fun _ => Comp.pure Common.model (.base .str), (forward_models _).mpr ?_⟩
  exact ⟨Common.equivalent_refl _, Common.equivalent_refl _, Common.equivalent_refl _⟩

theorem forward_materialized : materialize s2.atoms (2 : Fin 3) = some Roles.Examples.str := by
  have known : detect s2.atoms (2 : Fin 3) = some .str := by
    simp [s2, s1, s0, extend, CommonRoleCandidateStateFrontier.equality,
      detect, candidates, upper, lower, upperHead, lowerHead, State.empty]
  simp only [materialize, known]
  rfl

def forwardRun : Option (State 3 × Roles.Term × RoleDictionaries.Answer) := do
  let initial ← seed
  let out := (sweep forwardEdges initial).2
  if CommonRoleOpenPropagation.consistent out then
    let argument ← materialize out.atoms 2
    pure (out, argument, RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal argument))
  else none

theorem forward_value : forwardRun = some (s2, Roles.Examples.str,
    RoleDictionaries.elaborate visible declarations_wellFormed (parentGoal Roles.Examples.str)) := by
  unfold forwardRun
  rw [seed_from_declaration]
  change (if CommonRoleOpenPropagation.consistent (sweep forwardEdges s0).2 then
    (materialize (sweep forwardEdges s0).2.atoms 2).bind _ else none) = _
  rw [forward_sweep]
  change (if CommonRoleOpenPropagation.consistent s2 then (materialize s2.atoms 2).bind _ else none) = _
  rw [forward_consistent]
  simp only [↓reduceIte]
  rw [forward_materialized]
  rfl

def observable (result : Option (State 3 × Roles.Term × RoleDictionaries.Answer)) :=
  result.map fun item => (item.2.1, item.2.2)

/-- The two real source-to-dictionary executions have the same language-facing result. -/
theorem orders_observable : observable forwardRun = observable CommonRoleStatefulParentExample.run := by
  rw [forward_value, run_value]
  rfl

end Yulang.CommonRoleSiblingOrders
