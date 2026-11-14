import Yulang.GeneralNominalCenteredCanonicalExecutor

/-! Actual two-way transition correspondence is sufficient for canonical exit
lifting. No agreement of arbitrary terminal choices is required. -/
namespace Yulang.GeneralNominalCenteredCanonicalTransport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal GeneralNominalCenteredCanonicalExecutor
open GeneralCanonicalRegistry (canonical)
open GeneralNominalCenteredGroundComposition (terminalState)

variable {roles : Roles.RoleDecls}

structure Simulation (first last : Registry) (root : Occurrence roles)
    (related : State roles → State roles → Prop) : Prop where
  forward : ∀ left right, related left right → ∀ next, Step first root left next →
    ∃ nextRight, Step last root right nextRight ∧ related next nextRight
  backward : ∀ left right, related left right → ∀ next, Step last root right next →
    ∃ nextLeft, Step first root left nextLeft ∧ related nextLeft next
  observations : ∀ left right, related left right → ∀ demand frontier,
    Local last left demand frontier ↔ Local last right demand frontier

theorem steps_backward (simulation : Simulation first last root related)
    (same : related left right) (path : B4Target.Steps (Step last root) right final) :
    ∃ result, B4Target.Steps (Step first root) left result ∧ related result final := by
  induction path with
  | refl => exact ⟨left,.refl,same⟩
  | @tail middle final path step ih =>
    obtain ⟨previous,trace,related⟩ := ih
    obtain ⟨next,edge,nextRelated⟩ := simulation.backward previous middle related final step
    exact ⟨next,.tail trace edge,nextRelated⟩

theorem halt_reflects (simulation : Simulation first last root related)
    (same : related left right) (halted : ∀ next, ¬ Step last root right next) :
    ∀ next, ¬ Step first root left next := by
  intro next step
  obtain ⟨nextRight,edge,_⟩ := simulation.forward left right same next step
  exact halted nextRight edge

theorem lifted_exit_of_simulation
    (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = [])
    (simulation : Simulation registry (canonical registry) root related)
    (initial : related state state) : ∃ final, LiftedExit registry state root final := by
  have canonicalReachable := GeneralNominalCenteredRegistryPassive.canonical_reachable reachable empty
  have canonicalChecked := canonical_checked checked
  obtain ⟨final,path,same⟩ := steps_backward simulation initial
    (GeneralNominalCenteredAdministrativeComposition.execution _ canonicalChecked state root canonicalReachable)
  exact ⟨final,⟨path,halt_reflects simulation same
    (GeneralNominalCenteredAdministrativeComposition.halted _ canonicalChecked state root canonicalReachable)⟩,
    simulation.observations final _ same⟩

/-- This is the still-required concrete permutation simulation, scoped to the
only inputs on which the canonical executor needs it. -/
def ReachablePermutationSimulation (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root,
    B4TargetV5.Reachable (boundary roles) registry root state →
    state.erased.current.packets = [] →
    ∃ related : State roles → State roles → Prop,
      related state state ∧ Simulation registry (canonical registry) root related

theorem canonical_exit_lifting (simulation : ReachablePermutationSimulation roles) : CanonicalExitLifting roles := by
  intro registry checked state root reachable empty
  obtain ⟨related,initial,rule⟩ := simulation registry checked state root reachable empty
  exact lifted_exit_of_simulation checked reachable empty rule initial

theorem canonicalLocalOrder (simulation : ReachablePermutationSimulation roles) : CanonicalLocalOrder roles :=
  GeneralNominalCenteredCanonicalExecutor.canonicalLocalOrder (canonical_exit_lifting simulation)

theorem composition (simulation : ReachablePermutationSimulation roles)
    (evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles))
    (generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)) :
    B4TargetV5.Statement (boundary roles) (executor roles) :=
  GeneralNominalCenteredCanonicalExecutor.composition
    ⟨canonical_exit_lifting simulation,evidenceNode,generatedChildren⟩

end Yulang.GeneralNominalCenteredCanonicalTransport
