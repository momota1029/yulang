import Yulang.CommonRoleLinearSimulation
import Yulang.RoleDictionaries

/-!
# Finite regular role evidence for compiled linear programs

The declaration registry is finite actual `Roles.Impl` data. The independent
Common derivation interprets its actual head and child patterns and uses one
unchanged visible registry throughout. Every head match quantifies arbitrary
Common substitutions. Reflection to finite machine configurations is proved,
not supplied by a decoder or a termination hypothesis.

This module proves derivability, before the separate ambiguity condition. It
does not identify raw derivability with resolved role evidence in an overlapping
registry and does not claim undecidability by itself.
-/

namespace Yulang.CommonRoleLinearEvidence

open CommonRoleLinearClock

abbrev Registry := List (Nat × Rule)

def visible (registry : Registry) (terminal : Nat) : List Roles.Impl :=
  terminalImpl 0 terminal :: registry.map (fun entry => compile (entry.1 + 1) entry.2)

def LinearRegistry (registry : Registry) : Prop :=
  ∀ entry ∈ registry, Linear entry.2

def checkRegistry (registry : Registry) : Bool := registry.all (fun entry => checkLinear entry.2)

theorem checkRegistry_exact (registry : Registry) :
    checkRegistry registry = true ↔ LinearRegistry registry := by
  simp [checkRegistry, LinearRegistry, List.all_eq_true, checkLinear_exact]

theorem compiled_registry_accepted (registry : Registry) (terminal : Nat)
    (linear : LinearRegistry registry) :
    CheckedRoles.checkDatabase (visible registry terminal) = true := by
  simp only [CheckedRoles.checkDatabase, visible, List.all_cons, terminal_accepted,
    Bool.true_and, List.all_map, List.all_eq_true]
  intro entry member
  exact compile_accepted (entry.1 + 1) entry.2 (linear entry member)

theorem compiled_registry_wellFormed (registry : Registry) (terminal : Nat)
    (linear : LinearRegistry registry) : Roles.WellFormed (visible registry terminal) :=
  (CheckedRoles.checkDatabase_exact _).mp (compiled_registry_accepted registry terminal linear)

/-- Finite halting runs of the independent linear machine. -/
inductive MachineHalts (registry : Registry) (terminal : Nat) : Configuration → Prop where
  | done {configuration : Configuration} (finished : configuration.role = terminal) :
      MachineHalts registry terminal configuration
  | step {source target : Configuration} (entry : Nat × Rule)
      (member : entry ∈ registry) (transition : entry.2.Step source target)
      (rest : MachineHalts registry terminal target) : MachineHalts registry terminal source

/-- The Common interpretation of the actual compiled empty-where terminal
declaration and each actual single-where rule. It does not inspect a solver. -/
inductive Derives (registry : Registry) (terminal : Nat) : SemanticGoal → Prop where
  | done {goal : SemanticGoal} (finished : goal.role = terminal) :
      Derives registry terminal goal
  | step {goal : SemanticGoal} (entry : Nat × Rule) (assignment : Nat → Common.Ty)
      (member : entry ∈ registry) (matched : HeadMatches entry.2 goal assignment)
      (child : Derives registry terminal (childGoal entry.2 assignment)) :
      Derives registry terminal goal

theorem derives_transport {registry : Registry} {terminal : Nat} {first last : SemanticGoal}
    (same : GoalEquivalent first last) (derivation : Derives registry terminal first) :
    Derives registry terminal last := by
  cases derivation with
  | done finished => exact .done (same.1.symm.trans finished)
  | step entry assignment member matched child =>
      exact .step entry assignment member (GoalEquivalent.trans matched same) child

theorem machine_to_derives {registry : Registry} {terminal : Nat} {configuration : Configuration}
    (run : MachineHalts registry terminal configuration) :
    Derives registry terminal (goalOf configuration) := by
  induction run with
  | done finished => exact .done finished
  | @step source target entry member transition rest ih =>
      obtain ⟨assignment, matched, sameChild⟩ := finite_step_instance entry.2 source target transition
      exact .step entry assignment member matched (derives_transport (GoalEquivalent.symm sameChild) ih)

theorem derives_to_machine {registry : Registry} {terminal : Nat}
    (linear : LinearRegistry registry) {goal : SemanticGoal}
    (derivation : Derives registry terminal goal) :
    ∀ configuration, GoalEquivalent goal (goalOf configuration) →
      MachineHalts registry terminal configuration := by
  induction derivation with
  | done finished =>
      intro configuration same
      exact .done (same.1.symm.trans finished)
  | step entry assignment member matched child ih =>
      intro source same
      obtain ⟨target, transition, sameChild⟩ := matched_child_finite entry.2
        (linear entry member) source assignment (GoalEquivalent.trans matched same)
      exact .step entry member transition (ih target sameChild)

/-- No termination assumption: finite evidence exists exactly when the
independent machine has a finite halting run. The registry is unchanged. -/
theorem derives_iff_machine_halts (registry : Registry) (terminal : Nat)
    (linear : LinearRegistry registry) (configuration : Configuration) :
    Derives registry terminal (goalOf configuration) ↔ MachineHalts registry terminal configuration :=
  ⟨fun derivation => derives_to_machine linear derivation configuration (GoalEquivalent.refl _),
    machine_to_derives⟩

/-- A terminal root and a transition root are distinct candidates. Different
keys distinguish different declarations even if their head patterns coincide. -/
def HeadOverlap (registry : Registry) (terminal : Nat) (goal : SemanticGoal) : Prop :=
  (goal.role = terminal ∧ ∃ entry ∈ registry, ∃ assignment, HeadMatches entry.2 goal assignment) ∨
  ∃ first ∈ registry, ∃ last ∈ registry, first ≠ last ∧
    (∃ assignment, HeadMatches first.2 goal assignment) ∧
    (∃ assignment, HeadMatches last.2 goal assignment)

def UniqueHead (registry : Registry) (terminal : Nat) (entry : Nat × Rule)
    (goal : SemanticGoal) : Prop :=
  goal.role ≠ terminal ∧ ∀ other ∈ registry,
    (∃ assignment, HeadMatches other.2 goal assignment) → other = entry

inductive ReachesOverlap (registry : Registry) (terminal : Nat) : SemanticGoal → Prop where
  | here {goal : SemanticGoal} (overlap : HeadOverlap registry terminal goal) :
      ReachesOverlap registry terminal goal
  | descend {goal : SemanticGoal} (entry : Nat × Rule) (assignment : Nat → Common.Ty)
      (member : entry ∈ registry) (matched : HeadMatches entry.2 goal assignment)
      (unique : UniqueHead registry terminal entry goal)
      (child : ReachesOverlap registry terminal (childGoal entry.2 assignment)) :
      ReachesOverlap registry terminal goal

def Resolves (registry : Registry) (terminal : Nat) (goal : SemanticGoal) : Prop :=
  Derives registry terminal goal ∧ ¬ ReachesOverlap registry terminal goal

end Yulang.CommonRoleLinearEvidence
