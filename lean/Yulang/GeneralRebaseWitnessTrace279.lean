import Yulang.GeneralRebaseWitnessBudget279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWitnessTrace279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Committed Installable)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split reachable_step administrative_plans)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseQuietBound277 (Counted remaining_le)
open GeneralRebaseMixedCounts277 (Actual quietCap)
open GeneralRebaseWitnessBudget279
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start : State roles}

def Covers (r : Registry) (root : Occurrence roles) (start : State roles) (facts : List (Fact roles)) : Prop :=
  ∀ n before, Counted (Actual r root) start n before → ∀ effect : Effect roles,
    Installable (registry r) before effect → ¬ Committed before effect.plan →
    Actual r root before (install before effect) →
    ∃ f ∈ facts, ¬ Holds before f ∧ Holds (install before effect) f

theorem trace_budget {facts : List (Fact roles)} (cover : Covers r root start facts)
    (formed : Reachable r root start) {after : State roles} {n : Nat}
    (walk : Counted (Actual r root) start n after) :
    Reachable r root after ∧
      after.plans.length + remaining Holds facts after ≤ start.plans.length + remaining Holds facts start := by
  induction walk with
  | nil => exact ⟨formed,Nat.le_refl _⟩
  | tail path action ih =>
    refine ⟨reachable_step ih.1 action,?_⟩
    rcases split ih.1 action with quiet | ⟨effect,enabled,novel,rfl⟩
    · rw [administrative_plans quiet]
      have smaller := remaining_monotone Holds facts (administrative_growth quiet)
      omega
    · obtain ⟨fact,listed,old,new⟩ := cover _ _ path effect enabled novel action
      have strict := remaining_decreases Holds facts (installation_growth enabled.snapshot_eq) listed old new
      change (_ :: _).length + _ ≤ _
      simp only [List.length_cons]
      omega

theorem total_length {facts : List (Fact roles)} (cover : Covers r root start facts)
    (formed : Reachable r root start) (walk : Counted (Actual r root) start n after) :
    n ≤ remaining Holds facts start + (remaining Holds facts start + 1) * quietCap r start (remaining Holds facts start) :=
  GeneralRebaseBoundedInstallAcc277.bounded_steps formed _ (fun _ _ trace => by
    have limit := (trace_budget cover formed trace).2
    omega) walk

theorem accessible_from {facts : List (Fact roles)} (cover : Covers r root start facts)
    (formed : Reachable r root start) : Acc (fun after before => Actual r root before after) start :=
  GeneralRebaseBoundedInstallAcc277.adapter_accessible formed (remaining Holds facts start) (fun _ _ trace => by
    have limit := (trace_budget cover formed trace).2
    omega)

theorem global_covers (basis : WitnessBasis r root) (formed : Reachable r root start) :
    Covers r root start basis.facts := by
  intro n before path
  have all : Reachable r root before := by
    induction path with
    | nil => exact formed
    | tail _ action ih => exact reachable_step ih action
  intro effect enabled novel _
  exact basis.covers before all effect enabled novel

end Yulang.GeneralRebaseWitnessTrace279
