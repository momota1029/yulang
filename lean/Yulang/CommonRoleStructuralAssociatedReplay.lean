import Yulang.CommonRoleStructuralAssociatedSolver

/-! A terminating mixed driver, actual ordinary consistency check, and recursive
structural diagnostic replay. The trace is generated from initial syntax and
actual associated declarations, not supplied as batches by the caller. Fixed
occurrence templates and source-slot maps remain explicit fragment boundaries. -/
namespace Yulang.CommonRoleStructuralAssociatedReplay
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteAssociatedClosure (Occurrence)
open CommonRoleStructuralAssociatedClosure (clauses Derives)
open CommonRoleStructuralAssociatedSolver (completeState)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleStructuralFrontierReplay (Replay)
open CommonRoleStructuralSaturationTrace (accumulate)

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
  (wf : Roles.WellFormed env.cores)

def generated (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) :=
  CommonRoleStructuralHornClosure.generated seeds (clauses env roles wf occurrences)
def finalAtoms (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) :=
  seeds ++ generated env roles wf occurrences seeds

/-- The public cumulative final list has exactly independent mixed derivations,
although its order differs from the internal worklist's reverse cache. -/
theorem final_membership (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (a) :
    a ∈ finalAtoms env roles wf occurrences seeds ↔ Derives env roles occurrences seeds a := by
  have same : a ∈ generated env roles wf occurrences seeds ↔
      a ∈ CommonRoleStructuralAssociatedClosure.saturate env roles wf occurrences seeds := by
    rw [← List.mem_reverse,generated,CommonRoleStructuralHornClosure.generated_reverse]
    rfl
  simp only [finalAtoms,List.mem_append,same,CommonRoleStructuralAssociatedClosure.saturate_exact env roles wf awf]
  exact ⟨fun h => h.elim (Derives.seed a) id,Or.inr⟩

theorem final_models (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model) :
    All Common.model v (finalAtoms env roles wf occurrences initial.atoms) ↔
      All Common.model v (completeState env roles wf occurrences initial).atoms := by
  rw [CommonRoleStructuralAssociatedSolver.completeState_models env roles wf awf]
  apply forall_congr'
  intro a
  exact imp_congr_left ((final_membership env roles wf awf ..).trans
    (CommonRoleStructuralAssociatedClosure.saturate_exact env roles wf awf ..).symm)

/-- All generated snapshots are satisfied by every final model. The converse
is intentionally absent: associated equations may narrow an earlier state. -/
theorem final_models_snapshot (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model)
    (models : All Common.model v (completeState env roles wf occurrences initial).atoms)
    (state : List (Atom (Fin n)))
    (present : state ∈ initial.atoms :: accumulate initial.atoms (generated env roles wf occurrences initial.atoms)) :
    All Common.model v state := by
  intro a member
  exact (final_models env roles wf awf occurrences initial v).mpr models a
    (CommonRoleStructuralSaturationTrace.accumulate_cover initial.atoms _ state present a member)

/-- Consistency is checked after both kinds of consequences have saturated.
The complete diagnostic sequence is then replayed without early plateau exits. -/
def run (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n) : Option (Replay n) :=
  if CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences initial) then
    CommonRoleStructuralFrontierReplay.run registry slots sources goal initial.atoms
      (accumulate initial.atoms (generated env roles wf occurrences initial.atoms))
  else none

theorem run_exact (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n) (output : Replay n) :
    run env roles wf occurrences registry slots sources goal initial = some output ↔
      (∃ v : Fin n → Comp Common.model, ∀ a, Derives env roles occurrences initial.atoms a →
        a.Holds Common.model v) ∧ ∃ checked : Checked registry,
        output = CommonRoleStructuralFrontierReplay.replay registry checked slots sources goal initial.atoms
          (accumulate initial.atoms (generated env roles wf occurrences initial.atoms)) := by
  unfold run
  split
  · rename_i consistent
    rw [CommonRoleStructuralFrontierReplay.run_exact]
    exact (and_iff_right ((CommonRoleStructuralAssociatedSolver.solver_exact env roles wf awf ..).mp consistent)).symm
  · rename_i inconsistent
    constructor
    · intro impossible; cases impossible
    · rintro ⟨models,_⟩
      exact False.elim (inconsistent ((CommonRoleStructuralAssociatedSolver.solver_exact env roles wf awf ..).mpr models))

/-- Work domain, trace length, rebuilds, and recursive child visits are all
bounded by input-computed syntax and the original role goal. No model premise
is needed beyond successful return by the actual ordinary checker. -/
theorem run_computed_bound (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n) (output : Replay n)
    (returned : run env roles wf occurrences registry slots sources goal initial = some output) :
    ∃ bound, CommonRoleStructuralMaterializationDomain.workDomain registry
        (finalAtoms env roles wf occurrences initial.atoms) slots goal = some bound ∧
      output.snapshots.length ≤ 1 + (CommonRoleStructuralHornClosure.carrierAtoms initial.atoms
        (clauses env roles wf occurrences)).length ∧
      output.rebuilds ≤ 1 + 2 * CommonRoleMaterializationProgress.potential goal ∧
      output.visits ≤ (1 + 2 * CommonRoleMaterializationProgress.potential goal) * bound.length ∧
      ∀ tree ∈ output.snapshots, ∀ target ∈ CommonRoleFrontierReachability.goals tree, target ∈ bound := by
  obtain ⟨_,checked,rfl⟩ := (run_exact env roles wf awf ..).mp returned
  refine ⟨_,(CommonRoleStructuralMaterializationDomain.workDomain_exact ..).mpr ⟨checked,rfl⟩,?_,?_,?_,?_⟩
  · rw [CommonRoleStructuralFrontierReplay.replay_snapshots,List.length_map,List.length_cons,
      CommonRoleStructuralSaturationTrace.accumulate_length]
    have bound := CommonRoleStructuralSaturationTrace.discoveries_length
      (CommonRoleStructuralHornClosure.rules initial.atoms (clauses env roles wf occurrences))
      (CommonRoleStructuralHornClosure.carrierAtoms initial.atoms (clauses env roles wf occurrences))
      (CommonRoleStructuralHornClosure.carrierAtoms initial.atoms (clauses env roles wf occurrences)).length []
    simpa only [generated,CommonRoleStructuralHornClosure.generated,Nat.add_comm] using Nat.add_le_add_left bound 1
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources goal
      initial.atoms _ _ (CommonRoleStructuralSaturationTrace.accumulate_chain _ _)
      (CommonRoleStructuralSaturationTrace.accumulate_cover _ _)).1
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources goal
      initial.atoms _ _ (CommonRoleStructuralSaturationTrace.accumulate_chain _ _)
      (CommonRoleStructuralSaturationTrace.accumulate_cover _ _)).2
  · intro tree member target node
    exact CommonRoleStructuralFrontierReplay.replay_work_present registry checked slots sources goal
      initial.atoms _ _ (CommonRoleStructuralSaturationTrace.accumulate_cover _ _) tree member target node

/-- Graphs are regenerated on every occurrence, even when the role tree is
reused. Per-occurrence old demands remain explicit and are never silently lost. -/
def runGraphs (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n)
    (old : Nat → Plan (Fin n)) :=
  if CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences initial) then
    CommonRoleStructuralFrontierReplay.runGraphs registry slots sources goal initial.atoms
      (accumulate initial.atoms (generated env roles wf occurrences initial.atoms)) old
  else none

theorem runGraphs_exact (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n)
    (old : Nat → Plan (Fin n)) (output : Replay n)
    (returned : run env roles wf occurrences registry slots sources goal initial = some output) :
    ∃ graphs, runGraphs env roles wf occurrences registry slots sources goal initial old = some (output,graphs) ∧
      graphs.map some = (initial.atoms :: accumulate initial.atoms
        (generated env roles wf occurrences initial.atoms)).mapIdx
          (fun i atoms => CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old i) goal) := by
  unfold run at returned
  split at returned
  · rename_i valid
    simp only [runGraphs,valid,ite_true]
    exact CommonRoleStructuralFrontierReplay.runGraphs_exact _ _ _ _ _ _ _ _ returned
  · cases returned

/-- Final graph representation is exact for every assignment and retains
source-role obligations separately from ordinary consistency. -/
theorem final_graph_models_exact (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n)
    (old : Plan (Fin n)) (v : Fin n → Comp Common.model) :
    (∃ output, CommonRoleStructuralOrdinaryMaterialization.run registry slots sources
        (finalAtoms env roles wf occurrences initial.atoms) old goal = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 v) ↔
      Checked registry ∧ (∀ a, Derives env roles occurrences initial.atoms a → a.Holds Common.model v) ∧
        ∃ sourceValues, CommonRoleCaptureBatchModels.SharedFits v sourceValues old ∧
          CommonRoleGuardedIntervalPlans.Derives registry slots sources v sourceValues
            (CommonRoleStructuralOrdinaryMaterialization.materializeGoal
              (finalAtoms env roles wf occurrences initial.atoms) slots goal) := by
  change (∃ output, CommonRoleFrontierGraphs.run registry slots sources
      (finalAtoms env roles wf occurrences initial.atoms) old _ = some output ∧ _) ↔ _
  rw [CommonRoleFrontierGraphs.run_models_exact]
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  exact forall_congr' fun a => imp_congr_left (final_membership env roles wf awf ..)

end Yulang.CommonRoleStructuralAssociatedReplay
