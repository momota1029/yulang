import Yulang.CommonRoleMixedEvidenceClosure

/-! The mixed finite associated/ordinary closure supplies actual checked replay.
No external batch trace, model, fuel or stopping certificate is an input.
This is still an explicit finite source fragment, not the general B4 driver. -/
namespace Yulang.CommonRoleMixedEvidenceReplay
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteAssociatedClosure (Source Fact)
open CommonRoleMixedEvidenceClosure (Derives saturate completed)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleFrontierReplay (Replay)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def batches (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : List (State n) :=
  (saturate env roles wf p s).map CommonRoleEvidenceReplay.batch

private theorem append_batch (s : State n) (f : Fact n) :
    CommonRoleCheckedOrdinaryReplay.append s (CommonRoleEvidenceReplay.batch f) =
      CommonRoleCandidateStateFrontier.extend s f.1 f.2 := by
  cases s
  rfl

private theorem final_emit (fs : List (Fact n)) (s : State n) :
    CommonRoleCheckedOrdinaryReplay.final s (fs.map CommonRoleEvidenceReplay.batch) =
      CommonRoleFiniteAssociatedModels.emit fs s := by
  induction fs generalizing s with
  | nil => rfl
  | cons f rest ih =>
    rcases f with ⟨i,b⟩
    simp only [List.map_cons,CommonRoleCheckedOrdinaryReplay.final,append_batch,
      CommonRoleFiniteAssociatedModels.emit,ih]

/-- Literal final-state equality, including atom ordering and multiplicity. -/
theorem final_eq_completed (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    CommonRoleCheckedOrdinaryReplay.final s (batches env roles wf p s) =
      completed env roles wf p s := final_emit ..

/-- One assignment satisfies the original state and every independently derived
mixed scalar obligation. Associated output may remove original models. -/
def Models (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (p : Source n) (s : State n) : Prop :=
  ∃ v : Fin n → Comp Common.model, All Common.model v s.atoms ∧
    ∀ f, Derives env roles p s f → Common.Equivalent (v f.1).1 (.base f.2)

theorem completed_models_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) :
    (completed env roles wf p s).Models ↔ Models env roles p s :=
  exists_congr (CommonRoleMixedEvidenceClosure.completed_models env roles wf awf p s)

theorem validate_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) :
    CommonRoleCheckedOrdinaryReplay.validate s (batches env roles wf p s) = true ↔
      Models env roles p s := by
  rw [CommonRoleCheckedOrdinaryReplay.validate_exact,final_eq_completed,
    completed_models_iff env roles wf awf]

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal) :
    Option (Replay n) :=
  CommonRoleCheckedOrdinaryReplay.run registry slots sources original s (batches env roles wf p s)

/-- Exact replay success, not role resolution success. The associated declaration
well-formedness premise is used only to relate execution to independent meaning. -/
theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (output : Replay n) :
    run env roles wf p s registry slots sources original = some output ↔
      Models env roles p s ∧ ∃ checked : CommonRoleIntervalWorkClosure.Checked registry,
        output = CommonRoleFrontierReplay.replay registry checked slots sources original s.atoms
          ((CommonRoleCheckedOrdinaryReplay.trace s (batches env roles wf p s)).map State.atoms) := by
  rw [run,CommonRoleCheckedOrdinaryReplay.run_exact,final_eq_completed,
    completed_models_iff env roles wf awf]

theorem run_none_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal) :
    run env roles wf p s registry slots sources original = none ↔
      ¬ Models env roles p s ∨ ¬ CommonRoleIntervalWorkClosure.Checked registry := by
  rw [run,CommonRoleCheckedOrdinaryReplay.run_none_iff,final_eq_completed,
    completed_models_iff env roles wf awf]

/-- Every distinct mixed fact generates one batch, independent of derivation depth. -/
theorem batches_bounded (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    (batches env roles wf p s).length ≤ n * 4 := by
  simpa only [batches,List.length_map] using
    CommonRoleMixedEvidenceClosure.saturate_bounded env roles wf p s

/-- The computed closure supplies a finite update count, while the original goal
supplies diagnostic rebuild/visit bounds. This is not a total runtime bound. -/
theorem run_computed_bound (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (output : Replay n) (returned : run env roles wf p s registry slots sources original = some output) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry original = some bound ∧
      output.snapshots.length = 1 + (saturate env roles wf p s).length ∧
      output.snapshots.length ≤ 1 + n * 4 ∧
      output.rebuilds ≤ 1 + CommonRoleMaterializationProgress.potential original ∧
      output.visits ≤ (1 + CommonRoleMaterializationProgress.potential original) * bound.length := by
  obtain ⟨bound,hbound,hlen,hrebuild,hvisits⟩ :=
    CommonRoleCheckedOrdinaryReplay.run_computed_bound registry slots sources original
      s (batches env roles wf p s) output returned
  refine ⟨bound,hbound,?_,?_,hrebuild,hvisits⟩
  · simpa only [batches,List.length_map] using hlen
  · rw [hlen]
    exact Nat.add_le_add_left (batches_bounded env roles wf p s) 1

def runGraphs (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (old : Nat → Plan (Fin n)) :=
  CommonRoleCheckedOrdinaryReplay.runGraphs registry slots sources original s (batches env roles wf p s) old

theorem run_graphs_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources) (original : Goal)
    (output : Replay n) (returned : run env roles wf p s registry slots sources original = some output)
    (old : Nat → Plan (Fin n)) :
    ∃ graphs, runGraphs env roles wf p s registry slots sources original old = some (output,graphs) ∧
      graphs.map some =
        (s.atoms :: (CommonRoleCheckedOrdinaryReplay.trace s (batches env roles wf p s)).map State.atoms).mapIdx
          (fun i atoms => CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old i) original) :=
  CommonRoleCheckedOrdinaryReplay.run_graphs_exact registry slots sources original
    s (batches env roles wf p s) output returned old

end Yulang.CommonRoleMixedEvidenceReplay
