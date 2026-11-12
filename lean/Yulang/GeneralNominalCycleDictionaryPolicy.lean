import Yulang.GeneralDictionarySelectionPolicy
import Yulang.GeneralNominalCycleBoundary
import Yulang.GeneralNominalCycleRegressions

/-! I-22 dictionary guards for the actual cycle boundary. All four remaining
fields are quantified, not claimed to have been implemented. Payload Evidence
alone is not selected classification; only completed selected trees are guarded.
The executor corollary retains Exact and Checked. -/
namespace Yulang.GeneralNominalCycleDictionaryPolicy

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver
open B4TargetV3

abbrev boundary (roles : Roles.RoleDecls)
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary roles)) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalCycleBoundary.localFields roles) remaining

variable {roles : Roles.RoleDecls}
variable (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary roles))
variable {registry : Registry} {state : State roles} {root child : Occurrence roles}

/-- The completed schema uses exactly the actual cycle classifier, not placeholder K2. -/
theorem local_iff (frontier : Frontier (Occurrence roles)) :
    Local (boundary roles remaining) registry state root frontier ↔
      GeneralNominalCycleK2.Local registry state.context root frontier :=
  (GeneralNominalLocalBoundary.local_extension remaining frontier).symm.trans
    (GeneralNominalCycleBoundary.local_projection registry state root frontier)

/-- Transfer a lossless tree on the real cycle local relation without an executor. -/
theorem resolves_iff (tree : Tree) :
    Resolves (Local (boundary roles remaining) registry state) root tree ↔
      Resolves (GeneralNominalCycleK2.Local registry state.context) root tree := by
  have same : Local (boundary roles remaining) registry state =
      GeneralNominalCycleK2.Local registry state.context := by
    funext demand frontier
    exact propext (local_iff remaining frontier)
  rw [same]
  rfl

theorem selected_excludes_cycles
    (selected : Classify (boundary roles remaining) registry state root (.selected dictionary)) :
    ¬ GeneralNominalCycleK2.RootK2 state.context.state root.demand ∧
      ¬ GeneralNominalCycleK2.CandidateK2 registry state.context root :=
  ⟨GeneralDictionarySelectionPolicy.selected_not_rootK2 selected,
    GeneralDictionarySelectionPolicy.selected_not_candidateK2 selected⟩

/-- Every actually selected source descendant is guarded by both concrete cycle tests. -/
theorem selected_descendant_excludes_cycles
    (path : GeneralDictionarySelectionPolicy.SelectedPath (boundary roles remaining) registry state root child)
    (selected : Classify (boundary roles remaining) registry state root (.selected dictionary)) :
    ¬ GeneralNominalCycleK2.RootK2 state.context.state child.demand ∧
      ¬ GeneralNominalCycleK2.CandidateK2 registry state.context child :=
  GeneralDictionarySelectionPolicy.selected_path_excludes_K2 path selected

include remaining in
theorem completed_excludes_cycles
    (resolved : Resolves (GeneralNominalCycleK2.Local registry state.context) root tree)
    (done : Completed tree (.selected dictionary)) :
    ¬ GeneralNominalCycleK2.RootK2 state.context.state root.demand ∧
      ¬ GeneralNominalCycleK2.CandidateK2 registry state.context root :=
  GeneralDictionarySelectionPolicy.completed_tree_excludes_K2
    ((resolves_iff remaining tree).mpr resolved) done

include remaining in
theorem cycle_prevents_completed
    (resolved : Resolves (GeneralNominalCycleK2.Local registry state.context) root tree)
    (cycle : GeneralNominalCycleK2.RootK2 state.context.state root.demand ∨
      GeneralNominalCycleK2.CandidateK2 registry state.context root) :
    ¬ Completed tree (.selected dictionary) := by
  intro done
  have safe := completed_excludes_cycles remaining resolved done
  exact cycle.elim safe.1 safe.2

theorem descendant_cycle_prevents_completed
    (resolved : Resolves (GeneralNominalCycleK2.Local registry state.context) root tree)
    (path : GeneralDictionarySelectionPolicy.SelectedPath (boundary roles remaining) registry state root child)
    (cycle : GeneralNominalCycleK2.RootK2 state.context.state child.demand ∨
      GeneralNominalCycleK2.CandidateK2 registry state.context child) :
    ¬ Completed tree (.selected dictionary) :=
  GeneralDictionarySelectionPolicy.K2_descendant_prevents_completed
    ((resolves_iff remaining tree).mpr resolved) path cycle

/-- Conditional public-return guarantee, not a constructed exact executor. -/
theorem exact_executor_excludes_cycles
    (executor : Executor (GeneralNominalCycleBoundary.vocabulary roles))
    (exact : Exact (boundary roles remaining) executor)
    (checked : (boundary roles remaining).Checked registry)
    (done : Completed (executor.run registry state root).2 (.selected dictionary)) :
    ¬ GeneralNominalCycleK2.RootK2 (executor.run registry state root).1.context.state root.demand ∧
      ¬ GeneralNominalCycleK2.CandidateK2 registry (executor.run registry state root).1.context root :=
  GeneralDictionarySelectionPolicy.exact_executor_excludes_K2 executor exact checked done

section Regressions
abbrev exampleRoles := GeneralDeclarationExamples.roles
open GeneralNominalRecursiveExamples (lenRegistry lenRoot)
open GeneralNominalCycleRegressions (nominalLenRoot)

/-- `len (nest 0)` graph fixture: where-free Len still rejects at the cyclic root. -/
theorem nest_len_rejected
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary exampleRoles)) :
    Classify (boundary exampleRoles remaining) lenRegistry
      (initial GeneralNominalProgressObstruction.context nominalLenRoot) nominalLenRoot .rejected :=
  .rejected ⟨GeneralNominalCycleRegressions.nominal_len_K2.2.1,
    Or.inl GeneralNominalCycleRegressions.nominal_len_K2⟩

theorem nest_len_no_completed_dictionary
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary exampleRoles))
    (resolved : Resolves (Local (boundary exampleRoles remaining) lenRegistry
      (initial GeneralNominalProgressObstruction.context nominalLenRoot)) nominalLenRoot tree) :
    ¬ Completed tree (.selected dictionary) :=
  cycle_prevents_completed remaining ((resolves_iff remaining tree).mp resolved)
    (Or.inl GeneralNominalCycleRegressions.nominal_len_K2)

/-- `len [loop 1]` uses the full safe/unique proof, not a not-K2-to-selection inference. -/
theorem wrapper_len_classifies
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary exampleRoles)) :
    Classify (boundary exampleRoles remaining) lenRegistry
      (initial GeneralNominalCycleWrapper.context lenRoot) lenRoot (.selected (.node 30 [])) := by
  have localRule : Local (boundary exampleRoles remaining) lenRegistry
      (initial GeneralNominalCycleWrapper.context lenRoot) lenRoot (.selected 30 []) :=
    (local_iff remaining (.selected 30 [])).mpr
    GeneralNominalCycleRegressions.wrapper_len_selected
  cases localRule with
  | selected safe unique => exact .selected safe unique .nil

/-- A completed finite dictionary for the off-cycle wrapper, at the concrete initial journal. -/
theorem wrapper_len_completed
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCycleBoundary.vocabulary exampleRoles)) :
    Resolves (Local (boundary exampleRoles remaining) lenRegistry
      (initial GeneralNominalCycleWrapper.context lenRoot)) lenRoot (.selected 30 []) ∧
      Completed (.selected 30 []) (.selected (.node 30 [])) := by
  exact ⟨.selected ((local_iff remaining _).mpr GeneralNominalCycleRegressions.wrapper_len_selected) .nil,
    .selected .nil⟩

end Regressions
end Yulang.GeneralNominalCycleDictionaryPolicy
