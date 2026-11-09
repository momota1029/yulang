import Yulang.CommonRoleRecursivePaths
import Yulang.CommonRolePathFilteredInference

/-! Recursive structural pruning after directed path pruning, preserving the
whole diagnostic model family. No language classification is added. -/
namespace Yulang.CommonRoleRecursiveFilteredInference
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleGlobalChoices (Table)
variable (registry : Registry) (root : SourceRequest n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n)) (seed : State n)

def infer : List (State n) :=
  CommonRoleRecursivePaths.prune
    (CommonRolePathFilteredInference.infer registry root env roles wf annotations seed)

theorem infer_models_preserved (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    ∃ out ∈ CommonRolePathFilteredInference.infer registry root env roles wf annotations seed,
      All Common.model a out.atoms := CommonRoleRecursivePaths.prune_models _ a

theorem infer_models_exact (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    All Common.model a seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleDirectedGlobalChoices.Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (a q.output).1 (.base head) := by
  rw [infer_models_preserved, CommonRolePathFilteredInference.infer_models_exact]

theorem empty_excludes_stable_model
    (empty : infer registry root env roles wf annotations seed = [])
    (table : Table registry root)
    (stable : CommonRoleDirectedGlobalChoices.Stable registry root env roles wf annotations seed table)
    (a : Fin n → Comp Common.model) :
    ¬ All Common.model a
      (CommonRoleDirectedGlobalChoices.output registry root env roles wf annotations seed table).atoms := by
  intro hm
  obtain ⟨found,_,eq⟩ := CommonRoleDirectedGlobalChoices.complete
    registry root env roles wf annotations seed table stable
  have original : ∃ out ∈ CommonRoleDirectedGlobalChoices.infer registry root env roles wf annotations seed,
      All Common.model a out.atoms :=
    ⟨_, List.mem_map.mpr ⟨_,found,eq⟩,hm⟩
  have scalar0 := (CommonRoleConflictFilteredInference.infer_models_preserved
    registry root env roles wf annotations seed a).mpr original
  have scalar := (CommonRoleStructuralFilteredInference.infer_models_preserved
    registry root env roles wf annotations seed a).mpr scalar0
  have path := (CommonRolePathFilteredInference.infer_models_preserved
    registry root env roles wf annotations seed a).mpr scalar
  obtain ⟨out,hout,_⟩ := (infer_models_preserved registry root env roles wf annotations seed a).mpr path
  simp [empty] at hout
end Yulang.CommonRoleRecursiveFilteredInference
