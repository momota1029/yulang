import Yulang.CommonRolePathDecomposition
import Yulang.CommonRoleRecursiveFilteredInference

/-! Structural decomposition exposes payload variables to the existing path
refutation checker. Original states are retained; no language classification
or full satisfiability decision is asserted. -/
namespace Yulang.CommonRoleDecomposedInference
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)

def check (atoms : List (Atom (Fin n))) : Bool :=
  CommonRoleRecursivePaths.check (CommonRolePathDecomposition.normalize atoms)

def Certificate (atoms : List (Atom (Fin n))) : Prop :=
  CommonRoleRecursivePaths.AnyCertificate
    (CommonRolePathDecomposition.normalize atoms)

theorem check_exact (atoms : List (Atom (Fin n))) : check atoms = true ↔ Certificate atoms :=
  CommonRoleRecursivePaths.check_all_exact _

theorem checked_no_model (atoms : List (Atom (Fin n))) (h : check atoms = true)
    (a : Fin n → Comp Common.model) : ¬ All Common.model a atoms := by
  intro hm
  exact CommonRoleRecursivePaths.checked_no_model_all _ h a
    ((CommonRolePathDecomposition.normalize_exact atoms a).mpr hm)

def prune (states : List (State n)) : List (State n) := states.filter fun s => !check s.atoms

theorem prune_models (states : List (State n)) (a : Fin n → Comp Common.model) :
    (∃ s ∈ prune states, All Common.model a s.atoms) ↔
      ∃ s ∈ states, All Common.model a s.atoms := by
  constructor
  · rintro ⟨s,hs,hm⟩
    exact ⟨s,(List.mem_filter.mp hs).1,hm⟩
  · rintro ⟨s,hs,hm⟩
    refine ⟨s,List.mem_filter.mpr ⟨hs,?_⟩,hm⟩
    cases hc : check s.atoms
    · rfl
    · exact False.elim (checked_no_model s.atoms hc a hm)

open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleGlobalChoices (Table)
variable (registry : Registry) (root : SourceRequest n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n)) (seed : State n)

def infer : List (State n) :=
  prune (CommonRoleRecursiveFilteredInference.infer registry root env roles wf annotations seed)

theorem infer_models_preserved (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    ∃ out ∈ CommonRoleRecursiveFilteredInference.infer registry root env roles wf annotations seed,
      All Common.model a out.atoms := prune_models _ a

theorem infer_models_exact (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    All Common.model a seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleDirectedGlobalChoices.Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (a q.output).1 (.base head) := by
  rw [infer_models_preserved, CommonRoleRecursiveFilteredInference.infer_models_exact]

theorem empty_excludes_original_model
    (empty : infer registry root env roles wf annotations seed = [])
    (a : Fin n → Comp Common.model) :
    ¬ ∃ out ∈ CommonRoleRecursiveFilteredInference.infer registry root env roles wf annotations seed,
      All Common.model a out.atoms := by
  intro h
  obtain ⟨out,ho,_⟩ := (infer_models_preserved registry root env roles wf annotations seed a).mpr h
  simp [empty] at ho
end Yulang.CommonRoleDecomposedInference
