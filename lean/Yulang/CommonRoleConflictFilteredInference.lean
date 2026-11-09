import Yulang.CommonRoleDirectedConflicts
import Yulang.CommonRoleDirectedGlobalChoices

/-! Conflict pruning preserves the complete model family of the diagnostic search.
Passing the check does not certify existence of a model or a language decision. -/
namespace Yulang.CommonRoleConflictFilteredInference
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Remove only states with a checked scalar contradiction. -/
def prune (states : List (State n)) : List (State n) :=
  states.filter fun s => !CommonRoleDirectedConflicts.check s

theorem prune_exact (states : List (State n)) (s : State n) :
    s ∈ prune states ↔ s ∈ states ∧ ¬ CommonRoleDirectedConflicts.Conflict s := by
  have exact := CommonRoleDirectedConflicts.check_exact s
  cases h : CommonRoleDirectedConflicts.check s <;> simp_all [prune]

theorem prune_models (states : List (State n)) (a : Fin n → Comp Common.model) :
    (∃ s ∈ prune states, All Common.model a s.atoms) ↔
      ∃ s ∈ states, All Common.model a s.atoms := by
  constructor
  · rintro ⟨s,hs,hm⟩
    exact ⟨s,((prune_exact ..).mp hs).1,hm⟩
  · rintro ⟨s,hs,hm⟩
    refine ⟨s,(prune_exact ..).mpr ⟨hs,?_⟩,hm⟩
    intro conflict
    exact CommonRoleDirectedConflicts.conflict_no_model s conflict a hm

theorem pruned_no_models (states : List (State n)) (empty : prune states = []) :
    ¬ ∃ s ∈ states, ∃ a : Fin n → Comp Common.model, All Common.model a s.atoms := by
  rintro ⟨s,hs,a,hm⟩
  obtain ⟨t,ht,_⟩ := (prune_models states a).mpr ⟨s,hs,hm⟩
  simp [empty] at ht

open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleGlobalChoices (Table)
variable (registry : Registry) (root : SourceRequest n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n)) (seed : State n)

def infer : List (State n) :=
  prune (CommonRoleDirectedGlobalChoices.infer registry root env roles wf annotations seed)

/-- No ordinary model is lost by rejecting a certified scalar conflict. -/
theorem infer_models_preserved (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    ∃ out ∈ CommonRoleDirectedGlobalChoices.infer registry root env roles wf annotations seed,
      All Common.model a out.atoms := prune_models _ a

theorem infer_models_exact (a : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model a out.atoms) ↔
    All Common.model a seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleDirectedGlobalChoices.Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (a q.output).1 (.base head) := by
  rw [infer_models_preserved, CommonRoleDirectedGlobalChoices.infer_models_exact]

/-- Empty certified search implies no model of any stable table, not a language
rejected classification and not the converse of this implication. -/
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
  obtain ⟨out,hout,_⟩ := (infer_models_preserved registry root env roles wf annotations seed a).mpr original
  simp [empty] at hout
end Yulang.CommonRoleConflictFilteredInference
