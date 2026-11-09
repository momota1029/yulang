import Yulang.CommonRoleGlobalChoices

/-! Associated models for one jointly supported branch certificate. This is a
reference diagnostic interpretation, not a language candidate-selection policy.
Observation, source annotations and the checked registry remain inputs.
An associated request with no Computed result contributes no equation; this is
not resolution success or totality. -/
namespace Yulang.CommonRoleGlobalChoiceEquations
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleGlobalChoices (Table Valid mask)

variable (registry : Registry) (root : SourceRequest n) (observation : State n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

def view (table : Table registry root)
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) : State n :=
  CommonRoleCorrelatedEquations.view registry root (mask registry root table) observation
    env roles wf annotations seed

/-- For every independently valid shared table, all and only the associated
outputs of its chosen entries constrain one common assignment. Sibling equations
are conjoined, but existence of a satisfying assignment is NOT asserted. -/
theorem view_exact (table : Table registry root) (valid : Valid registry root observation table)
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root observation env roles wf table annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [view, CommonRoleCorrelatedEquations.view_exact]
  constructor
  · rintro ⟨hs,he⟩
    refine ⟨hs,?_⟩
    intro r d chosen q hq head hh
    obtain ⟨hd,hp,hc⟩ := valid.1 r d chosen
    exact he r hp d hd ((CommonRoleGlobalChoices.mask_exact ..).mpr chosen) hc q hq head hh
  · rintro ⟨hs,he⟩
    refine ⟨hs,?_⟩
    intro r _ d _ hm _ q hq head hh
    exact he r d ((CommonRoleGlobalChoices.mask_exact ..).mp hm) q hq head hh

/-- The actual associated interpreter agrees with independent declaration
resolution; AssocWellFormed remains an explicit checked-environment premise. -/
theorem view_declarative_exact (awf : Roles.AssocWellFormed env roles)
    (table : Table registry root) (valid : Valid registry root observation table)
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (view registry root observation env roles wf table annotations seed).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
          Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [view_exact registry root observation env roles wf table valid]
  simp only [CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf]
/-- Finite reference family, retaining each globally correlated alternative. -/
def infer (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) : List (State n) :=
  (CommonRoleGlobalChoices.search registry root observation).map fun table =>
    view registry root observation env roles wf table annotations seed

/-- Soundness and completeness of the entire finite model family. No Valid
certificate is required as an external input: it is existentially enumerated.
This does not claim a model/certificate exists, or a language inference result. -/
theorem infer_models_exact
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    (∃ output ∈ infer registry root observation env roles wf annotations seed,
      All Common.model assignment output.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root, Valid registry root observation table ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  constructor
  · rintro ⟨output,member,models⟩
    obtain ⟨table,found,rfl⟩ := List.mem_map.mp member
    have valid := ((CommonRoleGlobalChoices.search_exact ..).mp found).2
    obtain ⟨hs,he⟩ := (view_exact registry root observation env roles wf table valid annotations seed assignment).mp models
    exact ⟨hs,table,valid,he⟩
  · rintro ⟨hs,table,valid,he⟩
    obtain ⟨found,same⟩ := CommonRoleGlobalChoices.complete registry root observation table valid
    let canonical := (CommonRoleGlobalChoices.choiceSpace registry root).filter table.contains
    have cv : Valid registry root observation canonical :=
      ((CommonRoleGlobalChoices.search_exact ..).mp found).2
    refine ⟨view registry root observation env roles wf canonical annotations seed,
      List.mem_map.mpr ⟨canonical,found,rfl⟩,?_⟩
    apply (view_exact registry root observation env roles wf canonical cv annotations seed assignment).mpr
    refine ⟨hs,?_⟩
    intro r d hc q hq head hh
    exact he r d ((same (r,d)).mp hc) q hq head hh

/-- The model-family iff with independently defined associated resolution. -/
theorem infer_declarative_models_exact (awf : Roles.AssocWellFormed env roles)
    (annotations : Route registry root → Declaration → List (Request n))
    (seed : State n) (assignment : Fin n → Comp Common.model) :
    (∃ output ∈ infer registry root observation env roles wf annotations seed,
      All Common.model assignment output.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root, Valid registry root observation table ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
          Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [infer_models_exact]
  simp only [CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf]

end Yulang.CommonRoleGlobalChoiceEquations
