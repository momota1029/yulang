import Yulang.CommonRoleStableGlobalChoices

/-! Exact model family for total associated certificates at their own output.
This removes the externally supplied observation and explicitly checks resolution
of every selected annotation. It does not construct a language saturation driver.
The diagnostic family may be empty; no existence or principal solution is claimed. -/
namespace Yulang.CommonRoleStableGlobalModels
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route Path extend)
open CommonRoleSourceWorklist (Node)
open CommonRoleAssociatedStateFlow (Request Computed)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleGlobalChoices (Table)
open CommonRoleStableGlobalChoices (output requests Stable search)

variable (registry : Registry) (root : SourceRequest n)
  (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (Request n)) (seed : State n)

/-- All chosen equations are conjoined, and each chosen request really resolves.
This is a two-sided model statement, not a satisfiability/existence assertion. -/
theorem output_models (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (output registry root env roles wf annotations seed table).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [output, CommonRoleAssociatedBatch.run_models]
  apply and_congr Iff.rfl
  constructor
  · intro h r d chosen q hq head hh
    obtain ⟨hd,hp,_⟩ := stable.1.1 r d chosen
    apply h q _ head hh
    exact (CommonRoleStableGlobalChoices.requests_exact registry root annotations table q).mpr
      ⟨r,d,(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,chosen,hq⟩
  · intro h q hq head hh
    obtain ⟨r,d,_,chosen,hann⟩ :=
      (CommonRoleStableGlobalChoices.requests_exact registry root annotations table q).mp hq
    exact h r d chosen q hann head hh

/-- Recomputing the guarded view at the output retains exactly the direct
batch's models: no chosen equation is supported only by an obsolete observation.
This is semantic equality for this certificate, not structural driver stability. -/
theorem supported_view_models (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment
      (CommonRoleGlobalChoiceEquations.view registry root
        (output registry root env roles wf annotations seed table)
        env roles wf table annotations seed).atoms ↔
      All Common.model assignment (output registry root env roles wf annotations seed table).atoms := by
  rw [CommonRoleGlobalChoiceEquations.view_exact registry root _ env roles wf table stable.1,
    output_models registry root env roles wf annotations seed table stable]

/-- Equivalent independent certificate: validation at one's own output, plus
actual resolution of each annotation. No request is hidden by an implication. -/
theorem stable_declarative (awf : Roles.AssocWellFormed env roles)
    (table : Table registry root) :
    Stable registry root env roles wf annotations seed table ↔
      CommonRoleGlobalChoices.Valid registry root
        (output registry root env roles wf annotations seed table) table ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head := by
  constructor
  · intro st
    refine ⟨st.1,?_⟩
    intro r d chosen q hq
    obtain ⟨hd,hp,_⟩ := st.1.1 r d chosen
    have member := (CommonRoleStableGlobalChoices.requests_exact registry root annotations table q).mpr
      ⟨r,d,(CommonRoleGlobalChoices.universe_exact registry root r d).mpr
        ⟨CommonRoleCorrelatedCarrier.path_retained registry root _ _ r hp,hd⟩,chosen,hq⟩
    obtain ⟨head,hhead⟩ := st.2 q member
    exact ⟨head,(CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf q head).mp hhead⟩
  · rintro ⟨hv,hr⟩
    refine ⟨hv,?_⟩
    intro q hq
    obtain ⟨r,d,_,chosen,hann⟩ :=
      (CommonRoleStableGlobalChoices.requests_exact registry root annotations table q).mp hq
    obtain ⟨head,hh⟩ := hr r d chosen q hann
    exact ⟨head,(CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf q head).mpr hh⟩

/-- Every selected parent's children are revalidated at the equations generated
by the SAME global table, rather than an older external observation. -/
theorem siblings_at_output (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table)
    (c : Node registry root)
    (child : c.val ∈ CommonRoleSourceTemplateClosure.declarationChildren d r.2.val) :
    Path registry root (CommonRoleGlobalChoices.mask registry root table)
      (output registry root env roles wf annotations seed table) (extend registry root r d c) ∧
      ∃ e, (extend registry root r d c,e) ∈ table := by
  exact CommonRoleGlobalChoices.siblings_closed registry root _ table
    (((CommonRoleStableGlobalChoices.search_exact ..).mp found).2.1) r d chosen c child

def infer : List (State n) :=
  (search registry root env roles wf annotations seed).map
    (output registry root env roles wf annotations seed)

/-- Soundness and completeness against ALL stable tables, not just a supplied
candidate or observation. Canonicalization preserves their exact output state. -/
theorem infer_models_exact (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head) := by
  constructor
  · rintro ⟨out,hm,hmodels⟩
    obtain ⟨table,found,rfl⟩ := List.mem_map.mp hm
    have st := ((CommonRoleStableGlobalChoices.search_exact ..).mp found).2
    obtain ⟨hs,he⟩ := (output_models registry root env roles wf annotations seed table st assignment).mp hmodels
    exact ⟨hs,table,st,he⟩
  · rintro ⟨hs,table,st,he⟩
    obtain ⟨found,_,out_eq⟩ := CommonRoleStableGlobalChoices.complete registry root env roles wf annotations seed table st
    refine ⟨output registry root env roles wf annotations seed table,?_,?_⟩
    · exact List.mem_map.mpr ⟨_,found,out_eq⟩
    · exact (output_models registry root env roles wf annotations seed table st assignment).mpr ⟨hs,he⟩

/-- Independent declaration version, including resolution success rather than
silently dropping unresolved requests. Core and associated wellformedness are
explicit premises; source annotations and first-order receivers remain inputs. -/
theorem infer_declarative_models_exact (awf : Roles.AssocWellFormed env roles)
    (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleGlobalChoices.Valid registry root
          (output registry root env roles wf annotations seed table) table ∧
        (∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head) ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
            Common.Equivalent (assignment q.output).1 (.base head) := by
  rw [infer_models_exact]
  simp only [stable_declarative registry root env roles wf annotations seed awf,
    CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf, and_assoc]

end Yulang.CommonRoleStableGlobalModels
