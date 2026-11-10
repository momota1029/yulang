import Yulang.CommonRoleFiniteAssociatedDeclaration
import Yulang.CommonRoleSourceDescent

/-!
# Ordinary source identity and finite associated closure

Every occurrence of the same supplied source name shares its type, including
slots without scalar evidence. The finite table, occurrence templates and
checked first-order declarations remain inputs. This is an implementation
fragment, not a language restriction or a general dynamic B4 resolver.
-/
namespace Yulang.CommonRoleFiniteAssociatedSourceModels
open CommonRoleFiniteAssociatedClosure (Occurrence Source Fact)
open CommonRoleFiniteAssociatedDeclaration (DeclarativeDerives)
open CommonRoleSourceIdentity (Table Slot Coherent)
open CommonRoleSourceDescent (Factors)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def source (table : Table) (occurrences : List (Occurrence table.length)) :
    Source table.length := ⟨CommonRoleSourceIdentity.source table, occurrences⟩

/-- Add ordinary source equalities before running the existing finite closure.
The output retains all old type and effect constraints; only type identities
are added. Neither ordinary model existence nor a successful run is required. -/
def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (table : Table)
    (occurrences : List (Occurrence table.length)) (s : State table.length) :
    State table.length :=
  CommonRoleFiniteAssociatedModels.run env roles wf (source table occurrences)
    (CommonRoleSourceIdentity.extend table s)

/-- All ordinary assignments, explicit checked-declaration premises, and an
independent associated closure. Source coherence is a conclusion, not input. -/
theorem run_models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (table : Table) (occurrences : List (Occurrence table.length))
    (s : State table.length) (v : Slot table → Comp Common.model) :
    All Common.model v (run env roles wf table occurrences s).atoms ↔
      All Common.model v s.atoms ∧ Coherent table v ∧
        ∀ fact, DeclarativeDerives env roles (source table occurrences)
          (CommonRoleSourceIdentity.extend table s) fact →
          Common.Equivalent (v fact.1).1 (.base fact.2) := by
  unfold run
  rw [CommonRoleFiniteAssociatedModels.run_models_exact,
    CommonRoleSourceIdentity.extend_exact]
  simp only [CommonRoleFiniteAssociatedDeclaration.derives_exact env roles wf awf]
  exact and_assoc

/-- Every model descends to one valuation of the supplied source names.
No equality of effect rows, or meaning of names absent from the table, follows. -/
theorem source_factorization (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (table : Table)
    (occurrences : List (Occurrence table.length)) (s : State table.length)
    (v : Slot table → Comp Common.model)
    (model : All Common.model v (run env roles wf table occurrences s).atoms) :
    All Common.model v s.atoms ∧ ∃ sourceValues, Factors table v sourceValues := by
  obtain ⟨old, _⟩ := (CommonRoleFiniteAssociatedModels.run_models_exact
    env roles wf (source table occurrences) (CommonRoleSourceIdentity.extend table s) v).mp model
  obtain ⟨original, coherent⟩ := (CommonRoleSourceIdentity.extend_exact table s v).mp old
  exact ⟨original, (CommonRoleSourceDescent.factorization_exact table v).mp coherent⟩

/-- Soundness and completeness for all old states and all occurrence assignments.
One source valuation is existential in the conclusion, not a caller oracle.
Associated facts use the independent declaration judgment, not resolver output.
Finite source/template adequacy and full language principal typing remain open. -/
theorem run_source_models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (table : Table) (occurrences : List (Occurrence table.length))
    (s : State table.length) (v : Slot table → Comp Common.model) :
    All Common.model v (run env roles wf table occurrences s).atoms ↔
      All Common.model v s.atoms ∧ ∃ sourceValues, Factors table v sourceValues ∧
        ∀ fact, DeclarativeDerives env roles (source table occurrences)
          (CommonRoleSourceIdentity.extend table s) fact →
          Common.Equivalent (sourceValues (CommonRoleSourceIdentity.source table fact.1))
            (.base fact.2) := by
  rw [run_models_exact env roles wf awf]
  constructor
  · rintro ⟨old, coherent, equations⟩
    obtain ⟨values, factor⟩ := (CommonRoleSourceDescent.factorization_exact table v).mp coherent
    refine ⟨old, values, factor, ?_⟩
    intro fact derived
    exact Common.equivalent_trans (Common.equivalent_symm (factor fact.1)) (equations fact derived)
  · rintro ⟨old, values, factor, equations⟩
    refine ⟨old, CommonRoleSourceDescent.factors_coherent table v values factor, ?_⟩
    intro fact derived
    exact Common.equivalent_trans (factor fact.1) (equations fact derived)

/-- The actual ordinary solver accepts exactly the shared-source models of
this finite closure. No successful-run, model, fuel or frontier premise occurs. -/
theorem solver_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (table : Table) (occurrences : List (Occurrence table.length)) (s : State table.length) :
    CommonRoleOpenPropagation.consistent (run env roles wf table occurrences s) = true ↔
      ∃ v : Slot table → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ sourceValues, Factors table v sourceValues ∧
          ∀ fact, DeclarativeDerives env roles (source table occurrences)
            (CommonRoleSourceIdentity.extend table s) fact →
            Common.Equivalent (sourceValues (CommonRoleSourceIdentity.source table fact.1))
              (.base fact.2) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_models_exact env roles wf awf table occurrences s)

end Yulang.CommonRoleFiniteAssociatedSourceModels
