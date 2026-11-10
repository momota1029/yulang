import Yulang.CommonRoleNamedAssociatedGraph
import Yulang.CommonRoleFiniteAssociatedSourceModels

/-!
# Computed named allocation and independent source-name derivations

The finite named occurrence list supplies source names and goal templates.
This entry computes its table and every receiver/output slot, adds ordinary
source equalities, and relates its result to derivations on source names.
Names are already scope-resolved inputs; template adequacy and dynamic where
construction are not established here. This is an implementation fragment,
not a language restriction or the full B4 classification theorem.
-/
namespace Yulang.CommonRoleNamedAssociatedSourceModels
open CommonRoleNamedAssociatedGraph (Program table tableSlot)
open CommonRoleFiniteAssociatedClosure (Occurrence Source Fact)
open CommonRoleFiniteAssociatedDeclaration (DeclarativeDerives)
open CommonRoleSourceIdentity (Slot)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev receiver (p : Program) (i : Fin p.length) : Slot (table p) :=
  tableSlot p (CommonRoleNamedAssociatedGraph.receiver p i)

abbrev output (p : Program) (i : Fin p.length) : Slot (table p) :=
  tableSlot p (CommonRoleNamedAssociatedGraph.output p i)

theorem receiver_source (p : Program) (i : Fin p.length) :
    CommonRoleSourceIdentity.source (table p) (receiver p i) = p[i.val].receiver := by
  rw [CommonRoleNamedAssociatedGraph.table_source,
    CommonRoleNamedAssociatedGraph.receiver_identity]

theorem output_source (p : Program) (i : Fin p.length) :
    CommonRoleSourceIdentity.source (table p) (output p i) = p[i.val].output := by
  rw [CommonRoleNamedAssociatedGraph.table_source,
    CommonRoleNamedAssociatedGraph.output_identity]

def occurrence (p : Program) (i : Fin p.length) : Occurrence (table p).length :=
  ⟨receiver p i, output p i, p[i.val].name, p[i.val].template⟩

def occurrences (p : Program) : List (Occurrence (table p).length) :=
  (List.finRange p.length).map (occurrence p)

def source (p : Program) : Source (table p).length :=
  CommonRoleFiniteAssociatedSourceModels.source (table p) (occurrences p)

def prepared (p : Program) (s : State (table p).length) : State (table p).length :=
  CommonRoleSourceIdentity.extend (table p) s

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Program) (s : State (table p).length) :=
  CommonRoleFiniteAssociatedSourceModels.run env roles wf (table p) (occurrences p) s

/-- Adding variable-to-variable identities never invents explicit scalar
seed pairs. This is syntactic knownness, not general semantic entailment. -/
theorem prepared_evidence (p : Program) (s : State (table p).length)
    (slot : Slot (table p)) (head : Inference.Base) :
    Evidence (prepared p s).atoms slot head ↔ Evidence s.atoms slot head := by
  simp only [prepared, CommonRoleSourceIdentity.extend, Evidence, List.mem_append,
    CommonRoleSourceIdentity.mem_atoms]
  simp [CommonRoleSourceIdentity.pairAtoms]

/-- Seed evidence is the only ordinary-state interface. Slot positions and
source identities are computed, not separate caller maps. -/
def Seed (p : Program) (s : State (table p).length) (name : Nat)
    (head : Inference.Base) : Prop :=
  ∃ slot : Slot (table p), CommonRoleSourceIdentity.source (table p) slot = name ∧
    Evidence s.atoms slot head

/-- The independent associated declaration judgment, without an allocated
output slot or calls to the executable associated resolver. -/
def Associated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (q : CommonRoleNamedAssociatedGraph.NamedOccurrence)
    (head result : Inference.Base) : Prop :=
  Roles.argsBound (q.template head).args = 0 ∧
    RoleConstraints.Resolves env.cores (q.template head) ∧
      ∃ rhs, Roles.AssocDerives env roles (q.template head) q.name rhs ∧
        CommonRoleAssociatedStateFlow.scalar rhs = some result

/-- Independent derivations are on original names. Shared-name propagation
requires no special rule: equal names denote the same judgment. -/
inductive NamedDerives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) : Nat → Inference.Base → Prop
  | initial {name head} : Seed p s name head → NamedDerives env roles p s name head
  | associated (i : Fin p.length) {head result} :
      NamedDerives env roles p s p[i.val].receiver head →
      Associated env roles p[i.val] head result →
      NamedDerives env roles p s p[i.val].output result

/-- Soundness of the computed allocation against source-name derivations. -/
theorem allocated_to_named (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (fact : Fact (table p).length)
    (derived : DeclarativeDerives env roles (source p) (prepared p s) fact) :
    NamedDerives env roles p s (CommonRoleSourceIdentity.source (table p) fact.1) fact.2 := by
  induction derived with
  | initial evidence => exact .initial ⟨_, rfl, (prepared_evidence p s _ _).mp evidence⟩
  | @identity origin target head same _ ih =>
    change CommonRoleSourceIdentity.source (table p) origin =
      CommonRoleSourceIdentity.source (table p) target at same
    simpa only [same] using ih
  | @associated q head result member _ computed ih =>
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    have step : NamedDerives env roles p s p[i.val].output result :=
      .associated i (by simpa only [occurrence, receiver_source] using ih) computed
    simpa only [occurrence, output_source] using step

/-- Completeness: any represented occurrence of a derived name receives the
same fact. No source sharing map or precomputed frontier is a premise. -/
theorem named_to_allocated (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (name : Nat) (head : Inference.Base)
    (derived : NamedDerives env roles p s name head) :
    ∀ slot : Slot (table p), CommonRoleSourceIdentity.source (table p) slot = name →
      DeclarativeDerives env roles (source p) (prepared p s) (slot, head) := by
  induction derived with
  | initial seed =>
    obtain ⟨origin, same, evidence⟩ := seed
    intro slot target
    exact .identity (same.trans target.symm)
      (.initial ((prepared_evidence p s _ _).mpr evidence))
  | @associated i head result _ computed ih =>
    intro slot target
    have recv := ih (receiver p i) (receiver_source p i)
    have step : DeclarativeDerives env roles (source p) (prepared p s)
        (output p i, result) :=
      .associated (q := occurrence p i) (List.mem_map.mpr ⟨i, by simp, rfl⟩) recv computed
    exact .identity ((output_source p i).trans target.symm) step

/-- The allocation introduces neither missing nor extra name-level facts. -/
theorem allocated_named_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (fact : Fact (table p).length) :
    DeclarativeDerives env roles (source p) (prepared p s) fact ↔
      NamedDerives env roles p s (CommonRoleSourceIdentity.source (table p) fact.1) fact.2 :=
  ⟨allocated_to_named env roles p s fact,
    fun h => named_to_allocated env roles p s _ _ h fact.1 rfl⟩

/-- Derived names have a real source occurrence, even in cyclic or empty
programs. No equation is imposed on a name absent from the computed table. -/
theorem named_support (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Program) (s : State (table p).length) (name : Nat) (head : Inference.Base)
    (derived : NamedDerives env roles p s name head) :
    ∃ slot : Slot (table p), CommonRoleSourceIdentity.source (table p) slot = name := by
  cases derived with
  | initial seed => obtain ⟨slot, same, _⟩ := seed; exact ⟨slot, same⟩
  | associated i _ _ => exact ⟨output p i, output_source p i⟩

/-- The concrete scalar detector after execution sees exactly the independent
facts on source names, for every allocated position and scalar head. -/
theorem run_evidence_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (slot : Slot (table p))
    (head : Inference.Base) :
    Evidence (run env roles wf p s).atoms slot head ↔
      NamedDerives env roles p s (CommonRoleSourceIdentity.source (table p) slot) head :=
  (CommonRoleFiniteAssociatedDeclaration.run_declaration_exact
    env roles wf awf (source p) (prepared p s) slot head).trans
      (allocated_named_exact env roles p s (slot, head))

/-- Soundness and completeness for all finite named programs, all old ordinary
states, and every assignment. Only checked first-order declarations are assumed.
One source valuation is a conclusion, and all its facts use independent named
derivations. Templates and source scoping remain explicit input boundaries. -/
theorem run_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (v : Slot (table p) → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
        ∀ name head, NamedDerives env roles p s name head →
          Common.Equivalent (values name) (.base head) := by
  rw [run, CommonRoleFiniteAssociatedSourceModels.run_source_models_exact env roles wf awf]
  apply and_congr_right
  intro _
  apply exists_congr
  intro values
  apply and_congr_right
  intro _
  constructor
  · intro equations name head derived
    obtain ⟨slot, same⟩ := named_support env roles p s name head derived
    have result := equations (slot, head)
      (named_to_allocated env roles p s name head derived slot same)
    simpa only [same] using result
  · intro equations fact derived
    exact equations _ _ (allocated_to_named env roles p s fact derived)

/-- The actual ordinary solver accepts exactly a model with one valuation of
source names and all independent named facts. No success, fuel, model, or
complete finite-domain premise is supplied by the caller. -/
theorem solver_source_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) :
    CommonRoleOpenPropagation.consistent (run env roles wf p s) = true ↔
      ∃ v : Slot (table p) → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ values,
          CommonRoleSourceDescent.Factors (table p) v values ∧
            ∀ name head, NamedDerives env roles p s name head →
              Common.Equivalent (values name) (.base head) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_exact env roles wf awf p s)

end Yulang.CommonRoleNamedAssociatedSourceModels
