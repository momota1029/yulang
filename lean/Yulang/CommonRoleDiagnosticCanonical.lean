import Yulang.CommonRoleDiagnosticTree

/-! Exact ordered diagnostic representation invariance. Registry and source
carrier enumeration remain fixed. This is not a language dictionary interpreter,
or invariance under reordering declarations or source obligations. -/
namespace Yulang.CommonRoleDiagnosticCanonical
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleMaterializedDomain
open CommonRoleCorrelatedPaths (Route)
open CommonRoleGlobalChoices (Table mask)
open CommonRoleSettledConstraints (State)
open CommonRoleGuardedEquations (Candidate candidate candidate_exact)
open CommonRoleDiagnosticTree (Tree build diagnose enabled)

variable (registry : Registry) (root : SourceRequest n)

/-- Equality of active evidence, independent of tree construction. -/
def ActiveEquivalent (a b : Table registry root) (s t : State n) : Prop :=
  ∀ r d, d ∈ registry.declarations →
    ((r,d) ∈ a ∧ Candidate s r.2.val d ↔ (r,d) ∈ b ∧ Candidate t r.2.val d)

theorem active_test_eq (a b : Table registry root) (s t : State n)
    (same : ActiveEquivalent registry root a b s t)
    (r : Route registry root) (d : Declaration) (hd : d ∈ registry.declarations) :
    (mask registry root a r.1 r.2 d && candidate s r.2.val d) =
      (mask registry root b r.1 r.2 d && candidate t r.2.val d) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, CommonRoleGlobalChoices.mask_exact, candidate_exact]
    using same r d hd

/-- Candidate order and repeated registry entries are preserved literally. -/
theorem enabled_eq (a b : Table registry root) (s t : State n)
    (same : ActiveEquivalent registry root a b s t) (r : Route registry root) :
    enabled registry root a s r = enabled registry root b t r := by
  apply List.filter_congr
  intro d hd
  exact active_test_eq registry root a b s t same r d hd

/-- Child list order and multiplicity, not just membership, agree. -/
theorem children_eq (a b : Table registry root) (s t : State n)
    (same : ActiveEquivalent registry root a b s t) (r : Route registry root) :
    CommonRoleCorrelatedPaths.children registry root (mask registry root a) s r =
      CommonRoleCorrelatedPaths.children registry root (mask registry root b) t r := by
  unfold CommonRoleCorrelatedPaths.children
  have flat_congr {α β : Type} (xs : List α) (f g : α → List β)
      (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
  apply flat_congr
  intro d hd
  rw [active_test_eq registry root a b s t same r d hd]

/-- Full structural equality holds for every budget and starting route. -/
theorem build_eq (a b : Table registry root) (s t : State n)
    (same : ActiveEquivalent registry root a b s t)
    (fuel : Nat) (r : Route registry root) :
    build registry root a s fuel r = build registry root b t fuel r := by
  induction fuel generalizing r with
  | zero => simp only [build, enabled_eq registry root a b s t same r]
  | succ k ih =>
    simp only [build, enabled_eq registry root a b s t same r,
      children_eq registry root a b s t same r]
    congr 1
    apply List.map_congr_left
    intro c _
    exact ih c

/-- No external depth or accessibility premise is required at the entry point. -/
theorem diagnose_eq (a b : Table registry root) (s t : State n)
    (same : ActiveEquivalent registry root a b s t) :
    diagnose registry root a s = diagnose registry root b t :=
  build_eq registry root a b s t same _ _

/-- Reordering and repeating table entries cannot change the ordered tree. -/
theorem diagnose_membership (a b : Table registry root) (s : State n)
    (same : ∀ p, p ∈ a ↔ p ∈ b) :
    diagnose registry root a s = diagnose registry root b s := by
  apply diagnose_eq
  intro r d _
  exact and_congr (same (r,d)) Iff.rfl

/-- Every valid certificate has an actually searched canonical representative
with the same complete ordered diagnostic tree. -/
theorem valid_canonical_tree (table : Table registry root) (s : State n)
    (valid : CommonRoleGlobalChoices.Valid registry root s table) :
    let canonical := CommonRoleStableGlobalChoices.canonical registry root table
    canonical ∈ CommonRoleGlobalChoices.search registry root s ∧
      diagnose registry root canonical s = diagnose registry root table s := by
  obtain ⟨found,same⟩ := CommonRoleGlobalChoices.complete registry root s table valid
  exact ⟨found,diagnose_membership registry root _ table s same⟩

/-- Ordinary atom permutation/duplication preserves endpoint materialization
when the common state has a model. The premise is needed because the detector
selects the first explicit scalar witness; inconsistent evidence is not unique. -/
theorem endpoint_atoms (s t : State n)
    (same : ∀ atom, atom ∈ s.atoms ↔ atom ∈ t.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment s.atoms)
    (e : Endpoint n) : e.eval s = e.eval t := by
  have mt : PresenceNormalForm.All Common.model assignment t.atoms := by
    intro atom ha
    exact models atom ((same atom).mpr ha)
  induction e with
  | fixed v => rfl
  | wrap c e ih => simp only [Endpoint.eval, ih]
  | slot i =>
    have eqv : CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.int ↔
        CommonRoleOrdinaryKnownness.materialize t.atoms i = some Roles.Examples.int :=
      ⟨materialized_int_persists s t i (fun a ha => (same a).mp ha) assignment mt,
       materialized_int_persists t s i (fun a ha => (same a).mpr ha) assignment models⟩
    simp only [Endpoint.eval, eqv]

/-- Ordinary atom representation invariance, at every source request. -/
theorem candidate_atoms (s t : State n)
    (same : ∀ atom, atom ∈ s.atoms ↔ atom ∈ t.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment s.atoms)
    (p : SourceRequest n) (d : Declaration) : Candidate s p d ↔ Candidate t p d := by
  simp only [Candidate, endpoint_atoms s t same assignment models]

/-- Simultaneous ordinary-atom and certificate reordering/duplication leaves
the whole ordered diagnostic tree literally equal, provided ordinary consistency.
This does not cover different atom sets with equal semantic model sets. -/
theorem diagnose_atoms (a b : Table registry root) (s t : State n)
    (tables : ∀ p, p ∈ a ↔ p ∈ b)
    (atoms : ∀ atom, atom ∈ s.atoms ↔ atom ∈ t.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment s.atoms) :
    diagnose registry root a s = diagnose registry root b t := by
  apply diagnose_eq
  intro r d _
  exact and_congr (tables (r,d)) (candidate_atoms s t atoms assignment models r.2.val d)

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
  (annotations : Route registry root → Declaration → List (CommonRoleAssociatedStateFlow.Request n))
  (seed : State n)

/-- The self-output state is also independent of table enumeration. -/
theorem output_membership (a b : Table registry root) (same : ∀ p, p ∈ a ↔ p ∈ b) :
    CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed a =
      CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed b := by
  simp only [CommonRoleStableGlobalChoices.output, CommonRoleStableGlobalChoices.requests,
    CommonRoleStableGlobalChoices.canonical_ext registry root a b same]

/-- The self-output tree is identical, not merely model-equivalent. -/
theorem self_tree_membership (a b : Table registry root) (same : ∀ p, p ∈ a ↔ p ∈ b) :
    diagnose registry root a (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed a) =
      diagnose registry root b (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed b) := by
  rw [output_membership registry root env roles wf annotations seed a b same]
  exact diagnose_membership registry root a b _ same

/-- Completeness strengthens canonical search membership to equality of the
whole ordered self-output tree. Existence of a stable certificate is a premise. -/
theorem stable_canonical_tree (table : Table registry root)
    (stable : CommonRoleStableGlobalChoices.Stable registry root env roles wf annotations seed table) :
    let canonical := CommonRoleStableGlobalChoices.canonical registry root table
    canonical ∈ CommonRoleStableGlobalChoices.search registry root env roles wf annotations seed ∧
      diagnose registry root canonical
          (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed canonical) =
        diagnose registry root table
          (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table) := by
  obtain ⟨found,same,_⟩ := CommonRoleStableGlobalChoices.complete registry root env roles wf annotations seed table stable
  exact ⟨found,self_tree_membership registry root env roles wf annotations seed _ table same⟩

end Yulang.CommonRoleDiagnosticCanonical
