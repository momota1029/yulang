import Yulang.CommonRoleAssociatedStateFlow

/-!
# Associated values and independent declaration derivations

The reverse bridge does not assume the returned value already has a declarative
proof. Full iff uses the existing association well-formedness check explicitly.
This remains the first-order Roles carrier, not the general interval/source B4.
-/
namespace Yulang.CommonRoleAssociatedDeclarationExact
open Roles

/-- Soundness: any actual associated result yields the independent declaration
judgment, for every checked core registry. No extra associated well-formedness
is needed in this direction; the derivation uses the selected actual body. -/
theorem assocOf_sound (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (g : Goal) (name : Nat) (result : Term)
    (returned : assocOf env roles wf g name = some result) :
    AssocDerives env roles g name result := by
  have resolved : resolve env.cores wf g = .resolved := by
    by_cases yes : resolve env.cores wf g = .resolved
    · exact yes
    · simp [assocOf, yes] at returned
  obtain ⟨i, member, selected, hm⟩ := assoc_selected_of_resolved env wf g resolved
  have value : assocValue i (roles g.role) g name = some result := by
    rw [assoc_independent_of_constraints env roles wf g name resolved i member selected] at returned
    exact returned
  have children : ∀ c ∈ i.impl.constraints,
      Derives env.cores (c.subst (matchingSubst i.impl.head g.args)) := by
    obtain ⟨core, singleton, resolvedChildren⟩ := (resolve_resolved_iff env.cores wf g).mp resolved
    have same : core = i.impl := by
      rw [selected] at singleton
      exact (List.singleton_inj.mp singleton).symm
    subst core
    intro c present
    exact resolve_sound env.cores wf _ (resolvedChildren c present)
  cases body : i.assoc.lookup name with
  | some rhs =>
      have same : rhs.subst (matchingSubst i.impl.head g.args) = result := by
        simpa only [assocValue, body, Option.some.injEq] using value
      rw [← same]
      exact .explicit i (matchingSubst i.impl.head g.args) member hm.1
        (matched_head hm) children rhs body
  | none =>
      cases declaration : (roles g.role).assoc name with
      | none => simp [assocValue, body, declaration] at value
      | some default =>
          cases default with
          | none => simp [assocValue, body, declaration] at value
          | some rhs =>
              have same : rhs.subst (defaultSubst g.args) = result := by
                simpa only [assocValue, body, declaration, Option.join_some,
                  Option.map_some, Option.some.injEq] using value
              rw [← same]
              exact .default i (matchingSubst i.impl.head g.args) member hm.1
                (matched_head hm) children rhs body declaration

/-- Soundness and completeness, including independent resolution uniqueness.
The existing `AssocWellFormed` premise is explicit and is used for agreement
of arbitrary matching substitutions and source-scoped associated bodies. -/
theorem assocOf_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (result : Term) :
    assocOf env roles wf g name = some result ↔
      RoleConstraints.Resolves env.cores g ∧ AssocDerives env roles g name result := by
  constructor
  · intro returned
    have resolved : resolve env.cores wf g = .resolved := by
      by_cases yes : resolve env.cores wf g = .resolved
      · exact yes
      · simp [assocOf, yes] at returned
    exact ⟨(RoleConstraints.resolve_exact env.cores wf g).mp resolved,
      assocOf_sound env roles wf g name result returned⟩
  · rintro ⟨resolved, derived⟩
    exact assoc_derivation_agrees env roles wf awf g name
      ((RoleConstraints.resolve_exact env.cores wf g).mpr resolved) derived

/-- Independent scalar-associated judgment. Neither `assocOf`, `resolve`,
`value`, nor the finite Horn saturation occurs in this definition. -/
def DeclarativeComputed (env : AssocEnv) (roles : RoleDecls)
    (q : CommonRoleAssociatedStateFlow.Request n) (head : Inference.Base) : Prop :=
  argsBound q.receiver.args = 0 ∧ RoleConstraints.Resolves env.cores q.receiver ∧
    ∃ rhs, AssocDerives env roles q.receiver q.name rhs ∧
      CommonRoleAssociatedStateFlow.scalar rhs = some head

/-- Soundness and completeness of the scalar adapter against independent
associated derivations. The known receiver, no-overlap resolution, and actual
associated RHS are conclusions/parts of the judgment, not successful-run
premises. Association well-formedness remains explicit. -/
theorem computed_iff_declarative (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (q : CommonRoleAssociatedStateFlow.Request n) (head : Inference.Base) :
    CommonRoleAssociatedStateFlow.Computed env roles wf q head ↔
      DeclarativeComputed env roles q head := by
  constructor
  · rintro ⟨known, rhs, computed, decoded⟩
    obtain ⟨resolved, derived⟩ := (assocOf_exact env roles wf awf q.receiver q.name rhs).mp computed
    exact ⟨known, resolved, rhs, derived, decoded⟩
  · rintro ⟨known, resolved, rhs, derived, decoded⟩
    exact ⟨known, rhs,
      (assocOf_exact env roles wf awf q.receiver q.name rhs).mpr ⟨resolved, derived⟩,
      decoded⟩

end Yulang.CommonRoleAssociatedDeclarationExact
