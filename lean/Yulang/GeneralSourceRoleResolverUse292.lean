import Yulang.GeneralSourceRoleAssocRead292
import Yulang.GeneralSourceRoleSyntaxPipeline292

/-! A direct link to the existing first-order association reader. These
lemmas do not select impls or connect the Rust parser to this resolver. -/
namespace Yulang.GeneralSourceRoleResolverUse292
open GeneralSourceRoleSpelling292 (Environment Position position_lt ResolvedBody)
open GeneralSourceRoleSyntaxBoundary292 (Admitted Owner Shell)
open GeneralSourceRoleSyntaxPipeline292 (applyShells default_from_shells)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Yulang.Roles

def ShellDefault (frontend : Environment) (shells : List Shell)
    (r n : Nat) (rhs : Term) : Prop :=
    ∃ s ∈ shells, frontend.role s.name = some r ∧
        ∃ el ∈ s.directTypeChildren, ∃ o, Admitted .roleBodyDirect el o ∧
          frontend.output r o.spelling = some n ∧ ResolvedBody frontend s.parameters o.body (some rhs)

theorem omitted_value_exact {frontend : Environment} {arity : Nat} {source : List Shell}
    {out : RoleSource} (built : applyShells frontend arity source = some out)
    (impl : AssocImpl) (goal : Goal) (name : Nat) (omitted : impl.assoc.lookup name = none)
    (value : Term) :
    assocValue impl (roleTable out goal.role) goal name = some value ↔
      ∃ rhs, ShellDefault frontend source goal.role name rhs ∧
        rhs.subst (defaultSubst goal.args) = value := by
  have exactDefault := default_from_shells frontend arity source out built goal.role name
  unfold assocValue
  rw [omitted]
  constructor
  · intro h
    cases read : (roleTable out goal.role).assoc name with
    | none => simp [read,Option.join] at h
    | some slot =>
      cases slot with
      | none => simp [read,Option.join] at h
      | some rhs =>
        have instantiated : rhs.subst (defaultSubst goal.args) = value := by
          simpa [read,Option.join] using h
        exact ⟨rhs,(exactDefault rhs).mp read,instantiated⟩
  · rintro ⟨rhs,witness,rfl⟩
    rw [(exactDefault rhs).mpr witness]
    rfl

theorem selected_omitted_exact {frontend : Environment} {arity : Nat} {source : List Shell}
    {out : RoleSource} (built : applyShells frontend arity source = some out)
    (env : AssocEnv) (wf : WellFormed env.cores) (goal : Goal) (name : Nat)
    (resolved : resolve env.cores wf goal = .resolved)
    (impl : AssocImpl) (member : impl ∈ env.impls) (selected : candidates env.cores goal = [impl.impl])
    (omitted : impl.assoc.lookup name = none) (value : Term) :
    assocOf env (roleTable out) wf goal name = some value ↔
      ∃ rhs, ShellDefault frontend source goal.role name rhs ∧ rhs.subst (defaultSubst goal.args) = value := by
  rw [assoc_independent_of_constraints env (roleTable out) wf goal name resolved impl member selected]
  exact omitted_value_exact built impl goal name omitted value

theorem selected_explicit_independent (out : RoleSource) (env : AssocEnv)
    (wf : WellFormed env.cores) (goal : Goal) (name : Nat)
    (resolved : resolve env.cores wf goal = .resolved) (impl : AssocImpl)
    (member : impl ∈ env.impls) (selected : candidates env.cores goal = [impl.impl])
    (rhs : Term) (explicit : impl.assoc.lookup name = some rhs) :
    assocOf env (roleTable out) wf goal name =
      some (rhs.subst (matchingSubst impl.impl.head goal.args)) := by
  rw [assoc_independent_of_constraints env (roleTable out) wf goal name resolved impl member selected]
  simp [assocValue,explicit]

theorem supplied_positional {spelling : String} {binders : List String} {slot : Nat}
    (pos : Position spelling binders slot) (args : List Term)
    (arity : args.length = binders.length) :
    ∃ arg, args[slot]? = some arg ∧ (.var slot : Term).subst (defaultSubst args) = arg := by
  have fits := position_lt pos
  rw [← arity] at fits
  let arg := args[slot]
  have found : args[slot]? = some arg := List.getElem?_eq_getElem fits
  exact ⟨arg,found,by simp [Term.subst,defaultSubst,found]⟩

end Yulang.GeneralSourceRoleResolverUse292
