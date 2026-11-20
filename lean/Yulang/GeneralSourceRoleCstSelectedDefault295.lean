import Yulang.GeneralSourceRoleCstSelectedReadback295

/-! Reach the current association reader only under its unchanged
well-formedness and independent successful selected-implementation claims. -/
namespace Yulang.GeneralSourceRoleCstSelectedDefault295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile)
open GeneralSourceRoleCstSelectedReadback295 (AnchoredAssoc exact_for_entry)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles

theorem old_read_omitted_exact {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (built : compile policy scope w brand a sealed env fallback = some table)
    (impls : AssocEnv) (wf : WellFormed impls.cores) (goal : Goal) (name : Nat)
    (success : resolve impls.cores wf goal = .resolved) (impl : AssocImpl)
    (present : impl ∈ impls.impls) (selected : candidates impls.cores goal = [impl.impl])
    (omitted : impl.assoc.lookup name = none) (value : Term) :
    ∃ entry, entry.atRole = a ∧ a = sealed.selected.address ∧
      (assocOf impls (roleTable table) wf goal name = some value ↔
        ∃ body, AnchoredAssoc w env entry a goal.role name (some body) ∧
          body.subst (defaultSubst goal.args) = value) := by
  have common := GeneralSourceRoleCstSelectedCompile295.compile_origin
    policy scope w brand a sealed env fallback table built
  obtain ⟨_,correct,entry,site,go,tab⟩ := common
  refine ⟨entry,site,correct,?_⟩
  have read (rhs : Option Term) :
      (roleTable table goal.role).assoc name = some rhs ↔
        AnchoredAssoc w env entry a goal.role name rhs :=
    exact_for_entry policy scope w brand a sealed.selected env fallback entry table go site tab goal.role name rhs
  rw [assoc_independent_of_constraints impls (roleTable table) wf goal name success impl present selected]
  unfold assocValue
  rw [omitted]
  constructor
  · intro result
    cases slot : (roleTable table goal.role).assoc name with
    | none => simp [slot,Option.join] at result
    | some rhs =>
      cases rhs with
      | none => simp [slot,Option.join] at result
      | some body => exact ⟨body,(read _).mp slot,by simpa [slot,Option.join] using result⟩
  · rintro ⟨body,origin,rfl⟩
    rw [(read _).mpr origin]
    rfl

end Yulang.GeneralSourceRoleCstSelectedDefault295
