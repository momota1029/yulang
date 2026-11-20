import Yulang.GeneralSourceRoleResolverUse292

/-! The source binder index has an independent characterization by the
ordered head list. Duplicates must be rejected before assigning this meaning. -/
namespace Yulang.GeneralSourceRoleBinderIndex292
open GeneralSourceRoleSpelling292

theorem of_index {xs : List String} (unique : xs.Nodup) {s : String} {n : Nat}
    (read : xs[n]? = some s) : Position s xs n := by
  induction xs generalizing n with
  | nil => cases read
  | cons x xs ih =>
    cases n with
    | zero =>
      rw [List.getElem?_cons_zero] at read
      cases Option.some.inj read
      exact .first
    | succ n =>
      rw [List.getElem?_cons_succ] at read
      have tail := List.nodup_cons.mp unique
      have diff : x ≠ s := by
        intro same
        subst s
        exact tail.1 (List.mem_of_getElem? read)
      exact .rest diff (ih tail.2 read)

theorem index_exact (binders : List String) (unique : binders.Nodup)
    (s : String) (slot : Nat) :
    position s binders = some slot ↔ binders[slot]? = some s :=
  (position_exact ..).trans ⟨position_index,of_index unique⟩

theorem duplicate_lookup_cannot_use_every_index :
    (["'a","'a"] : List String)[1]? = some "'a" ∧
    position "'a" ["'a","'a"] = some 0 ∧
    position "'a" ["'a","'a"] ≠ some 1 := by decide

theorem binder_value_at_exact_index (env : Environment) (xs : List String) (nodup : xs.Nodup)
    (name : String) (n : Nat) (args : List Roles.Term) (len : args.length = xs.length)
    (direct : xs[n]? = some name) :
    body env xs (.binder name) = some (some (.var n)) ∧
      ∃ value, args[n]? = some value ∧ (.var n : Roles.Term).subst (Roles.defaultSubst args) = value := by
  refine ⟨(body_exact ..).mpr (.binder (of_index nodup direct)),?_⟩
  exact GeneralSourceRoleResolverUse292.supplied_positional (of_index nodup direct) args len

end Yulang.GeneralSourceRoleBinderIndex292
