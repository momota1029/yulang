import Yulang.GeneralSourceRoleCstSelectedRow295

namespace Yulang.GeneralSourceRoleCstOtherRole295
open GeneralSourceMetadataRoles291 (RoleSource RoleRow roleTable fallback index indexed)
open GeneralSourceMetadataFiniteLookup291 (get)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile)
open GeneralSourceRoleCstSelectedRow295 (compile_single_row)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleSpelling292 (Environment)

theorem other_role_is_fallback (table : RoleSource) (row : RoleRow)
    (just : table.rows = [row]) (r : Nat) (different : r ≠ row.role) :
    roleTable table r = fallback table.fallbackArity := by
  unfold roleTable
  cases read : get r (index table) with
  | none => rfl
  | some picked =>
    have ⟨member,same⟩ := indexed read
    rw [just] at member
    exact False.elim (different ((List.mem_singleton.mp member) ▸ same.symm))

theorem no_other_role_data {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (arity : Nat)
    (table : RoleSource) (done : compile policy scope w brand a sealed env arity = some table) :
    ∃ row : RoleRow, table.rows = [row] ∧ ∀ r, r ≠ row.role → roleTable table r = fallback arity := by
  obtain ⟨fixed,_,_,row,_,_,_,just,_⟩ := compile_single_row policy scope w brand a sealed env arity table done
  exact ⟨row,just,fun r diff => fixed ▸ other_role_is_fallback table row just r diff⟩

end Yulang.GeneralSourceRoleCstOtherRole295
