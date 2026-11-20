import Yulang.GeneralSourceMetadataFiniteLookup291

/-! Finite resolved role data, with existing positional scope carried by
the row and finite name uniqueness tested independently. -/
namespace Yulang.GeneralSourceMetadataRoles291
open GeneralSourceMetadataFiniteLookup291 (get some_sound)
open GeneralSourceMetadataDefaults291 (Default)

structure RoleRow where
  role : Nat
  arity : Nat
  outputs : List (Nat × Option Roles.Term)
  boundOK : ∀ name rhs, (name,some rhs) ∈ outputs → rhs.bound ≤ arity

structure RoleSource where
  fallbackArity : Nat
  rows : List RoleRow

def RoleRow.interpret (row : RoleRow) : Roles.RoleDecl :=
  ⟨row.arity,fun name => get name row.outputs,
    fun name rhs h => row.boundOK name rhs (some_sound h)⟩

def fallback (arity : Nat) : Roles.RoleDecl := ⟨arity,fun _ => none,fun _ _ bad => by cases bad⟩

def index (s : RoleSource) : List (Nat × RoleRow) :=
  s.rows.map fun row => (row.role,row)

def roleTable (s : RoleSource) : Roles.RoleDecls := fun role =>
  (get role (index s)).map RoleRow.interpret |>.getD (fallback s.fallbackArity)

def Valid (s : RoleSource) : Prop :=
  (s.rows.map RoleRow.role).Nodup ∧ ∀ row ∈ s.rows, (row.outputs.map Prod.fst).Nodup

def check (s : RoleSource) : Bool :=
  decide (s.rows.map RoleRow.role).Nodup && s.rows.all (fun row => decide (row.outputs.map Prod.fst).Nodup)

theorem check_exact (s : RoleSource) : check s = true ↔ Valid s := by
  simp only [check,Valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]

theorem indexed {s : RoleSource} {role : Nat} {row : RoleRow}
    (found : get role (index s) = some row) : row ∈ s.rows ∧ row.role = role := by
  obtain ⟨w,p,eq⟩ := List.mem_map.mp (some_sound found)
  cases eq
  exact ⟨p,rfl⟩

theorem lookup_row {s : RoleSource} (valid : Valid s) {r : RoleRow} (member : r ∈ s.rows) :
    get r.role (index s) = some r := by
  apply GeneralSourceMetadataFiniteLookup291.some_complete
  · simpa only [index,List.map_map,Function.comp_def] using valid.1
  · exact List.mem_map.mpr ⟨r,member,rfl⟩

theorem role_ext (a b : Roles.RoleDecl) (arity : a.arity = b.arity) (assoc : a.assoc = b.assoc) : a = b := by
  cases a
  cases b
  cases arity
  cases assoc
  rfl

end Yulang.GeneralSourceMetadataRoles291
