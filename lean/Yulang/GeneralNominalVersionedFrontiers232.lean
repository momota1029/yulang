import Yulang.GeneralNominalVersionedBoundary232
namespace Yulang.GeneralNominalVersionedFrontiers232
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedBoundary232
variable {roles : Roles.RoleDecls}

/-! Two concrete local frontier bridge laws. These do not provide a saturation
executor, termination, child accessibility, or registry-order independence. -/
noncomputable def frontiers (roles : Roles.RoleDecls) (registry : Registry) (state : State roles) :
    Protocol (Occurrence roles) := by
  classical
  exact { frontier := fun root => if checked : Checked registry then Classical.choose (local_total checked state root) else .pending
          Local := Local registry state }

theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier := by
  classical
  have valid := Classical.choose_spec (local_total checked.2 state root)
  change (if checked : Checked registry then Classical.choose (local_total checked state root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  exact ⟨fun same => same ▸ valid,fun chosen => local_functional valid chosen⟩

theorem localIdentity (registry : Registry) (state : State roles) :
    (frontiers roles registry state).Local = Local registry state := rfl
end Yulang.GeneralNominalVersionedFrontiers232
