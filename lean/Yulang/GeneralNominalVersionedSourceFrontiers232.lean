import Yulang.GeneralNominalVersionedSourceBoundary232
namespace Yulang.GeneralNominalVersionedSourceFrontiers232
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 GeneralNominalVersionedSourceBoundary232
variable {roles : Roles.RoleDecls}

/-! Source-facing frontierLocal/localIdentity, with the same HeadAlloc encoding
as the actual source boundary. No saturation or recursive resolver is supplied. -/
noncomputable def frontiers (roles : Roles.RoleDecls) (value : Registry) (state : State roles) :
    Protocol (Occurrence roles) := by
  classical
  exact { frontier := fun root => if checked : (boundary roles).Checked value then Classical.choose (local_total checked state root) else .pending
          Local := Local value state }

theorem frontierLocal (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (frontier) :
    (frontiers roles value state).frontier root = frontier ↔ Local value state root frontier := by
  classical
  have valid := Classical.choose_spec (local_total checked state root)
  change (if checked : (boundary roles).Checked value then Classical.choose (local_total checked state root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked]
  exact ⟨fun same => same ▸ valid,fun chosen => local_functional valid chosen⟩

theorem localIdentity (value : Registry) (state : State roles) :
    (frontiers roles value state).Local = Local value state := rfl
end Yulang.GeneralNominalVersionedSourceFrontiers232
