import Yulang.GeneralDictionaryAgreedComputed174
import Yulang.GeneralDictionaryAgreedExact174

/-! Computable declaration certificate followed by the ground-source diagnostic.
The caller runs `check registry fuel`; no declaration rank, common model,
readback producer or accessibility premise is required by these interfaces.
The diagnostic itself remains noncomputable. Rejection by `check` is not a
language rejection and successful `Completed` classification is not guaranteed.
This connects exactly the role-DAG fragment to the current agreed Local relation,
not to a future central-argument representation or general recursive language. -/
namespace Yulang.GeneralDictionaryAgreedChecked174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal
open GeneralDictionaryAgreedGround174 GeneralDictionaryAgreedComputed174
open CommonRoleOutermostResolver B4TargetV5
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

theorem run_resolves_iff (checked : (boundary defer gap).Checked registry)
    (passed : check registry fuel = true)
    (reachable : Reachable (boundary defer gap) registry root state) (tree : Tree) :
    ((executor defer gap).run registry state root).2 = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1) root tree :=
  GeneralDictionaryAgreedExact174.run_resolves_iff checked (check_sound passed) reachable tree

theorem completed_iff (checked : (boundary defer gap).Checked registry)
    (passed : check registry fuel = true)
    (reachable : Reachable (boundary defer gap) registry root state) (out : Result) :
    B4TargetV3.Completed ((executor defer gap).run registry state root).2 out ↔
      B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1 root out :=
  GeneralDictionaryAgreedExact174.completed_iff checked (check_sound passed) reachable out

theorem initial_run_resolves_iff (checked : (boundary defer gap).Checked registry)
    (passed : check registry fuel = true)
    (initial : (boundary defer gap).Initial registry root state) (tree : Tree) :
    ((executor defer gap).run registry state root).2 = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1) root tree :=
  run_resolves_iff checked passed (reachable_initial _ initial) tree

/-- Fuel is certificate-search fuel only: two accepted searches expose the
same executor and current-Local specification, with no runtime fuel parameter. -/
theorem accepted_fuels_same_spec (checked : (boundary defer gap).Checked registry)
    (passed : check registry fuel = true)
    (reachable : Reachable (boundary defer gap) registry root state)
    (tree : Tree) :
    (∃ otherFuel, check registry otherFuel = true ∧
      ((executor defer gap).run registry state root).2 = tree) ↔
    Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
      ((executor defer gap).run registry state root).1) root tree := by
  constructor
  · rintro ⟨_, _, eq⟩
    exact (run_resolves_iff checked passed reachable tree).mp eq
  · intro resolved
    exact ⟨fuel, passed, (run_resolves_iff checked passed reachable tree).mpr resolved⟩

end Yulang.GeneralDictionaryAgreedChecked174
