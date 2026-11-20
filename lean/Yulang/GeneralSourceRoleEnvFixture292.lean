import Yulang.GeneralSourceRoleEnvExact292
import Yulang.GeneralSourceRoleCoveredShell292

/-! Controls for locality: an unobserved change is harmless, a read change
prevents exact recovery, and mutual failure alone does not imply agreement. -/
namespace Yulang.GeneralSourceRoleEnvFixture292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleEnvCheck292 (checkShells)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceRoleSyntaxFixture292 (full broken read)
open GeneralSourceRoleFixture292 (fixtureEnv)

def untouched : Environment := fixtureEnv 0

def unobserved : Environment :=
  { untouched with nullaryConstructor := fun n =>
    if n = "unused" then some 77 else untouched.nullaryConstructor n }

def changed : Environment :=
  { untouched with nullaryConstructor := fun n =>
    if n = "char" then some 77 else untouched.nullaryConstructor n }

theorem unobserved_check_passes :
    untouched.nullaryConstructor "unused" ≠ unobserved.nullaryConstructor "unused" ∧
    checkShells untouched unobserved [full] = true := by decide

theorem unobserved_same_export :
    applyShells untouched 0 [full] = applyShells unobserved 0 [full] :=
  GeneralSourceRoleEnvCheck292.shell_check_sound _ _ _ _ unobserved_check_passes.2

theorem observed_change_detected :
    checkShells untouched changed [full] = false ∧
    read changed full 1 4 = some (some (some (.app 77 []))) := by decide

theorem malformed_independent_of_resolver :
    checkShells untouched changed [broken] = true ∧
    (applyShells untouched 0 [broken]).isNone = true ∧
    (applyShells changed 0 [broken]).isNone = true := by decide

def missingRole : Environment := { untouched with role := fun _ => none }
def missingOutputs : Environment := { untouched with output := fun _ _ => none }

theorem both_failed_but_not_agree :
    (applyShells missingRole 0 [full]).isNone = true ∧
    (applyShells missingOutputs 0 [full]).isNone = true ∧
    checkShells missingRole missingOutputs [full] = false := by decide

def aliased : Environment :=
  { untouched with output := fun r _ => if r = 1 then some 2 else none }

theorem name_id_collision_detected :
    (applyShells aliased 0 [full]).isNone = true := by decide

#guard checkShells untouched unobserved [full]
#guard !(checkShells untouched changed [full])

end Yulang.GeneralSourceRoleEnvFixture292
