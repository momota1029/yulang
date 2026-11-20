import Yulang.GeneralSourceRoleCstNamingGate295

/-! Synthetic checks for distinct roles of declaration scope and semantic
lookup values. They use the C292 example environment, not Rust name binding. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralSourceRoleCstNamingControl295
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleCstSelectedControl295 (first second packet both naming)
open GeneralSourceRoleCstSelectedCompile295 (compile)
open GeneralSourceRoleCstNamingGate295 (check checkedCompile)
open GeneralSourceRoleResolverFixture292 (localEnv parameterTable charTable)
open GeneralSourceMetadataRoles291 (RoleRow)

def shiftedRole : Nat → Environment := fun _ =>
  { localEnv with
    role := fun n => if n = "Index" then some 12 else localEnv.role n,
    output := fun r n => if r = 12 then localEnv.output 2 n else localEnv.output r n }

def shiftedOutput : Nat → Environment := fun _ =>
  { localEnv with output := fun r n => if r = 2 ∧ n = "value" then some 4 else localEnv.output r n }

def shiftedCtor : Nat → Environment := fun _ =>
  { localEnv with nullaryConstructor := fun n =>
      if n = "char" then some 33 else localEnv.nullaryConstructor n }

def irrelevant : Nat → Environment := fun sc =>
  if sc = 5 then { localEnv with role := fun n => if n = "Other" then some 19 else localEnv.role n }
    else shiftedCtor sc

theorem unguarded_context_can_change_key :
    ((compile .selectedBranch 5 both 71 first (packet first) shiftedRole 2).map
      (fun r => r.rows.map RoleRow.role)) = some [12] := by
  -- This alternative needs the output key for the new role as well.
  rfl

theorem checked_compares_actual_output_requests :
    (check .selectedBranch 5 both 71 first (packet first) naming shiftedOutput) = false ∧
    checkedCompile .selectedBranch 5 both 71 first (packet first) naming shiftedOutput 2 = none :=
  ⟨rfl,rfl⟩

theorem constructor_scope_used_only_by_second :
    (check .selectedBranch 5 both 71 first (packet first) naming shiftedCtor) = true ∧
    (check .selectedBranch 5 both 71 second (packet second) naming shiftedCtor) = false := ⟨rfl,rfl⟩

theorem unrelated_lookups_do_not_change_selected_export :
    checkedCompile .selectedBranch 5 both 71 first (packet first) naming irrelevant 2 =
      some parameterTable := rfl

end Yulang.GeneralSourceRoleCstNamingControl295
