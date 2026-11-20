import Yulang.GeneralSourceRoleAttach292

/-! Hand-stated role spelling certificate attached to the existing two Lean
source worlds. This verifies identity with actual resolver input, not that the
role shell was emitted from Rust parsing or chosen by it. -/
namespace Yulang.GeneralSourceRoleActualAttach292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (Shell)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceRoleAttach292 (Input compose)
open GeneralSourceMetadataBundle291 (Certificate inspect)
open GeneralSourceMetadataBundleFixture291 (actual executable_both)
open GeneralSourceMetadataRoleFixture291 (fixture actual_role_table)
open GeneralRebaseRowChildSource287 (registry roles)

def roleShell : Shell := ⟨"Parent",["'a"],[⟨"value",false,.absent,true⟩]⟩

def suppliedEnv : Environment :=
  ⟨fun n => if n = "Parent" then some 0 else none,
   fun r n => if r = 0 ∧ n = "value" then some 0 else none,
   fun _ => none⟩

theorem lowers_exact_actual_table : applyShells suppliedEnv 1 [roleShell] = some fixture := by rfl

theorem original_roles_pointwise :
    ∀ r, (GeneralSourceMetadataRoles291.roleTable fixture r) = roles r := by
  intro r; rw [actual_role_table]

def attachInput (branch : Bool) : Input :=
  ⟨(actual branch).declared,(actual branch).snapshot,(registry branch).declarations,1,[roleShell]⟩

theorem exact_actual_bundle (choice : Bool) :
    compose suppliedEnv (attachInput choice) = some (actual choice) :=
  (GeneralSourceRoleAttach292.assemble_exact ..).mpr ⟨rfl,rfl,rfl,lowers_exact_actual_table⟩

theorem preserves_actual_ready (choice : Bool) :
    ((compose suppliedEnv (attachInput choice)).map (fun s => (inspect s).ready)) = some choice := by
  rw [exact_actual_bundle]
  exact congrArg some (executable_both choice)

theorem no_new_raw_claim (choice : Bool) :
    GeneralDeclarations.Checked (registry choice) := GeneralRebaseRowChildSource287.checked choice

end Yulang.GeneralSourceRoleActualAttach292
