import Yulang.GeneralSourceRoleDiagnosticLink292
import Yulang.GeneralSourceRoleActualAttach292

/-! Independent perturbation of the certified source table. The added role is
not claimed to occur in the original input or any original raw trajectory. -/
set_option maxRecDepth 29000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralSourceRoleDiagnosticFixture292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (Shape Shell)
open GeneralSourceRoleAttach292 (Input compose)
open GeneralSourceRoleActualAttach292 (attachInput suppliedEnv roleShell)
open GeneralSourceMetadataBundle291 (SourceBundle Certificate inspect)
open GeneralSourceMetadataDiagnostics291 (Failure)

def hiddenDefault : Shape := ⟨"scalar",true,.nullary "Named",true⟩
def extraRole : Shell := ⟨"Unused",[],[hiddenDefault]⟩
def droppedRole : Shell := {extraRole with directTypeChildren := []}

def alternateEnv : Environment :=
  ⟨fun s => if s = "Unused" then some 17 else suppliedEnv.role s,
   fun r n => if r = 17 ∧ n = "scalar" then some 0 else suppliedEnv.output r n,
   fun s => if s = "Named" then some 6 else none⟩

def input (missed : Bool) : Input :=
  {(attachInput true) with shells := [roleShell,if missed then droppedRole else extraRole]}

def diagnostics (missed : Bool) : Option (List Failure) :=
  (compose alternateEnv (input missed)).map fun bundle => (inspect bundle).unsupported

theorem default_diagnostic_exact :
    diagnostics false = some [⟨⟨.roleDefault 17 0,(6,0)⟩,.wrongArity 1⟩] ∧
    diagnostics true = some [] := by decide +kernel

theorem mere_adapter_success_not_complete_coverage :
    ((compose alternateEnv (input false)).map (fun b => (inspect b).ready)) = some false ∧
    ((compose alternateEnv (input true)).map (fun b => (inspect b).ready)) = some true := by
  decide +kernel

def exportedRead (missed : Bool) : Option (Option (Option Roles.Term)) :=
  (compose alternateEnv (input missed)).map fun b =>
    (GeneralSourceMetadataRoles291.roleTable b.roles 17).assoc 0

theorem omitted_cannot_attach_full_roles :
    ∀ full omitted : SourceBundle,
      compose alternateEnv (input false) = some full →
      compose alternateEnv (input true) = some omitted →
      GeneralSourceMetadataRoles291.roleTable full.roles ≠
        GeneralSourceMetadataRoles291.roleTable omitted.roles := by
  intro full omitted fullOK omitOK eq
  have actualSplit :
      exportedRead false = some (some (some (.app 6 []))) ∧ exportedRead true = some none := by
    decide +kernel
  unfold exportedRead at actualSplit
  rw [fullOK,omitOK,Option.map_some,Option.map_some,eq] at actualSplit
  have bad := actualSplit.1.symm.trans actualSplit.2
  cases bad

#guard (diagnostics false).isSome

end Yulang.GeneralSourceRoleDiagnosticFixture292
