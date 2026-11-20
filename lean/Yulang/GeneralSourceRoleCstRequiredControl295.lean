import Yulang.GeneralSourceRoleCstSelectedJson295

/-! Controlled required associated declaration, no substituted default.
The actual archived role is method-only and yields no output slot at all. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralSourceRoleCstRequiredControl295
open GeneralSourceRoleCstSelectedControl295 (rawWrapped first second both packet naming actualRead)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWireFixture293 (rawRequired sigil ident rawMethod indent)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceRoleTrack292 (runTracked)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleResolverFixture292 (requiredTable required_without_body_is_not_valid_implementation)
open Roles
open Roles.Examples (int str)
open Roles.AssocExamples (index singletonEnv omittedImpl)

def requiredRole : Wire :=
  match rawWrapped (sigil "'key") with
  | .node tag children => .node tag
    (children.take 6 ++ [.node "IndentedStatementBlock"
      [indent,.node "Statement" [rawRequired],indent,.node "Statement" [rawMethod]]])
  | token => token

def retained : Wire := .node "Root" [requiredRole]
def permitted : Boundary Nat Nat := ⟨5,⟨first,.selectedBranch,⟨retained,.reported 71 []⟩⟩⟩

theorem required_slot_separate_from_nondeclaration :
    compile .selectedBranch 5 retained 71 first permitted naming 2 = some requiredTable ∧
    (roleTable requiredTable 2).assoc 0 = some none ∧
    (roleTable requiredTable 2).assoc 1 = none := ⟨rfl,rfl,rfl⟩

theorem required_omitted_not_a_default :
    ((compile .selectedBranch 5 retained 71 first permitted naming 2).bind actualRead) = none ∧
    ¬ AssocWellFormed (singletonEnv omittedImpl) (roleTable requiredTable) := by
  rw [required_slot_separate_from_nondeclaration.1]
  exact required_without_body_is_not_valid_implementation

theorem both_selected_still_not_a_joint_same_key_export :
    ((handoff .selectedBranch 5 both 71 first (packet first)).bind fun p =>
      (handoff .selectedBranch 5 both 71 second (packet second)).bind fun q =>
        runTracked naming 2 [p,q]) = none := rfl

end Yulang.GeneralSourceRoleCstRequiredControl295
