import Yulang.GeneralSourceRoleCstSelectedDefault295

/-! Closed synthetic contrast. Both selectable positions intentionally use
the same role spelling and independently supplied name map, but distinct
defaults. This is a wire adapter control, not a claim the Rust parser
accepts a file with two declarations of this spelling. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralSourceRoleCstSelectedControl295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWireFixture293 (ws indent ident sigil rawMethod)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceRoleCstVisibleReceipt294 (project)
open GeneralSourceRoleCstWireBinding294 (BoundReceipt useBound)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleResolverFixture292
  (localEnv parameterTable charTable role_parameter_used_by_actual_reader nullary_shell_default_used)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles
open Roles.Examples (int str)
open Roles.AssocExamples (char index singletonEnv omittedImpl omitted_paterson)

def rawAssoc (body : Wire) : Wire :=
  .node "TypeDeclaration" [.token "TypeKw" "type",ws,ident "value",ws,.token "Equals" "=",ws,
    .node "TypeExpression" [body]]

def rawWrapped (body : Wire) : Wire :=
  .node "RoleDeclaration" [.token "PubKw" "pub",ws,.token "RoleKw" "role",ws,
    .node "TypeExpression" [ident "Index",
       .node "TypeApplyArgument" [ws,.node "TypeExpression" [sigil "'container"]],
       .node "TypeApplyArgument" [ws,.node "TypeExpression" [sigil "'key"]]],
    .token "Colon" ":",
    .node "IndentedStatementBlock" [indent,.node "Statement" [rawAssoc body],indent,
      .node "Statement" [rawMethod]]]

def both : Wire :=
  .node "Root" [rawWrapped (sigil "'key"),.token "Newline" "\n",rawWrapped (ident "char")]

def first : Address Nat := ⟨71,[0]⟩
def second : Address Nat := ⟨71,[2]⟩
def diag : BoundReceipt Nat := ⟨both,.reported 71 []⟩

def packet (site : Address Nat) : Boundary Nat Nat :=
  ⟨5,⟨site,.selectedBranch,diag⟩⟩

def naming : Nat → Environment := fun _ => localEnv
def actualRead (table : RoleSource) : Option Term :=
  assocOf (singletonEnv omittedImpl) (roleTable table) omitted_paterson (index str int) 0

theorem reusable_view_found_both :
    (useBound .selectedBranch 5 both 71 first diag).isSome = true ∧
    (useBound .selectedBranch 5 both 71 second diag).isSome = true := ⟨rfl,rfl⟩

theorem selected_controls :
    compile .selectedBranch 5 both 71 first (packet first) naming 2 = some parameterTable ∧
    compile .selectedBranch 5 both 71 second (packet first) naming 2 = none ∧
    compile .selectedBranch 5 both 71 second (packet second) naming 2 = some charTable :=
  ⟨rfl,rfl,rfl⟩

theorem wrong_context_denied :
    compile .selectedBranch 6 both 71 first (packet first) naming 2 = none ∧
    compile .whole 5 both 71 first (packet first) naming 2 = none ∧
    compile .selectedBranch 5 both 72 first (packet first) naming 2 = none :=
  ⟨rfl,rfl,rfl⟩

theorem reader_differs_by_selected_declaration :
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind actualRead) = some int ∧
    ((compile .selectedBranch 5 both 71 second (packet first) naming 2).bind actualRead) = none ∧
    ((compile .selectedBranch 5 both 71 second (packet second) naming 2).bind actualRead) = some char := by
  obtain ⟨p,q,r⟩ := selected_controls
  rw [p,q,r]
  exact ⟨role_parameter_used_by_actual_reader,rfl,nullary_shell_default_used⟩

end Yulang.GeneralSourceRoleCstSelectedControl295
