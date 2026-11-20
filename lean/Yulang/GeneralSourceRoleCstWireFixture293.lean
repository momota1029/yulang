import Yulang.GeneralSourceRoleCstWirePaths293
import Yulang.GeneralSourceRoleCstSourceExtentFixture293

/-! Wire fixture for the documented role, including exact public Rust tag
spellings. It is reconstructed from documentation, not emitted by Rust here. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralSourceRoleCstWireFixture293
open GeneralSourceRoleCstWire293 (Wire decode spelling)
open GeneralSourceRoleCstWirePaths293 (exportWire atWire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstLossless293 (documentedFile)
open GeneralSourceRoleCstSpan293 (locate)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleCstShapes293 (toHead)

def ws : Wire := .token "Whitespace" " "
def indent : Wire := .token "Whitespace" "\n    "
def ident (s : String) : Wire := .token "Identifier" s
def sigil (s : String) : Wire := .token "SigilIdentifier" s

def rawRequired : Wire := .node "TypeDeclaration" [.token "TypeKw" "type",ws,ident "value"]

def rawMethod : Wire := .node "BindingStatement"
  [.token "PubKw" "pub",ws,ident "index",.token "Colon" ":",ws,
    .node "TypeExpression" [sigil "'key",ws,.token "Arrow" "->",ws,ident "value"]]

def rawRole (m : Wire) : Wire :=
  .node "RoleDeclaration" [.token "PubKw" "pub",ws,.token "RoleKw" "role",ws,
    .node "TypeExpression" [ident "Index",.node "TypeApplyArgument" [ws,sigil "'container"],
      .node "TypeApplyArgument" [ws,sigil "'key"]],
    .token "Colon" ":",
    .node "IndentedStatementBlock" [indent,.node "Statement" [rawRequired],indent,.node "Statement" [m]]]

def raw : Wire := .node "Root" [rawRole rawMethod]
def path : Address Nat := ⟨42,[0]⟩

def expected : Tracked Unit (Address Nat) :=
  ⟨(),toHead "Index" ["'container","'key"],path,
    [(⟨42,[0,6,1,0]⟩,.typeDecl ⟨"value",false,.absent,true⟩),
     (⟨42,[0,6,3,0]⟩,.other)]⟩

theorem actual_tag_spellings_decode : decode raw = some documentedFile := rfl

theorem exported_role_exact :
    exportWire () 42 raw path = some expected := rfl

theorem visible_raw_member_slot : atWire [0,6,1,0] raw = some rawRequired := rfl

theorem nested_unknown_tag_rejected :
    decode (.node "Root" [rawRole (.node "BindingStatement" [.token "MadeUpTag" "?"])]) = none := rfl

theorem nesting_recovery_not_opaque :
    exportWire () 42 (.node "Root" [rawRole (.node "BindingStatement"
      [.node "NestingTooDeep" [.token "Error" "x"]])]) path = none := rfl

#guard (exportWire () 42 raw path).isSome

end Yulang.GeneralSourceRoleCstWireFixture293
