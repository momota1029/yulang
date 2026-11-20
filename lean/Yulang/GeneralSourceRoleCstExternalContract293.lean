import Yulang.GeneralSourceRoleCstTriviaFixture293
import Yulang.GeneralSourceRoleCstWireFixture293

/-! Wire acceptance and source-text equality are not authentication of
Rust node kinds. These are declared controls on the transport, not parser bugs. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralSourceRoleCstExternalContract293
open GeneralSourceRoleCstWire293 (Wire decode spelling)
open GeneralSourceRoleCstWirePaths293 (exportWire)
open GeneralSourceRoleCstWireFixture293 (raw rawMethod rawRequired path expected ws indent ident sigil)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleTrack292 (Tracked)

def relabeledRole : Wire :=
  .node "RoleDeclaration" [.token "PubKw" "pub",ws,.token "RoleKw" "role",ws,
    .node "TypeExpression" [ident "Index",.node "TypeApplyArgument" [ws,sigil "'container"],
      .node "TypeApplyArgument" [ws,sigil "'key"]],
    .token "Colon" ":",
    .node "IndentedStatementBlock" [indent,
      .node "Statement" [.node "BindingStatement" [.token "TypeKw" "type",ws,ident "value"]],
      indent,.node "Statement" [rawMethod]]]

def relabeledFile : Wire := .node "Root" [relabeledRole]

def relabeledExpected : Tracked Unit (Address Nat) :=
  {expected with body := [(⟨42,[0,6,1,0]⟩,.other),(⟨42,[0,6,3,0]⟩,.other)]}

theorem same_bytes_not_same_child_kind :
    spelling raw = spelling relabeledFile ∧
    exportWire () 42 raw path = some expected ∧
    exportWire () 42 relabeledFile path = some relabeledExpected ∧
    expected.body ≠ relabeledExpected.body := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro bad
  nomatch bad

theorem no_text_only_equality_certificate :
    ¬ ∃ recover : String → Option (Tracked Unit (Address Nat)),
      ∀ w, recover (spelling w) = exportWire () 42 w path := by
  rintro ⟨f,claim⟩
  have split := same_bytes_not_same_child_kind
  have before := claim raw
  rw [split.1,claim relabeledFile,split.2.1,split.2.2.1] at before
  exact split.2.2.2 (congrArg Tracked.body (Option.some.inj before).symm)

/-- Auxiliary tags not inspected by the role slice may compact to the same
kind. Keep the original wire if original labels matter. -/
theorem tag_compaction_not_injective :
    let w := Wire.node "BindingHeader" []
    let x := Wire.node "BindingBody" []
    w ≠ x ∧ decode w = decode x := by
  change Wire.node "BindingHeader" [] ≠ Wire.node "BindingBody" [] ∧
    decode (.node "BindingHeader" []) = decode (.node "BindingBody" [])
  refine ⟨?_,rfl⟩
  intro impossible
  have eq := Wire.node.inj impossible |>.1
  contradiction

end Yulang.GeneralSourceRoleCstExternalContract293
