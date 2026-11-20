import Yulang.GeneralSourceRoleCstPath293
import Yulang.GeneralSourceRoleHeadPacketFixture292

/-! The required declaration mirrors the documented indented role topology.
The other cases are explicit controls, not a Rust executable trace. -/
namespace Yulang.GeneralSourceRoleCstFixture293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstProducer293 (extract)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstShapes293 (toHead)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleSyntaxBoundary292 (Rhs)

def ws : Tree := .token .whitespace " "
def indent : Tree := .token .whitespace "\n    "
def id (s : String) : Tree := .token .identifier s
def sigil (s : String) : Tree := .token .sigilIdentifier s
def head : Tree := .node .head
  [id "Index",.node .argument [ws,sigil "'container"],.node .argument [ws,sigil "'key"]]

def required : Tree := .node .typeDecl [.token .typeKw "type",ws,id "value"]
def namedBody (t : Tree) : Tree := .node .typeDecl
  [.token .typeKw "type",ws,id "value",ws,.token .equals "=",ws,.node .head [t]]

def method : Tree := .node .binding [.token .pubKw "pub",.node .other [id "index"]]

def block (first second : Tree) : Tree :=
  .node .indented [indent,.node .statement [first],indent,.node .statement [second]]

def role (h b : Tree) : Tree :=
  .node .role [.token .pubKw "pub",ws,.token .roleKw "role",ws,h,.token .colon ":",b]

def whole (assoc : Tree) : Tree :=
  .node .root [required,.token .whitespace "\n",role head (block assoc method)]

def result (body : Rhs) (eq : Bool) : Tracked Unit Path :=
  ⟨(),toHead "Index" ["'container","'key"],[2],
    [([2,6,1,0],.typeDecl ⟨"value",eq,body,true⟩),([2,6,3,0],.other)]⟩

def run (file : Tree) : Option (Tracked Unit Path) :=
  (follow [2] file).bind (extract () [2])

theorem required_roundtrip : run (whole required) = some (result .absent false) := rfl
theorem binder_roundtrip :
    run (whole (namedBody (sigil "'key"))) = some (result (.binder "'key") true) := rfl
theorem scalar_roundtrip :
    run (whole (namedBody (id "char"))) = some (result (.nullary "char") true) := rfl

theorem direct_handle_readback :
    follow [2,6,1,0] (whole required) = some required ∧
    follow [2,6,3,0] (whole required) = some method := ⟨rfl,rfl⟩

theorem nested_member_not_promoted :
    run (.node .root [required,ws,role head (block required
      (.node .statement [.node .statement [required]]))]) = none := rfl

theorem missing_rhs_rejected : run (whole (namedBody (.node .missing []))) = none := rfl

theorem unsupported_argument_not_dropped :
    extract () [] (role (.node .head
      [id "Index",.node .argument [.node .other [id "A",id "B"]],
        .node .argument [sigil "'key"]]) (block required method)) = none := rfl

theorem recovery_in_method_rejected :
    extract () [] (role head (block required (.node .binding [.node .error []]))) = none := rfl

#guard (run (whole required)).isSome
#guard (run (whole (namedBody (.node .missing [])))).isNone

end Yulang.GeneralSourceRoleCstFixture293
