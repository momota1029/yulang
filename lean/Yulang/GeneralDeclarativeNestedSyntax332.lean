import Yulang.GeneralDeclarativeInlineTrace331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedSyntax332
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (TailCode)
open GeneralDeclarativeRecordResidual323 (withTail)
open CommonRoleCanonicalRows (Row)
open GeneralCandidateInspection (Primitive)

inductive Tail where
  | capture (key : Nat)
  | width
  | exactEnd

def Tail.code : Tail → Expr
  | .capture key => .variable key
  | .width => .primitive .emptyRecord []
  | .exactEnd => .primitive .exactEmpty []

theorem Tail.code_ok (tail : Tail) : TailCode tail.code := by
  cases tail with
  | capture => exact .binder
  | width => exact .width
  | exactEnd => exact .exactEnd

mutual
/-- Only the finite normalized head grammar covered by this source
producer. A record spine is represented as one selected field list;
the tail is not itself a second competing decomposition. -/
inductive Node where
  | capture (key : Nat)
  | primitive (tag : Primitive) (fields : Nodes)
  | nominal (tag : Nat) (fields : Nodes)
  | variant (tag : Nat) (payload : Node)
  | join (left right : Node)
  | record (fields : Fields) (tail : Tail)
inductive Nodes where
  | nil
  | cons (head : Node) (tail : Nodes)
inductive Fields where
  | nil
  | cons (key : Nat) (head : Node) (tail : Fields)
end

mutual
def Node.code : Node → Expr
  | .capture key => .variable key
  | .primitive tag args => .primitive tag args.codes
  | .nominal tag args => .nominal tag args.codes
  | .variant tag payload => .variant tag payload.code
  | .join a b => .join a.code b.code
  | .record row tail => withTail row.codes tail.code
def Nodes.codes : Nodes → List Expr
  | .nil => []
  | .cons first last => first.code::last.codes
def Fields.codes : Fields → Row Expr
  | .nil => []
  | .cons key one rest => (key,one.code)::rest.codes
end

def Fields.keys (row : Fields) : List Nat := row.codes.map Prod.fst

/-- Non-binder target needed to open a supported name. In the
record case the nonempty key guard excludes a disguised binder. -/
def Node.observable : Node → Prop
  | .capture _ => False
  | .record fields _ => fields.keys ≠ []
  | _ => True

theorem Node.not_binder (target : Node) (exposes : target.observable) (n : Nat) :
    target.code ≠ .variable n := by
  intro h
  cases target with
  | capture => exact exposes
  | primitive | nominal | variant | join => cases h
  | record fs tail =>
    cases fs with
    | nil => exact exposes rfl
    | cons => cases h

end Yulang.GeneralDeclarativeNestedSyntax332
