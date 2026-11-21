import Yulang.GeneralDeclarativeNestedView332
import Yulang.GeneralDeclarativeRecordConsumption330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedRun332
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields Tail)
open GeneralDeclarativeNestedView332 (Sources expand literalRows)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeTermWalk322 (Occurrence)
open CommonRoleCanonicalRows (Row normalize)

def tagId : Primitive → Nat
  | .scalar .int => 0
  | .scalar .str => 1
  | .scalar .bool => 2
  | .scalar .unit => 3
  | .pair => 4
  | .emptyRecord => 5
  | .exactEmpty => 6

theorem tagId_exact {a b : Primitive} (matchId : tagId a = tagId b) : a = b := by
  cases a <;> cases b
  all_goals try rfl
  all_goals first
    | (rename_i k j; cases k <;> cases j <;> simp_all [tagId])
    | (rename_i k; cases k <;> simp_all [tagId])
    | cases matchId

def tailRun (mode : Mode) (input : Expr) (tail : Tail) : Option (List Occurrence) :=
  match tail,input with
  | .capture n,raw => some [⟨n,mode,raw⟩]
  | .width,.primitive .emptyRecord [] => some []
  | .exactEnd,.primitive .exactEmpty [] => some []
  | _,_ => none

mutual
/-- Deterministic local source read from the target syntax. Every
recursive call passes to a proper field or argument of the finite
target. Opening a name consults only the given certified view;
the result `none` has no resolution-diagnostic meaning. -/
def run (src : Sources s) (mode : Mode) (input : Expr) : Node → Option (List Occurrence)
  | .capture binder => some [⟨binder,mode,input⟩]
  | .primitive tag targets =>
    match expand src input with
    | .primitive observed raw =>
      if tagId observed = tagId tag then runArgs src mode raw targets else none
    | _ => none
  | .nominal tag targets =>
    match expand src input with
    | .nominal observed raw =>
      if observed = tag then runArgs src .actual raw targets else none
    | _ => none
  | .variant tag target =>
    match expand src input with
    | .variant observed raw =>
      if observed = tag then run src mode raw target else none
    | _ => none
  | .join first last =>
    match expand src input with
    | .join a b => do
      let x ← run src mode a first
      let y ← run src mode b last
      pure (x ++ y)
    | _ => none
  | .record written tail => do
    if written.keys ≠ [] ∧ written.keys.Nodup then
      let (raw,terminal) ← literalRows src.spines (expand src input)
      let selected ← order (normalize raw) written.keys
      let head ← runFields src mode selected written
      let rest ← tailRun mode (tailExpr raw written.keys terminal) tail
      pure (head ++ rest)
    else none
def runArgs (src : Sources s) (mode : Mode) (input : List Expr) : Nodes → Option (List Occurrence)
  | .nil => if input.isEmpty then some [] else none
  | .cons first rest =>
    match input with
    | [] => none
    | a::as => do
      let x ← run src mode a first
      let y ← runArgs src mode as rest
      pure (x++y)
def runFields (src : Sources s) (mode : Mode) (input : Row Expr) : Fields → Option (List Occurrence)
  | .nil => if input.isEmpty then some [] else none
  | .cons key payload rest =>
    match input with
    | [] => none
    | (label,rhs)::later => do
      if key = label then
        let head ← run src mode rhs payload
        let tail ← runFields src mode later rest
        pure (head++tail)
      else none
end

end Yulang.GeneralDeclarativeNestedRun332
