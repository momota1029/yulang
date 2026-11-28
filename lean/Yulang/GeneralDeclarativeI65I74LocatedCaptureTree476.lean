import Yulang.GeneralDeclarativeI65I74MarkedRootOrigin475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields)
open GeneralDeclarativeNestedRun332 (tagId tailRun)
open GeneralDeclarativeNestedView332 (literalRows)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row)

/-- Coordinates relative to the already compiled capture query, not
physical parser keys or a new rule of inspection. The two join keys
name the existing C332 capture arms only. -/
inductive QueryStep476 where
  | field (label : Nat)
  | argument (ordinal : Nat)
  | variantPayload
  | legacyJoinLeft
  | legacyJoinRight
  deriving DecidableEq, BEq, Repr

structure LocatedMark476 (rows : List StampedRead) where
  path : List QueryStep476
  exposure : Opened rows

structure LocatedCapture476 (rows : List StampedRead) where
  uses : List Occurrence
  marks : List (LocatedMark476 rows)

def LocatedCapture476.combine {rows} (a b : LocatedCapture476 rows) : LocatedCapture476 rows :=
  ⟨a.uses ++ b.uses,a.marks ++ b.marks⟩

def LocatedCapture476.prefix {rows} (path : List QueryStep476) (marks : List (Opened rows))
    (out : LocatedCapture476 rows) : LocatedCapture476 rows :=
  ⟨out.uses,(marks.map fun mark => ⟨path,mark⟩) ++ out.marks⟩

def LocatedCapture476.erase {rows} (out : LocatedCapture476 rows) : Traced rows :=
  ⟨out.uses,out.marks.map LocatedMark476.exposure⟩

mutual
def runLocated476 (rows : List StampedRead) (path : List QueryStep476)
    (mode : Mode) (input : Expr) : Node → Option (LocatedCapture476 rows)
  | .capture binder => some ⟨[⟨binder,mode,input⟩],[]⟩
  | .primitive tag targets =>
    let e := exposeStamped rows input
    match e.1 with
    | .primitive actual raw =>
      if tagId actual = tagId tag then
        (runLocatedArgs476 rows path 0 mode raw targets).map (LocatedCapture476.prefix path e.2)
      else none
    | _ => none
  | .nominal tag targets =>
    let e := exposeStamped rows input
    match e.1 with
    | .nominal actual raw =>
      if actual = tag then
        (runLocatedArgs476 rows path 0 .actual raw targets).map (LocatedCapture476.prefix path e.2)
      else none
    | _ => none
  | .variant tag target =>
    let e := exposeStamped rows input
    match e.1 with
    | .variant actual raw =>
      if actual = tag then
        (runLocated476 rows (path ++ [.variantPayload]) mode raw target).map (LocatedCapture476.prefix path e.2)
      else none
    | _ => none
  | .join left right =>
    let e := exposeStamped rows input
    match e.1 with
    | .join a b => do
      let x ← runLocated476 rows (path ++ [.legacyJoinLeft]) mode a left
      let y ← runLocated476 rows (path ++ [.legacyJoinRight]) mode b right
      pure (LocatedCapture476.prefix path e.2 (x.combine y))
    | _ => none
  | .record written tail => do
    if written.keys ≠ [] ∧ written.keys.Nodup then
      let e := exposeStamped rows input
      let (raw,terminal) ← literalRows (fun _ => none) e.1
      let selected ← order (CommonRoleCanonicalRows.normalize raw) written.keys
      let children ← runLocatedFields476 rows path mode selected written
      let rest ← tailRun mode (tailExpr raw written.keys terminal) tail
      pure (LocatedCapture476.prefix path e.2 (children.combine ⟨rest,[]⟩))
    else none

def runLocatedArgs476 (rows : List StampedRead) (path : List QueryStep476) (ordinal : Nat)
    (mode : Mode) (input : List Expr) : Nodes → Option (LocatedCapture476 rows)
  | .nil => if input.isEmpty then some ⟨[],[]⟩ else none
  | .cons first rest =>
    match input with
    | [] => none
    | a::as => do
      let x ← runLocated476 rows (path ++ [.argument ordinal]) mode a first
      let y ← runLocatedArgs476 rows path (ordinal+1) mode as rest
      pure (x.combine y)

def runLocatedFields476 (rows : List StampedRead) (path : List QueryStep476)
    (mode : Mode) (input : Row Expr) : Fields → Option (LocatedCapture476 rows)
  | .nil => if input.isEmpty then some ⟨[],[]⟩ else none
  | .cons key payload rest =>
    match input with
    | [] => none
    | (label,rhs)::later => do
      if key = label then
        let head ← runLocated476 rows (path ++ [.field key]) mode rhs payload
        let tail ← runLocatedFields476 rows path mode later rest
        pure (head.combine tail)
      else none
end

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
