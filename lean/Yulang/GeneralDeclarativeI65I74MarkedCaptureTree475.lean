import Yulang.GeneralDeclarativeI65I74BeforeCaptureRun475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields Tail)
open GeneralDeclarativeNestedRun332 (run runArgs runFields tagId tailRun)
open GeneralDeclarativeNestedView332 (literalRows expand)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open CommonRoleCanonicalRows (Row)

structure Opened (rows : List StampedRead) where
  name : Nat
  picked : StampedRead
  literalFirst : first name rows = some picked

structure Traced (rows : List StampedRead) where
  uses : List Occurrence
  opened : List (Opened rows)

def Traced.cat {rows} (first rest : Traced rows) : Traced rows :=
  ⟨first.uses ++ rest.uses,first.opened ++ rest.opened⟩

def Traced.prefix {rows} (xs : List (Opened rows)) (value : Traced rows) : Traced rows :=
  ⟨value.uses,xs ++ value.opened⟩

def exposeStamped (rows : List StampedRead) (e : Expr) : Expr × List (Opened rows) :=
  match e with
  | .variable n =>
    match hit : first n rows with
    | none => (e,[])
    | some picked => (picked.row.right,[⟨n,picked,hit⟩])
  | others => (others,[])

/- Capture-local annotation of the old finite source view. No raw name,
equation, source route, or K2 decision is created by this trace. -/
mutual
def runMarked (rows : List StampedRead) (mode : Mode) (input : Expr) : Node → Option (Traced rows)
  | .capture binder => some ⟨[⟨binder,mode,input⟩],[]⟩
  | .primitive tag targets =>
    let e := exposeStamped rows input
    match e.1 with
    | .primitive observed raw =>
      if tagId observed = tagId tag then
        (runMarkedArgs rows mode raw targets).map (Traced.prefix e.2)
      else none
    | _ => none
  | .nominal tag targets =>
    let e := exposeStamped rows input
    match e.1 with
    | .nominal observed raw =>
      if observed = tag then (runMarkedArgs rows .actual raw targets).map (Traced.prefix e.2) else none
    | _ => none
  | .variant tag target =>
    let e := exposeStamped rows input
    match e.1 with
    | .variant observed raw =>
      if observed = tag then (runMarked rows mode raw target).map (Traced.prefix e.2) else none
    | _ => none
  | .join first last =>
    let e := exposeStamped rows input
    match e.1 with
    | .join a b => do
      let x ← runMarked rows mode a first
      let y ← runMarked rows mode b last
      pure (Traced.prefix e.2 (x.cat y))
    | _ => none
  | .record written tail => do
    if written.keys ≠ [] ∧ written.keys.Nodup then
      let e := exposeStamped rows input
      let (raw,terminal) ← literalRows (fun _ => none) e.1
      let selected ← order (CommonRoleCanonicalRows.normalize raw) written.keys
      let children ← runMarkedFields rows mode selected written
      let rest ← tailRun mode (tailExpr raw written.keys terminal) tail
      pure (Traced.prefix e.2 (children.cat ⟨rest,[]⟩))
    else none

def runMarkedArgs (rows : List StampedRead) (mode : Mode) (input : List Expr) : Nodes → Option (Traced rows)
  | .nil => if input.isEmpty then some ⟨[],[]⟩ else none
  | .cons first rest =>
    match input with
    | [] => none
    | a::as => do
      let x ← runMarked rows mode a first
      let y ← runMarkedArgs rows mode as rest
      pure (x.cat y)

def runMarkedFields (rows : List StampedRead) (mode : Mode) (input : Row Expr) : Fields → Option (Traced rows)
  | .nil => if input.isEmpty then some ⟨[],[]⟩ else none
  | .cons key payload rest =>
    match input with
    | [] => none
    | (label,rhs)::later => do
      if key = label then
        let head ← runMarked rows mode rhs payload
        let tail ← runMarkedFields rows mode later rest
        pure (head.cat tail)
      else none
end

def stampedView (normal : GeneralDeclarativeHead320.State) (rows : List StampedRead) :
    GeneralDeclarativeHead320.State :=
  ⟨normal.normal,rows.map StampedRead.row⟩

def stampedOld (normal : GeneralDeclarativeHead320.State) (rows : List StampedRead) :=
  GeneralDeclarativeNestedIndex332.ofRows (s := stampedView normal rows)
    (rows.map StampedRead.row) (fun _ h => h)

theorem expose_erases {normal : GeneralDeclarativeHead320.State} {rows : List StampedRead} (e : Expr) :
    (exposeStamped rows e).1 = expand (stampedOld normal rows) e := by
  cases e with
  | «variable» n =>
    have h := first_erases_to_unchanged_old_result n rows
    change (exposeStamped rows (.variable n)).1 =
      (GeneralDeclarativeNestedIndex332.direct (rows.map StampedRead.row) n).getD (.variable n)
    simp only [exposeStamped]
    split
    · rename_i read
      simp only [read, Option.map_none] at h
      simp [←h]
    · rename_i got read
      simp only [read,Option.map_some] at h
      simp [←h]
  | primitive | nominal | record | variant | join => rfl

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
