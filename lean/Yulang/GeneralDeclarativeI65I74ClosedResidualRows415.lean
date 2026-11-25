import Yulang.GeneralDeclarativeI65I74OpenTailNoAuthority414
import Yulang.CommonRoleStableRecordResidual

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (capture lookup)
open CommonRoleStableRecordResidual (check headMatches size count checked_residual_decreases)
open Checker408 (Problem)

def residualExpr (y payload : Nat) : Expr :=
  .record y (.variable payload) (.primitive .emptyRecord [])

def wholeExpr (x intSlot y strSlot : Nat) : Expr :=
  .record x (.variable intSlot) (residualExpr y strSlot)

def wholeOriginal (x intSlot y strSlot : Nat) : CommonRecursiveNominalIntervals.Endpoint Nat :=
  .ordinary (.record x (.var intSlot) (.record y (.var strSlot) .emptyRecord))

def strRow (strSlot : Nat) : Equation := ⟨strSlot,.primitive (.scalar .str) []⟩

def isSplit415 (root label known : Nat) (e : Equation) : Bool :=
  match e.right with
  | .record key (.variable value) (.variable _) =>
    decide (e.left = root ∧ key = label ∧ value = known)
  | _ => false

structure ClosedRows (s : I72.State) (q : I72.Request) where
  root : Nat
  x : Nat
  intSlot : Nat
  y : Nat
  strSlot : Nat
  residual : Nat
  original : Origin
  actualOriginal : original ∈ s.core.origins
  originalRoot : original.slot = root
  originalCount : (s.core.origins.filter (fun src => src.slot == root)).length = 1
  source : original.endpoint = wholeOriginal x intSlot y strSlot
  requested : q.demand.arguments = [GeneralDeclarativeWitnessDeclaredState357.point root]
  noOutputs : q.demand.outputs = []
  different : x ≠ y
  distinctSlots : ([root,intSlot,strSlot,residual] : List Nat).Nodup
  whole : (⟨root,wholeExpr x intSlot y strSlot⟩ : Equation) ∈ s.core.current.ordinary.equations
  integer : OpenTail414.intRow intSlot ∈ s.core.current.ordinary.equations
  string : strRow strSlot ∈ s.core.current.ordinary.equations
  retainedResidual : (⟨residual,residualExpr y strSlot⟩ : Equation) ∈ s.core.current.ordinary.equations
  retainedSplit : OpenTail414.openRow root x intSlot residual ∈ s.core.current.ordinary.equations
  uniqueSplit : s.core.current.ordinary.equations.filter (isSplit415 root x intSlot) =
    [OpenTail414.openRow root x intSlot residual]

def ClosedRows.fields {s q} (a : ClosedRows s q) : List (Nat × Nat) :=
  [(a.x,a.intSlot),(a.y,a.strSlot)]

theorem closed_source_subtraction_exact415 {s q} (a : ClosedRows s q) :
    capture [a.x] a.fields = [(a.y,a.strSlot)] := by
  simp [ClosedRows.fields,CommonRoleCanonicalRows.capture,CommonRoleCanonicalRows.residual,
    CommonRoleCanonicalRows.normalize,Ne.symm a.different]

theorem residual_source_shape_retains_only_the_other_field415 {s q} (a : ClosedRows s q) :
    GeneralDeclarativeGraphRows321.shapeOf (wholeExpr a.x a.intSlot a.y a.strSlot) =
       some (.record a.fields) ∧
    GeneralDeclarativeGraphRows321.shapeOf (residualExpr a.y a.strSlot) =
       some (.record (capture [a.x] a.fields)) := by
  rw [closed_source_subtraction_exact415 a]
  simp [wholeExpr,residualExpr,ClosedRows.fields,GeneralDeclarativeGraphRows321.shapeOf,
    GeneralDeclarativeGraphRows321.fields,Ne.symm a.different]

theorem retained_concrete_residual_decreases415 {s q} (a : ClosedRows s q)
    (weight : Nat → Nat) (occurrences : Nat → Nat → Nat) :
    size weight [(a.y,a.strSlot)] < size weight a.fields ∧
    ∀ name, count (occurrences name) (CommonRoleCanonicalRows.normalize [(a.y,a.strSlot)]) ≤
      count (occurrences name) (CommonRoleCanonicalRows.normalize a.fields) := by
  have accept : check [a.x] = true := rfl
  have actualMatch : headMatches [a.x] a.fields = true := by
    simp [headMatches,ClosedRows.fields,CommonRoleCanonicalRows.normalize,
      CommonRoleCanonicalRows.lookup]
  simpa only [closed_source_subtraction_exact415 a] using
    checked_residual_decreases _ _ accept actualMatch weight occurrences

structure RowsWire where
  original : Nat
  whole : Nat
  intRow : Nat
  strRow : Nat
  residualRow : Nat
  splitRow : Nat

/-- Reads both concrete record rows independently and checks the exact
same retained root split. Neither a model nor a proposed captured tail
value is available to the function. -/
def readRows415 (p : Problem) (w : RowsWire) : Option (ClosedRows p.state p.root) := do
  let s := p.state.core
  let rows := s.current.ordinary.equations
  match seen : s.origins[w.original]? with
  | none => none
  | some o =>
    match term : o.endpoint with
    | .ordinary (.record x (.var intSlot) (.record y (.var strSlot) .emptyRecord)) =>
      match rows[w.residualRow]? with
      | none => none
      | some residual =>
        if eqs : rows[w.whole]? = some ⟨o.slot,wholeExpr x intSlot y strSlot⟩ ∧
            rows[w.intRow]? = some (OpenTail414.intRow intSlot) ∧
            rows[w.strRow]? = some (strRow strSlot) ∧
            rows[w.residualRow]? = some ⟨residual.left,residualExpr y strSlot⟩ ∧
            rows[w.splitRow]? = some (OpenTail414.openRow o.slot x intSlot residual.left) ∧
            rows.filter (isSplit415 o.slot x intSlot) = [OpenTail414.openRow o.slot x intSlot residual.left] then
          match args : p.root.demand.arguments with
          | [arg] =>
            if caps : arg.lower = o.slot ∧ arg.center = o.slot ∧ arg.upper = o.slot ∧
                p.root.demand.outputs = [] then
              if distinct : x ≠ y ∧ ([o.slot,intSlot,strSlot,residual.left] : List Nat).Nodup ∧
                  (s.origins.filter (fun src => src.slot == o.slot)).length = 1 then
                have pointEq : arg = GeneralDeclarativeWitnessDeclaredState357.point o.slot := by
                  cases arg
                  simp only [GeneralDeclarativeWitnessDeclaredState357.point]
                  congr
                  · exact caps.1
                  · exact caps.2.1
                  · exact caps.2.2.1
                some ⟨o.slot,x,intSlot,y,strSlot,residual.left,o,List.mem_of_getElem? seen,rfl,distinct.2.2,term,
                  args.trans (congrArg (fun a => [a]) pointEq),caps.2.2.2,distinct.1,distinct.2.1,
                  List.mem_of_getElem? eqs.1,List.mem_of_getElem? eqs.2.1,List.mem_of_getElem? eqs.2.2.1,
                  List.mem_of_getElem? eqs.2.2.2.1,List.mem_of_getElem? eqs.2.2.2.2.1,eqs.2.2.2.2.2⟩
              else none
            else none
          | _ => none
        else none
    | _ => none

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
