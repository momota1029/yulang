import Yulang.GeneralDeclarativeI65I74MergedOutputSource439
import Yulang.GeneralDeclarativeI65I74ExactEscape410
import Yulang.GeneralDeclarativeI65I74MergedOutputHeader439

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarativeI65
open GeneralDeclarations (Clause Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute preparation whereBatch placed
  printDemand print_injective map_injective)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr sameRows rows_exact)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure Wire439 where
  originalInput : Nat
  rootEscape : ExactEscapeWire

private def captureKey (a : Capture) : Nat × Nat × Nat := (a.lower,a.center,a.upper)
private theorem capture_eq (a b : Capture) : captureKey a = captureKey b ↔ a = b := by
  cases a
  cases b
  simp [captureKey]

local instance : DecidableEq Capture :=
  fun a b => decidable_of_iff (captureKey a = captureKey b) (capture_eq a b)

def printRequest (q : Request) : List Nat × Nat × List (Nat × Nat × Nat) × List (Nat × Nat) := (q.occurrence,printDemand q.demand)

theorem print_request_injective439 {a b : Request} (h : printRequest a = printRequest b) : a = b := by
  cases a
  cases b
  simp only [printRequest,Prod.mk.injEq] at h
  obtain ⟨rfl,codes⟩ := h
  cases print_injective codes
  rfl

def requestListEq : List Request → List Request → Bool
  | [],[] => true
  | a::as,b::bs =>
    decide (a.occurrence = b.occurrence) &&
      decide (printDemand a.demand = printDemand b.demand) && requestListEq as bs
  | _,_ => false

theorem request_list_eq439 {a b : List Request} (h : requestListEq a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [requestListEq]
  | cons a as ih =>
    cases b with
    | nil => cases h
    | cons b bs =>
      have ⟨one,t⟩ := GeneralDeclarativeWitnessProblem349.splitAnd h
      have ⟨origin,demand⟩ := GeneralDeclarativeWitnessProblem349.splitAnd one
      have head : a = b := print_request_injective439 (by
        exact Prod.ext (of_decide_eq_true origin) (of_decide_eq_true demand))
      rw [head,ih t]

private def readsCode (e : Option Expr) (code : Expr) : Bool :=
  match e with
  | none => false
  | some c => eqExpr c code

private theorem reads_code {e code} (h : readsCode e code = true) : e = some code := by
  cases e with
  | none => cases h
  | some c => exact congrArg some ((eq_expr ..).mp h)

private theorem row_from_code (e : Equation) {code} (h : eqExpr e.right code = true) :
    e = ⟨e.left,code⟩ :=
  congrArg (Equation.mk e.left) ((eq_expr ..).mp h)

private def noCapture : Nat → Capture := fun _ => point 0

private def scalarSource {s : I72.State} {q : Request} {d : Declaration}
    {a : Capture} {key slot : Nat}
    (args : q.demand.arguments = [a]) (head : d.head = [.app key []])
    (pointAt : a = point slot)
    (translation : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot) (.app key []) = some intCode)
    (read : (⟨slot,intCode⟩ : Equation) ∈ s.core.current.ordinary.equations) :
    SourceHead s.core q d := by
  refine .ordered noCapture ?_
  rw [args,head,pointAt]
  exact .cons (.ordinary ⟨⟨.refl slot,.refl slot⟩,intCode,translation,.direct (.whole read)⟩) .nil

private theorem rootSafe {s : I72.State} {q : Request} {slot : Nat}
    (args : q.demand.arguments = [point slot]) (w : ExactEscapeWire)
    (safe : checkExactEscape s.core.current.ordinary slot w = true) : ¬ RootCycle s q := by
  rintro ⟨a,found,bad⟩
  rw [args] at found
  obtain rfl := List.mem_singleton.mp found
  exact exact_escape_refutes_raw_root_K2410 safe bad

structure SourceInput439 (s : I72.State) (q : Request) where
  parent : Declaration
  parentVisible : visible s.core q = [parent]
  checked : Checked (authoredRegistry s.core.current)
  ordinal : Nat
  exactOrdinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 = some ordinal
  book : (authoredRegistry s.core.current).declarations[ordinal]? = some parent
  key : Nat
  parentSyntax : parent.head = [.app key []]
  root : Nat
  originalArgs : q.demand.arguments = [point root]
  rootOutputEmpty : q.demand.outputs = []
  sourceHead : SourceHead s.core q parent
  rootSafe : ¬ RootCycle s q
  input : Origin
  issuer : input.issuer = q.occurrence
  inputSlot : input.slot = root
  inputType : input.endpoint = .ordinary (.base .int)
  inputSeen : input ∈ s.core.origins
  leftCell : Nat
  rightCell : Nat
  distinctCells : leftCell ≠ rightCell
  rootLeftDistinct : root ≠ leftCell
  rootRightDistinct : root ≠ rightCell
  originalRows : s.core.current.ordinary.equations =
    [⟨root,intCode⟩,⟨leftCell,intCode⟩,⟨rightCell,tickCode⟩]

private def readSourceInput439 (s : I72.State) (q : Request) (w : Wire439) :
    Option (SourceInput439 s q) := do
  let registry := authoredRegistry s.core.current
  let raw := s.core.current.ordinary
  if header : checkHeader439 s.core.current.environment = true then
    if rootEmpty : q.demand.outputs = [] then
      match actual : visible s.core q, args : q.demand.arguments, rows : raw.equations with
      | [d],[arg],[root,left,right] =>
        match head : d.head, source : s.core.origins[w.originalInput]? with
        | [.app key []],some o =>
          match inputTy : o.endpoint with
          | .ordinary (.base .int) =>
            if inputAt : arg = point root.left ∧ o.issuer = q.occurrence ∧ o.slot = root.left then
              if operands : eqExpr root.right intCode = true ∧ eqExpr left.right intCode = true ∧
                  eqExpr right.right tickCode = true ∧ left.left ≠ right.left ∧
                  root.left ≠ left.left ∧ root.left ≠ right.left then
                if escape : checkExactEscape raw root.left w.rootEscape = true then
                  let tr := translate registry.constructors
                    (interpretation s.core.current.environment.source.snapshot) (.app key [])
                  if hasTranslation : readsCode tr intCode = true then
                    match readOrdinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
                        registry.declarations 0 with
                    | none => none
                    | some ordinal =>
                      if atBook : registry.declarations[ordinal]? = some d then
                        have rootRow := row_from_code root operands.1
                        have leftRow := row_from_code left operands.2.1
                        have rightRow := row_from_code right operands.2.2.1
                        have exactRows : raw.equations =
                          [⟨root.left,intCode⟩,⟨left.left,intCode⟩,⟨right.left,tickCode⟩] := by
                          calc
                            raw.equations = [root,left,right] := rows
                            _ = _ := by rw [rootRow,leftRow,rightRow]
                        have original : q.demand.arguments = [point root.left] := args.trans
                          (congrArg (fun x => [x]) inputAt.1)
                        let readHead : SourceHead s.core q d :=
                          scalarSource args head inputAt.1 (reads_code hasTranslation)
                            (by rw [exactRows]; exact List.mem_cons_self)
                        return ⟨d,actual,(checked_header439 (s := s.core.current) header).1,
                          ordinal,readOrdinal,atBook,key,head,root.left,original,rootEmpty,readHead,
                          rootSafe original w.rootEscape escape,o,inputAt.2.1,inputAt.2.2,inputTy,
                          List.mem_of_getElem? source,left.left,right.left,operands.2.2.2.1,
                          operands.2.2.2.2.1,operands.2.2.2.2.2,exactRows⟩
                      else none
                  else none
                else none
              else none
            else none
          | _ => none
        | _,_ => none
      | _,_,_ => none
    else none
  else none

private def mergeContext {s q} (src : SourceInput439 s q) (first : Clause) : Context :=
  ⟨authoredRegistry s.core.current,interpretation s.core.current.environment.source.snapshot,
    q.demand,src.parent,s.core.current.ordinary,[],[],noCapture,
    fun cl _ => if cl.id = first.id then src.leftCell else src.rightCell⟩

/-- Shape and addresses are obtained from the whole authoritative
book and recorded ordinary rows; neither candidate list, expected
result nor requested output-slot names are supplied by the wire. -/
def replay439 (s : I72.State) (q : Request) (w : Wire439) : Option (Original439 s q) := do
  let actual ← readSourceInput439 s q w
  let registry := authoredRegistry s.core.current
  let interp := interpretation s.core.current.environment.source.snapshot
  match requirements : actual.parent.requirements with
  | [first,last] =>
    match firstOut : first.outputs, lastOut : last.outputs with
    | [left],[right] =>
      if original : first.id ≠ last.id ∧ last.role = first.role ∧ first.arguments = [] ∧
          last.arguments = [] ∧ right.name = left.name ∧ left.rhs = .app actual.key [] ∧
          right.rhs = .variant 0 (.app actual.key []) then
        if firstCode : readsCode (translate registry.constructors interp left.rhs) intCode = true then
          if lastCode : readsCode (translate registry.constructors interp right.rhs) tickCode = true then
            let child : Request := ⟨q.occurrence ++ [0],⟨first.role,[],[⟨left.name,actual.leftCell⟩]⟩⟩
            let next : Request := ⟨q.occurrence ++ [1],⟨first.role,[],[⟨left.name,actual.rightCell⟩]⟩⟩
            match leafAt : visible s.core child with
            | [leaf] =>
              match leafOut : leaf.associated with
              | [e] =>
                if leafShape : leaf.head = [] ∧ leaf.requirements = [] ∧
                    e.name = left.name ∧ e.rhs = .app actual.key [] then
                  let c := mergeContext actual first
                  match prep : preparation c with
                  | none => none
                  | some (before,ports) =>
                    match compiled : whereBatch c ports with
                    | none => none
                    | some rows =>
                      if rowsAt : sameRows [⟨actual.leftCell,intCode⟩,⟨actual.rightCell,tickCode⟩] rows = true then
                        let placement := placed c ports
                        let frame := frameAtSource395 (by rw [actual.parentVisible]; exact List.mem_cons_self)
                          actual.ordinal actual.book placement noCapture
                        if sourceKids : requestListEq (frameWhereKids400 frame) [child,next] = true then
                          match ran : execute c with
                          | none => none
                          | some done =>
                            if compilerKids : requestListEq (children q done.kids) (frameWhereKids400 frame) = true then
                              if noWrites : done.fixed.isEmpty = true then
                                let conflicts : Original439 s q := {
                                  frame := frame
                                  sourceHead := actual.sourceHead
                                  checked := actual.checked
                                  oneParent := actual.parentVisible
                                  safe := actual.rootSafe
                                  key := actual.key
                                  sourceHeadSyntax := actual.parentSyntax
                                  firstClause := first
                                  lastClause := last
                                  originalClauses := requirements
                                  distinctClauses := original.1
                                  childRole := first.role
                                  outName := left.name
                                  firstEquation := left
                                  lastEquation := right
                                  firstRole := rfl
                                  lastRole := original.2.1
                                  firstArgs := original.2.2.1
                                  lastArgs := original.2.2.2.1
                                  firstOutput := firstOut
                                  lastOutput := lastOut
                                  firstName := rfl
                                  lastName := original.2.2.2.2.1
                                  firstRhs := original.2.2.2.2.2.1
                                  lastRhs := original.2.2.2.2.2.2
                                  firstCode := reads_code firstCode
                                  lastCode := reads_code lastCode
                                  rootCell := actual.root
                                  originalRootArgs := actual.originalArgs
                                  leftCell := actual.leftCell
                                  rightCell := actual.rightCell
                                  distinctCells := actual.distinctCells
                                  rootLeftDistinct := actual.rootLeftDistinct
                                  rootRightDistinct := actual.rootRightDistinct
                                  leftKept := by rw [actual.originalRows]; exact List.mem_cons_of_mem _ List.mem_cons_self
                                  rightKept := by
                                    rw [actual.originalRows]
                                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
                                  exactKids := request_list_eq439 sourceKids
                                  compiler := c
                                  compilerDeclaration := rfl
                                  compilerRequest := rfl
                                  compilerRegistry := rfl
                                  compilerInterpretation := rfl
                                  compilerState := rfl
                                  prepared := before
                                  ports := ports
                                  preparedExact := prep
                                  originalPlacement := rfl
                                  emittedExact := compiled.trans (congrArg some ((rows_exact _ _).mp rowsAt))
                                  finished := done
                                  executed := ran
                                  compilerKids := request_list_eq439 compilerKids
                                  compilerNoFixed := List.isEmpty_iff.mp noWrites
                                  leaf := leaf
                                  oneLeaf := leafAt
                                  leafHead := leafShape.1
                                  leafWhere := leafShape.2.1
                                  leafEquation := e
                                  leafBody := leafOut
                                  leafName := leafShape.2.2.1
                                  leafRhs := leafShape.2.2.2
                                }
                                return conflicts
                              else none
                            else none
                        else none
                      else none
                else none
              | _ => none
            | _ => none
          else none
        else none
      else none
    | _,_ => none
  | _ => none

end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
