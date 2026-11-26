import Yulang.GeneralDeclarativeI65I74StructuralWhereOutputRead432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere427
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeHead320 (Equation Read)
open GeneralDeclarativeBounds319 (Bound)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure RootWire432 where
  declOrdinal : Nat
  rootRow : Nat
  childRetainedRow : Nat
  escape : ExactEscapeWire

/-- A checked pre-output frame. The where output position is a
candidate retained physical address, not an allocator decision or
a proof of successful selection. It still has to be validated with
the literal child's typed output and the parent's B6 plan. -/
structure ProvisionalWrapFrame432 (p : Problem) where
  frame : AuthoredBodyFrame393 p.state.core p.root
  declared : Checked (authoredRegistry p.state.core.current)
  onlyVisible : visible p.state.core p.root = [frame.decl]
  head : SourceHead p.state.core p.root frame.decl
  sameCapture : positiveCaptureOf427 head = some frame.input
  safe : ¬ RootCycle p.state p.root
  ctor : Nat
  binder : Nat
  headLiteral : frame.decl.head = [.app ctor [.var binder]]
  inputPoint : Nat
  demandPoint : p.root.demand.arguments = [point inputPoint]
  childTarget : Nat
  childAddress : Nat
  childOnRootState : ∃ eqn : Equation,
    p.state.core.current.ordinary.equations[childAddress]? = some eqn ∧ eqn.left = childTarget

private def captureFromRoot432 (binder payload : Nat) (n : Nat) : Capture :=
  if n = binder then point payload else point 0

private def scopedRetainedPlacement432 (target : Nat) : Placement :=
  ⟨fun _ _ => point 0, fun _ _ => target⟩

/-- The narrow invariant unary authored head lane reads the actual
ordinary graph at its demanded original root and is independent of
where and output completion. This is not a classifier or a statement
about a different leaf-only view of the declaration. -/
def readProvisionalWrapFrame432 (p : Problem) (w : RootWire432) :
    Option (ProvisionalWrapFrame432 p) := do
  let s := p.state.core
  let registry := authoredRegistry s.current
  let interp := GeneralSourceMetadataRows291.interpretation s.current.environment.source.snapshot
  if covers : GeneralSourceMetadataDeclarations291.explicitCheck registry interp = true then
    if header : GeneralDeclarativeWitnessHeader349.checkedRegistry s.current.environment.source = true then
      let covered := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp covers
      have checked : Checked registry := by
        have info := GeneralDeclarativeWitnessProblem349.splitAnd header
        exact ⟨of_decide_eq_true info.1,fun d found =>
          GeneralDeclarativeWitnessHeader349.decl_checked (covered d found)
            (List.all_eq_true.mp info.2 d found)⟩
      match atDecl : registry.declarations[w.declOrdinal]? with
      | none => none
      | some d =>
        if only : visible s p.root = [d] then
          match head : d.head, asked : p.root.demand.arguments with
          | [.app key [.var binder]], [arg] =>
            match rowAt : s.current.ordinary.equations[w.rootRow]? with
            | none => none
            | some row =>
              match rowCode : row.right with
              | .nominal rowKey [.variable payload] =>
                if same : rowKey = key ∧ arg.lower = row.left ∧ arg.center = row.left ∧ arg.upper = row.left then
                  if ok : checkExactEscape s.current.ordinary row.left w.escape = true then
                    match codeAt : translate registry.constructors interp (.app key [.var binder]) with
                    | none => none
                    | some code =>
                      if literal : eqExpr code (.nominal key [.variable binder]) = true then
                        match childAt : s.current.ordinary.equations[w.childRetainedRow]? with
                        | none => none
                        | some child =>
                          let capture := captureFromRoot432 binder payload
                          let frame : AuthoredBodyFrame393 s p.root :=
                            ⟨w.declOrdinal,d,atDecl,by simp [only],
                              scopedRetainedPlacement432 child.left,capture⟩
                          have actualPoint : arg = point row.left := by
                            cases arg with
                            | mk l c u =>
                              have centerFacts : l = row.left ∧ c = row.left ∧ u = row.left := same.2
                              obtain ⟨hl,hc,hu⟩ := centerFacts
                              simp [point,hl,hc,hu]
                          have actualRow : (⟨row.left,.nominal key [.variable payload]⟩ : Equation)
                              ∈ s.current.ordinary.equations := by
                            have before := List.mem_of_getElem? rowAt
                            have equality : row = ⟨row.left,.nominal key [.variable payload]⟩ := by
                              cases row
                              exact congrArg (Equation.mk _) (rowCode.trans (congrArg
                                (fun k => Expr.nominal k [.variable payload]) same.1))
                            exact equality ▸ before
                          have actualRead : Read s.current.ordinary capture .actual row.left
                              (.nominal key [.variable binder]) := by
                            apply Read.nominal (n:=1) (fun _ => payload) (fun _ => .variable binder)
                            · exact actualRow
                            · intro _
                              have pointCaptured : capture binder = point payload := by
                                simp [capture,captureFromRoot432]
                              apply Read.capture <;>
                                (change Bound s.current.ordinary.normal _ _; rw [pointCaptured]; exact .refl _)
                          let chosen : SourceHead s p.root d := by
                            refine .ordered capture ?_
                            rw [head,asked,actualPoint]
                            refine .cons (.ordinary ⟨⟨.refl _,.refl _⟩,
                              .nominal key [.variable binder],?_,.direct (.structural actualRead)⟩) .nil
                            exact codeAt.trans (congrArg some ((eq_expr ..).mp literal))
                          have noCycle : ¬ RootCycle p.state p.root := by
                            rintro ⟨a,mem,cycle⟩
                            rw [asked,actualPoint] at mem
                            cases List.mem_singleton.mp mem
                            exact exact_escape_refutes_raw_root_K2410 ok cycle
                          pure ⟨frame,checked,only,chosen,rfl,noCycle,key,binder,head,row.left,
                            asked.trans (congrArg (fun a => [a]) actualPoint),child.left,w.childRetainedRow,
                            ⟨child,childAt,rfl⟩⟩
                      else none
                  else none
                else none
              | _ => none
          | _,_ => none
        else none
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
