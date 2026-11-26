import Yulang.GeneralDeclarativeI65I74StructuralWhereRootRead432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

structure AssociatedWire432 where
  parentDeclaration : Nat
  parentHeadRow : Nat
  parentOutputRow : Nat
  parentEscape : List410.ExactEscapeWire
  child : ExplicitPick419.PickWire

structure ReadAssociatedWrap432 (p : Problem) where
  event : Event p.state p.root
  original : OriginalAssociatedWrap432 event
  child : ExplicitPick419.PickPacket ⟨p.state,original.origin.child⟩

/-- Data-only narrow Wrap/Container read. The child's original output
row must be the one used for the parent's output-only slot, and the
child independently checks the real caller-derived Request there.
No selected event, report, model, or derived child input is supplied
in the witness. A failed read remains unsupported. -/
def readAssociatedWrap432 (p : Problem) (w : AssociatedWire432) :
    Option (ReadAssociatedWrap432 p) := do
  let root ← readProvisionalWrapFrame432 p
    ⟨w.parentDeclaration,w.parentHeadRow,w.child.outputRow,w.parentEscape⟩
  let s := p.state
  let q := p.root
  let f := root.frame
  let checked := root.declared.2 f.decl (List.mem_of_getElem? f.authored)
  match whereAt : f.decl.requirements, bindAt : f.decl.outputBinders,
      asked : q.demand.outputs with
  | [clause],[binder],[requested] =>
    match equationAt : clause.outputs with
    | [equation] =>
      if rule : clause.arguments = [.var root.binder] ∧ clause.id = binder.clause ∧
          equation.id = binder.equation ∧ equation.rhs = .var binder.name then
        if fresh : root.childTarget ≠ requested.target then
          have outputLen : q.demand.outputs.length = 1 := by
            exact congrArg List.length asked
          let i : Fin q.demand.outputs.length := ⟨0,by rw [outputLen]; decide⟩
          let out ← readOriginalOutput432 s f checked i w.parentOutputRow
          match bodyAt : out.output.body with
          | .explicit parentBody =>
            if typedShape : normalize (bodyPattern out.output.body) =
                .app root.ctor [.var binder.name] then
              let candidate := cast (congrArg (B6MixedRhs401 s.core false) typedShape) out.output.plan
              let typed ← readInvariantUnary432 candidate
              if originalCode : eqExpr out.code (.nominal root.ctor [.variable root.childTarget]) = true then
                let entry := f.whereFor clause
                match atChildOut : entry.demand.outputs[0]? with
                | none => none
                | some item =>
                  if outputAt : item.target = root.childTarget ∧ item.name = equation.name then
                    match atSlot : f.slots (.explicit parentBody) binder.name with
                    | none => none
                    | some slot =>
                      if pointAt : slot.lower = item.target ∧ slot.center = item.target ∧
                          slot.upper = item.target then
                        have slotProper : slot = point (GeneralSourceState.Output.target item) := by
                          cases slot with
                          | mk lo center hi =>
                            obtain ⟨a,b,c⟩ := pointAt
                            cases a; cases b; cases c; rfl
                        let origin : OriginalWhereBinder395 f binder parentBody :=
                          ⟨0,0,entry,equation,item,by simp [entry,AuthoredBodyFrame393.clauses,whereAt],
                            rule.2.1,by simp [entry,AuthoredBodyFrame393.whereFor,equationAt],rule.2.2.1,
                            rule.2.2.2,atChildOut,outputAt.2,
                            atSlot.trans (congrArg some slotProper)⟩
                        let actual : Event s q :=
                          ⟨f,root.head,fun j => (show i = j from Fin.eq_of_val_eq (by
                            have limit : j.val < 1 :=
                              Eq.mp (congrArg (fun n : Nat => j.val < n) outputLen) j.isLt
                            change 0 = j.val
                            omega)) ▸ out.output⟩
                        have namesExact : HEq out.output.plan
                            (invariantUnaryValuePlan432 root.ctor binder.name typed.param
                              typed.use typed.mode typed.table typed.kind typed.invariant) :=
                          (cast_heq _ _).symm.trans typed.exactPlan
                        have retained : RetainedTypedValueRows403 actual := by
                          intro j
                          have same : j = i := Fin.eq_of_val_eq (by
                            have limit : j.val < 1 :=
                              Eq.mp (congrArg (fun n : Nat => j.val < n) outputLen) j.isLt
                            change j.val = 0
                            omega)
                          subst j
                          exact ⟨out.code,out.valueCode,List.mem_of_getElem? out.row⟩
                        let original : OriginalAssociatedWrap432 actual :=
                          ⟨root.declared,root.onlyVisible,root.safe,root.binder,root.ctor,point root.inputPoint,
                            root.demandPoint,root.headLiteral,root.sameCapture,binder,by rw [bindAt]; exact List.mem_cons_self,
                            parentBody,origin,whereAt,rule.1,outputLen,i,bodyAt,typedShape,
                            typed.param,typed.use,typed.mode,typed.table,typed.kind,typed.invariant,
                            namesExact,retained⟩
                        let selected ← ExplicitPick419.replayPick419 ⟨p.state,original.origin.child⟩ w.child
                        pure ⟨actual,original,selected⟩
                      else none
                  else none
              else none
            else none
          | _ => none
        else none
      else none
    | _ => none
  | _,_,_ => none

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
