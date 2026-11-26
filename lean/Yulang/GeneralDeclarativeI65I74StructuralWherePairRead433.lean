import Yulang.GeneralDeclarativeI65I74StructuralWhereRootRead432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419
import Yulang.GeneralDeclarativeI65I74StructuralWhereSiblingReceipts433

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeWitnessLiteral349 (eqExpr)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

structure TwoNamedWrapWire433 where
  parentDeclaration : Nat
  parentHeadRow : Nat
  parentOutputRow : Nat
  parentEscape : List410.ExactEscapeWire
  first : ExplicitPick419.PickWire
  second : ExplicitPick419.PickWire

structure ReadTwoNamedWrap433 (p : Problem) where
  event : Event p.state p.root
  original : OriginalTwoNamedWhere433 event
  first : ExplicitPick419.PickPacket ⟨p.state,original.origin.child⟩
  second : ExplicitPick419.PickPacket
    ⟨p.state,⟨p.root.occurrence ++ [1],(event.frame.whereFor original.sibling).demand⟩⟩
  distinctRoles : original.origin.entry.demand.role ≠ original.sibling.role

/-- Independent data-only read of two selected literal named-output where children. The producer's original output
row must be the one used for the parent's output-only slot;
each child independently replays its literal, caller-derived request.
No selected event, report, model, or derived child input is supplied
in the witness. A failed read remains unsupported. -/
def readTwoNamedWrap433 (p : Problem) (w : TwoNamedWrapWire433) :
    Option (ReadTwoNamedWrap433 p) := do
  let root ← readProvisionalWrapFrame432 p
    ⟨w.parentDeclaration,w.parentHeadRow,w.first.outputRow,w.parentEscape⟩
  let s := p.state
  let q := p.root
  let f := root.frame
  let checked := root.declared.2 f.decl (List.mem_of_getElem? f.authored)
  match whereAt : f.decl.requirements, bindAt : f.decl.outputBinders,
      asked : q.demand.outputs with
  | [clause,sibling],[binder],[requested] =>
    match equationAt : clause.outputs, secondAt : sibling.outputs with
    | [equation],[siblingEquation] =>
      if rule : clause.arguments = [.var root.binder] ∧ clause.id = binder.clause ∧
          equation.id = binder.equation ∧ equation.rhs = .var binder.name ∧
          sibling.arguments = [.var root.binder] ∧ siblingEquation.rhs = .var binder.name ∧
          (f.whereFor clause).demand.role ≠ sibling.role then
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
                            rule.2.2.2.1,atChildOut,outputAt.2,
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
                        let original : OriginalTwoNamedWhere433 actual :=
                          ⟨root.declared,root.onlyVisible,root.safe,binder,by rw [bindAt]; exact List.mem_cons_self,
                            parentBody,origin,sibling,whereAt,rfl,root.binder,root.ctor,root.headLiteral,rule.1,
                            rule.2.2.2.2.1,siblingEquation,secondAt,rule.2.2.2.2.2.1,i,bodyAt,typedShape,
                            typed.param,typed.use,typed.mode,typed.table,typed.kind,typed.invariant,namesExact,retained⟩
                        let left ← ExplicitPick419.replayPick419 ⟨p.state,original.origin.child⟩ w.first
                        let right ← ExplicitPick419.replayPick419
                          ⟨p.state,⟨q.occurrence ++ [1],(f.whereFor sibling).demand⟩⟩ w.second
                        pure ⟨actual,original,left,right,rule.2.2.2.2.2.2⟩
                      else none
                  else none
              else none
            else none
          | _ => none
        else none
      else none
    | _,_ => none
  | _,_,_ => none

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
