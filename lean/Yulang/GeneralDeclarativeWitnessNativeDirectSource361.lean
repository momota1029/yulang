import Yulang.GeneralDeclarativeWitnessSequentialNative360
import Yulang.GeneralDeclarativeWitnessNativeReceiver360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeDirectSource361
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativeValue360 (Address)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarationPatterns (Pattern normalize variablesArgs)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessReleasedForward360 (forwardKey forwardDemand)
open GeneralDeclarativeWitnessNativeReceiver360 (key)

structure Wire where
  child : FrameKey
  headPosition : Nat
  binder : Nat
  clausePosition : Nat
  clauseId : Nat
  operandPosition : Nat

/-- Literal source lineage for a fresh child which forwards exactly one
bare binder of a released point input. This reads neither the compiler
result nor any proposed type/value assignment. It is not election. -/
structure Direct (env : Environment) (parent : FrameKey) (d : Demand) (address : Address) (w : Wire) where
  impl : Declaration
  receiver : Declaration
  row : Clause
  seed : Capture
  operand : Pattern
  source : env.source.declarations[parent.sourceOrdinal]? = some impl
  targetSource : env.source.declarations[w.child.sourceOrdinal]? = some receiver
  actualRow : impl.requirements[w.clausePosition]? = some row
  argument : d.arguments[w.headPosition]? = some seed
  actualOperand : row.arguments[w.operandPosition]? = some operand
  parentIdentity : impl.id = parent.declaration ∧ impl.role = d.role
  childIdentity : receiver.id = w.child.declaration ∧ receiver.role = row.role
  ownerPath : w.child.occurrence = parent.occurrence ++ [w.clausePosition]
  sourceId : row.id = w.clauseId
  parentHead : (impl.head[w.headPosition]?).map normalize = some (.var w.binder)
  onlyUse : (variablesArgs (impl.head.map normalize)).count w.binder = 1
  childInput : normalize operand = .var w.binder
  seedPoint : seed.lower = address.target ∧ seed.center = address.target ∧ seed.upper = address.target
  checkedParent : checkDecl env impl = true
  checkedChild : checkDecl env receiver = true

def sourceRoute (env : Environment) (parent : FrameKey) (d : Demand) (address : Address) (w : Wire) :
    Option (Direct env parent d address w) :=
  match h : env.source.declarations[parent.sourceOrdinal]?, child : env.source.declarations[w.child.sourceOrdinal]? with
  | some impl,some receiver =>
    match row : impl.requirements[w.clausePosition]?, arg : d.arguments[w.headPosition]? with
    | some clause,some seed =>
      match operand : clause.arguments[w.operandPosition]? with
      | none => none
      | some pat =>
        if p : impl.id = parent.declaration ∧ impl.role = d.role then
          if c : receiver.id = w.child.declaration ∧ receiver.role = clause.role then
            if path : w.child.occurrence = parent.occurrence ++ [w.clausePosition] then
              if id : clause.id = w.clauseId then
                if a : (impl.head[w.headPosition]?).map normalize = some (.var w.binder) then
                  if unique : (variablesArgs (impl.head.map normalize)).count w.binder = 1 then
                    if direct : normalize pat = .var w.binder then
                      if center : seed.lower = address.target ∧ seed.center = address.target ∧ seed.upper = address.target then
                        if checked : checkDecl env impl && checkDecl env receiver then
                          have checks := Bool.and_eq_true_iff.mp checked
                          some ⟨impl,receiver,clause,seed,pat,h,child,row,arg,operand,p,c,path,id,a,unique,direct,center,checks.1,checks.2⟩
                        else none
                      else none
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
    | _,_ => none
  | _,_ => none

theorem same_actual_source {env parent d addr w l} (a : Direct env parent d addr w)
    (p : Prepared env parent d l) : p.impl = a.impl :=
  Option.some.inj (p.authored.symm.trans a.source)

theorem literal_source_not_guessed {env parent d addr w} (a : Direct env parent d addr w) :
    ∃ impl clause pat input,
      env.source.declarations[parent.sourceOrdinal]? = some impl ∧
      impl.requirements[w.clausePosition]? = some clause ∧
      clause.id = w.clauseId ∧ clause.arguments[w.operandPosition]? = some pat ∧
      normalize pat = .var w.binder ∧
      (impl.head[w.headPosition]?).map normalize = some (.var w.binder) ∧
      d.arguments[w.headPosition]? = some input ∧ input.lower = addr.target ∧
      w.child.occurrence = parent.occurrence ++ [w.clausePosition] :=
  ⟨a.impl,a.row,a.operand,a.seed,a.source,a.actualRow,a.sourceId,a.actualOperand,
    a.childInput,a.parentHead,a.argument,a.seedPoint.1,a.ownerPath⟩

def actualWire : Wire := ⟨key,0,90,0,181,0⟩

open GeneralDeclarativeWitnessCompiler350 (portNames placed)
open GeneralDeclarativeWitnessNativePreparation360 (context)
open GeneralDeclarativeSourceEmission322 (useArg exact_at source_var)

theorem actual_compiler_position {env parent d addr w l} (a : Direct env parent d addr w)
    (p : Prepared env parent d l) :
    (p.kids[w.clausePosition]?).bind (fun child => child.arguments[w.operandPosition]?) =
      some ((portNames (context env d p.impl l) p.ports).input w.binder) := by
  let names := portNames (context env d p.impl l) p.ports
  let place := placed (context env d p.impl l) p.ports
  have aRow : p.impl.requirements[w.clausePosition]? = some a.row := by rw [same_actual_source a p]; exact a.actualRow
  have atPos : p.kids[w.clausePosition]? =
      some (GeneralDeclarativeSourceEmission322.demand p.impl a.row names (place.compound a.row) (place.targets a.row)) := by
    simp [Prepared.kids,GeneralDeclarativeEmissionForest322.children,names,place,aRow]
  rw [atPos]
  change (GeneralDeclarativeSourceEmission322.inputs names (place.compound a.row) 0 a.row.arguments)[w.operandPosition]? = _
  rw [exact_at names (place.compound a.row) 0 a.row.arguments w.operandPosition a.actualOperand,source_var names _ _ a.childInput]

end Yulang.GeneralDeclarativeWitnessNativeDirectSource361
