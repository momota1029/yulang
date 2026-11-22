import Yulang.GeneralDeclarativeWitnessMixedScope356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPayloadRoute356
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessRangeCut355 (bare_scope selected_center)
open GeneralDeclarativeWitnessCompiler350 (portNames placed)
open GeneralDeclarativeSourceEmission322 (demand)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarations (Clause)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def clauseDemand {s : State} (p : Node s) (c : Clause) : Demand :=
  demand p.proof.compiled.readFrom.ctx.decl c (portNames p.proof.compiled.readFrom.ctx p.proof.compiled.ports)
    ((placed p.proof.compiled.readFrom.ctx p.proof.compiled.ports).compound c)
    ((placed p.proof.compiled.readFrom.ctx p.proof.compiled.ports).targets c)

structure Route {s : State} (p : Node s) (idx : Nat) (observed : Demand) where
  clause : Clause
  atClause : p.proof.compiled.readFrom.center.decl.requirements[idx]? = some clause
  atDemand : p.proof.compiled.children[idx]? = some observed
  literal : observed = clauseDemand p clause
  binder : Nat
  args : clause.arguments = [.var binder]
  input : binder ∈ p.proof.compiled.readFrom.center.decl.inputNames
  noOutput : binder ∉ p.proof.compiled.readFrom.center.decl.outputNames

/-- A real written where argument from the selected merged Box payload.
It is not a write or a type conversion of the fixed nominal result. -/
def read {s : State} (p : Node s) (idx : Nat) (observed : Demand)
    (clauseId name : Nat) : Option (Route p idx observed) :=
  match at_ : p.proof.compiled.readFrom.center.decl.requirements[idx]? with
  | none => none
  | some c =>
    if _ : c.id = clauseId then
      if args : c.arguments = [.var name] then
        if eq : GeneralDeclarativeWitnessCompiler350.printDemand observed =
            GeneralDeclarativeWitnessCompiler350.printDemand (clauseDemand p c) then
          let printed := GeneralDeclarativeWitnessCompiler350.print_injective eq
          let scope := bare_scope p.proof.compiled.readFrom.center.good (List.mem_of_getElem? at_) args
          let got : p.proof.compiled.children[idx]? = some observed := by
            unfold GeneralDeclarativeWitnessTypedRangeWriter354.Run.children GeneralDeclarativeEmissionForest322.children
            rw [List.getElem?_map]
            change (p.proof.compiled.readFrom.center.decl.requirements[idx]?).map _ = _
            rw [at_,printed]
            rfl
          some ⟨c,at_,got,printed,name,args,scope.1,scope.2⟩
        else none
      else none
    else none

theorem argument_is_projected_payload {s : State} {p : Node s} {idx d} (a : Route p idx d) :
    ∃ cap : Capture, d.arguments = [cap] ∧ cap.center = p.valueName := by
  refine ⟨(portNames p.proof.compiled.readFrom.ctx p.proof.compiled.ports).input a.binder,?_,
    selected_center p.proof.compiled a.input a.noOutput⟩
  refine (congrArg Demand.arguments a.literal).trans ?_
  simp [clauseDemand,demand,GeneralDeclarativeSourceEmission322.inputs,
    GeneralDeclarativeSourceEmission322.useArg,a.args,GeneralDeclarationPatterns.normalize]

theorem ordinary_payload_law {s : State} {p : Node s} {idx d} (a : Route p idx d)
    (m : Assignment) (fit : Models s m) :
    ∃ cap, d.arguments = [cap] ∧ cap.center = p.valueName ∧
    Equivalent (m cap.center).1
      (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
              (m p.proof.compiled.readFrom.center.anchor.last.valueName).1) := by
  obtain ⟨cap,actual,phys⟩ := argument_is_projected_payload a
  have whole := GeneralDeclarativeWitnessCovariantOrigin353.whole_full p.proof.compiled.readFrom.center.anchor m
    (GeneralDeclarativeGrowth327.restrict
      ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp p.proof.kept) m fit)
  exact ⟨cap,actual,phys,phys.symm ▸ whole⟩

end Yulang.GeneralDeclarativeWitnessPayloadRoute356
