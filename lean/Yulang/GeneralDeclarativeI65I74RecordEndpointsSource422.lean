import Yulang.GeneralDeclarativeI65I74RepeatedCentersDiagnostics421
import Yulang.GeneralDeclarativeEndpointRecord336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open ExplicitPick419 (pickSyntax pickCode)
open OpenTail414 (openRow openTerm)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

/-- The two endpoint observations are independently attached to the
original requested root slots; this never reads a center source row. -/
structure AuthoredRecord (s : I72.State) (slot : Nat) where
  original : Origin
  owned : original ∈ s.core.origins
  slotEq : original.slot = slot
  label : Nat
  field : Nat
  residual : Nat
  writtenForm : original.endpoint = openTerm label field residual
  row : openRow slot label field residual ∈ s.core.current.ordinary.equations

structure Locator where
  origin : Nat
  row : Nat

def readAuthoredRecord (s : I72.State) (slot : Nat) (w : Locator) :
    Option (AuthoredRecord s slot) := do
  match known : s.core.origins[w.origin]? with
  | some o =>
    match form : o.endpoint with
    | .ordinary (.record label (.var field) (.var residual)) =>
      match present : s.core.current.ordinary.equations[w.row]? with
      | some e =>
        if h : o.slot = slot ∧ e.left = slot ∧
            eqExpr e.right (.record label (.variable field) (.variable residual)) = true then
          have exact : e = openRow slot label field residual := by
            cases e
            congr
            · exact h.2.1
            · exact (eq_expr _ _).mp h.2.2
          pure ⟨o,List.mem_of_getElem? known,h.1,label,field,residual,form,
            exact ▸ List.mem_of_getElem? present⟩
        else none
      | none => none
    | _ => none
  | none => none

/-- The original request and literal Pick clause are matched on the
authored endpoints only. Nothing here asserts that the fixed kernel
can turn these genuine nonpoint projections into its old Center proof. -/
structure Read (p : Problem) where
  arg : Capture
  request : p.root.demand.arguments = [arg]
  ranged : GeneralDeclarativeDemand320.Bounds p.state.core.current.ordinary arg
  endpointsApart : arg.lower ≠ arg.upper
  low : AuthoredRecord p.state arg.lower
  high : AuthoredRecord p.state arg.upper
  sameLabel : high.label = low.label
  decl : Declaration
  only : visible p.state.core p.root = [decl]
  ordinal : Nat
  actualDecl : (authoredRegistry p.state.core.current).declarations[ordinal]? = some decl
  checked : Checked (authoredRegistry p.state.core.current)
  fieldBinder : Nat
  residualBinder : Nat
  distinct : fieldBinder ≠ residualBinder
  literal : decl.head = [pickSyntax low.label fieldBinder residualBinder]
  noWhere : decl.requirements = []
  noOutBinders : decl.outputBinders = []
  assoc : GeneralDeclarations.Equation
  actualAssoc : decl.associated = [assoc]
  assocRhs : assoc.rhs = .var fieldBinder
  exactOut : p.root.demand.outputs.length = 1
  outputName : p.root.demand.outputs[ExplicitPick419.exactlyOneOutput p exactOut].name = assoc.name
  rawSafe : ¬ RootCycle p.state p.root

structure Wire where
  low : Locator
  high : Locator
  selected : Nat
  escape : ExactEscapeWire

def readEndpoints422 (p : Problem) (w : Wire) : Option (Read p) := do
  match args : p.root.demand.arguments with
  | [a] =>
    if narrow : RepeatedCenters421.checkRange p.state a ∧ a.lower ≠ a.upper then
      let low ← readAuthoredRecord p.state a.lower w.low
      let high ← readAuthoredRecord p.state a.upper w.high
      if same : high.label = low.label then
        if raw : checkExactEscape p.state.core.current.ordinary a.lower w.escape = true then
          if valid : RoleDefault420.checkHeader p.state.core.current.environment = true then
            match one : visible p.state.core p.root with
            | [d] =>
              if written : (authoredRegistry p.state.core.current).declarations[w.selected]? = some d then
                match head : d.head with
                | [.record label (.var x) (.var rest)] =>
                  match body : d.associated with
                  | [b] =>
                    match rhs : b.rhs with
                    | .var n =>
                      if shape : label = low.label ∧ x ≠ rest ∧ n = x ∧
                          d.requirements = [] ∧ d.outputBinders = [] then
                        if out : p.root.demand.outputs.length = 1 then
                          if nm : p.root.demand.outputs[ExplicitPick419.exactlyOneOutput p out].name = b.name then
                            have noRoot : ¬ RootCycle p.state p.root := by
                              rintro ⟨other,seen,cycle⟩
                              rw [args] at seen
                              cases List.mem_singleton.mp seen
                              exact exact_escape_refutes_raw_root_K2410 raw cycle
                            pure ⟨a,args,RepeatedCenters421.exact_range_bounds421 narrow.1,
                              narrow.2,low,high,same,d,one,w.selected,written,
                              (RoleDefault420.checked_default_header420 valid).1,x,rest,
                              shape.2.1,by simpa only [pickSyntax,shape.1] using head,
                              shape.2.2.2.1,shape.2.2.2.2,b,body,
                              by simpa only [shape.2.2.1] using rhs,out,nm,noRoot⟩
                          else none
                        else none
                      else none
                    | _ => none
                  | _ => none
                | _ => none
              else none
            | _ => none
          else none
        else none
      else none
    else none
  | _ => none

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
