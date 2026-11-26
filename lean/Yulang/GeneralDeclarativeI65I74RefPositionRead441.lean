import Yulang.GeneralDeclarativeI65I74RefPositionSource441
import Yulang.GeneralDeclarativeI65I74MergedOutputHeader439

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open Checker408 (Problem)
open PresenceNormalForm (Atom)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure Wire where
  original : Nat
  escape : ExactEscapeWire

/-- A locator and a finite raw escape certificate. Neither supplies a
    role ID, declared mode, capture slot, dictionary or report. -/
def replay441 (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (wire : Wire) :
    Option (Original p.state p.root d) := do
  let core := p.state.core
  let env := core.current.environment
  let raw := core.current.ordinary
  if header : MergedOutput439.checkHeader439 env = true then
    if boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true then
      match written : d.head, asked : p.root.demand.arguments with
      | [.app key [.var rowBinder,.var valueBinder]],[arg] =>
        if separate : rowBinder ≠ valueBinder then
          if verify : checkExactEscape raw arg.lower wire.escape = true then
            match atOrigin : core.origins[wire.original]? with
            | none => none
            | some original =>
              match read : original.endpoint with
              | .nominal observed [.inr (.point (.var r)),.inl (.point (.ordinary (.var v)))] =>
                if routes : observed = key ∧ original.issuer = p.root.occurrence ∧
                    original.slot = arg.lower ∧ original.slot = arg.center ∧ original.slot = arg.upper then
                  let use ← readUse env key 2
                  match source : use.mode with
                  | .declared params =>
                    if exact : params = layout ∧ core.modes[key]? = some layout then
                      if atoms : decide ((Atom.rowLe (.var r) (.var r) : Atom Nat) ∈ raw.normal.ordinary) &&
                          decide ((Atom.tyLe (.var v) (.var v) : Atom Nat) ∈ raw.normal.ordinary) then
                        let refined := MergedOutput439.checked_header439 header
                        let actually := ((visible_exact core p.root d).mp
                          (by rw [scope]; exact List.mem_cons_self)).1
                        let safe : ¬RootCycle p.state p.root := by
                          rintro ⟨someArg,mem,cycle⟩
                          rw [asked] at mem
                          cases List.mem_singleton.mp mem
                          exact exact_escape_refutes_raw_root_K2410 verify cycle
                        some {
                          only := scope
                          checked := refined.1.2 d actually
                          covered := refined.2.1 d actually
                          noWhere := List.isEmpty_iff.mp (splitAnd boundary).1
                          noOutputs := List.isEmpty_iff.mp (splitAnd boundary).2
                          arg := arg
                          asked := asked
                          key := key
                          rowBinder := rowBinder
                          valueBinder := valueBinder
                          separateBinders := separate
                          written := written
                          original := original
                          authored := List.mem_of_getElem? atOrigin
                          issuer := routes.2.1
                          lower := routes.2.2.1
                          center := routes.2.2.2.1
                          upper := routes.2.2.2.2
                          rowName := r
                          valueName := v
                          read := by rw [read,routes.1]; rfl
                          use := use
                          fromBody := by rw [source,exact.1]
                          table := exact.2
                          rowAtom := of_decide_eq_true (splitAnd atoms).1
                          valueAtom := of_decide_eq_true (splitAnd atoms).2
                          safe := safe }
                      else none
                    else none
                  | _ => none
                else none
              | _ => none
          else none
        else none
      | _,_ => none
    else none
  else none

theorem read_checks_own_row_and_value_in_order441 {p d scope wire a}
    (_got : replay441 p d scope wire = some a) :
    a.original.issuer = p.root.occurrence ∧
    a.original.endpoint = endpoint a.key a.rowName a.valueName ∧
    a.use.mode = .declared [rowCov,valueInv] ∧
    a.rowBinder ≠ a.valueBinder :=
  ⟨a.issuer,a.read,a.fromBody,a.separateBinders⟩

end Yulang.GeneralDeclarativeI65.I72.RefPositions441
