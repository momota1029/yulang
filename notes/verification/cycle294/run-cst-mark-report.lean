import Yulang.GeneralSourceRoleCstReportWire294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstMarkScope294 (Zone)
open GeneralSourceRoleCstMarkSpans294 (Entry)
open GeneralSourceRoleCstReportWire294 (input)
open GeneralSourceRoleHeadShape292 (Primary)

def num (n : Nat) : Json := .num (Lean.JsonNumber.fromNat n)
def pathJson (p : List Nat) : Json := .arr (p.map num).toArray

def zoneString : Zone → String
  | .selected => "selected"
  | .ancestor => "ancestor"
  | .unrelated => "unrelated"

def kindString : GeneralSourceRoleCstTree293.Kind → String
  | .error => "error"
  | .invalid => "invalid"
  | .missing => "missing"
  | k => reprStr k

def itemJson : Zone × Entry → Json
  | (zone,e) => Json.mkObj [("zone",.str (zoneString zone)),("path",pathJson e.path),
      ("kind",.str (kindString e.kind)),("low",num e.extent.low),("high",num e.extent.high)]

def main (args : List String) : IO UInt32 := do
  let file :: indices := args | return 2
  let some path := indices.mapM String.toNat? | return 2
  let text ← IO.FS.readFile file
  match input 64 text () (0 : Nat) ⟨0,path⟩ with
  | .error e =>
    IO.eprintln (reprStr e)
    return 1
  | .ok r =>
    let chosen := r.projected.bind fun p => match p.head.primary with
      | .simple n => some (.str n)
      | _ => none
    IO.println (Json.compress (Json.mkObj [
      ("path",pathJson path),
      ("candidateRole",chosen.getD .null),
      ("wholeWireMarkFree",.bool r.wholeWireMarkFree),
      ("selectedBranchMarkFree",.bool r.selectedBranchMarkFree),
      ("projectionAdmittedUnderWholeMarkPolicy",.bool (r.admitted .whole).isSome),
      ("projectionAdmittedUnderSelectedMarkPolicy",.bool (r.admitted .selectedBranch).isSome),
      ("rustDiagnosticsChecked",.bool false),
      ("wireMarks",.arr (r.found.map itemJson).toArray)]))
    return 0
