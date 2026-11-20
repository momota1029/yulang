import Yulang.GeneralSourceRoleCstExplicitRead295

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (Wire decode)
open GeneralSourceRoleCstSpan293 (locate Extent)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

def localNaming (_ : Nat) : Environment :=
  ⟨fun n => if n = "a" then some 7 else none,fun _ _ => none,fun _ => none⟩

def missingNames (_ : Nat) : Environment :=
  ⟨fun _ => none,fun _ _ => none,fun _ => none⟩

def main (args : List String) : IO UInt32 := do
  let [fname] := args | return 2
  let .ok j := Json.parse (← IO.FS.readFile fname) | return 2
  let some w := read 64 j | return 2
  let addr : Address Nat := ⟨17,[0]⟩
  let sealed : Boundary Nat Nat := ⟨11,⟨addr,.selectedBranch,⟨w,.reported 17 [.errorGroupRange ⟨49,58⟩]⟩⟩⟩
  let some payload := handoff .selectedBranch 11 w 17 addr sealed | return 1
  unless payload.atRole == addr do return 1
  unless payload.body.length == 1 do return 1
  let [(method,.other)] := payload.body | return 1
  unless method.path == [0,4,2,0] do return 1
  let some root := decode w | return 1
  let some (_,roleSpan) := locate addr.path root 0 | return 1
  let some (_,headSpan) := locate [0,2] root 0 | return 1
  let some (_,memberSpan) := locate method.path root 0 | return 1
  unless roleSpan == ⟨0,49⟩ && headSpan == ⟨5,9⟩ && memberSpan == ⟨15,49⟩ do return 1
  let some table := compile .selectedBranch 11 w 17 addr sealed localNaming 1 | return 1
  let [row] := table.rows | return 1
  unless row.role == 7 && row.arity == 1 && row.outputs.isEmpty do return 1
  if (compile .selectedBranch 11 w 17 addr sealed missingNames 1).isSome then return 1
  if (compile .selectedBranch 11 w 17 ⟨17,[1]⟩ sealed localNaming 1).isSome then return 1
  if (compile .whole 11 w 17 addr sealed localNaming 1).isSome then return 1
  IO.println "Archived role a [0], method child [0,4,2,0], selected declaration only."
  IO.println "Role bytes 0..49; direct head [0,2] bytes 5..9; method bytes 15..49."
  IO.println "Caller-provided map a -> 7 yields one role row (arity 1); no associated outputs."
  IO.println "Without the map, or with a different site or policy, no table is produced."
  IO.println "No runtime Rust parser, full diagnostic receipt or compiler naming environment was collected."
  return 0
