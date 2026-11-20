import Yulang.GeneralSourceRoleCstRustEntry293

open Lean (Json)
open Yulang
open GeneralSourceRoleCstRustEntry293 (extractValue)
open GeneralSourceRoleChildCoverage292 (Child)

def pathFromJson (j : Json) : Except String (List Nat) := do
  let a ← j.getArr?
  a.toList.mapM Json.getNat?

def checkOne (j : Json) : Except String Bool := do
  let arr ← j.getArr?
  match arr.toList with
  | [wire, selector, expected] =>
    let path ← pathFromJson selector
    match expected,extractValue 64 wire () (0 : Nat) ⟨0,path⟩ with
    | .null,.error _ => return true
    | .null,.ok _ => return false
    | _,.error _ => return false
    | .arr _,.ok output =>
      let p ← pathFromJson expected
      match output.body with
      | (a,.typeDecl _)::_ => return a.path == p
      | _ => return false
    | _,.ok _ => return false
  | _ => throw "expected [wire, selector, expectedMemberPathOrNull]"

def main (argv : List String) : IO UInt32 := do
  let [file] := argv | return 2
  let text ← IO.FS.readFile file
  let .ok corpus := Json.parse text | return 2
  let .ok inputs := corpus.getArr? | return 2
  let .ok reports := inputs.toList.mapM checkOne | return 2
  let results := reports.zipIdx.filter fun (ok,_) => !ok
  if results.isEmpty then
    IO.println s!"All {reports.length} synthetic matrix cases matched"
    return 0
  else
    IO.eprintln (reprStr (results.map Prod.snd))
    return 1
