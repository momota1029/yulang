import Yulang.GeneralSourceRoleCstRustEntry293

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (decode)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleCstSpan293 (Extent locate)

def main (argv : List String) : IO UInt32 := do
  let [file] := argv | return 2
  let bytes ← IO.FS.readFile file
  let .ok parsed := Json.parse bytes | return 2
  let some wire := read 64 parsed | return 2
  let some tree := decode wire | return 2
  let some picked := exportAt () ⟨0,tree⟩ ⟨(0 : Nat),[0]⟩ | return 2
  let [member] := picked.body | return 1
  let some (_,roleExtent) := locate picked.atRole.path tree 0 | return 1
  let some (_,memberExtent) := locate member.1.path tree 0 | return 1
  if picked.atRole.path == [0] && member.1.path == [0,4,2,0] &&
      roleExtent == ⟨0,49⟩ && memberExtent == ⟨15,49⟩ then
    IO.println "Recorded golden selected role path [0], bytes 0..49; direct binding path [0,4,2,0], bytes 15..49."
    return 0
  else
    IO.eprintln (reprStr (roleExtent,memberExtent))
    return 1
