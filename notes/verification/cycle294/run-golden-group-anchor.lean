import Yulang.GeneralSourceRoleCstGroupFixture294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (decode)
open GeneralSourceRoleCstGroupAnchor294 (unique outside)

def main (args : List String) : IO UInt32 := do
  let [file] := args | return 2
  let text ← IO.FS.readFile file
  let .ok j := Json.parse text | return 2
  let some wire := read 64 j | return 2
  let some tree := decode wire | return 2
  -- Independently recorded in the Rust test assertion, not computed from this decoder.
  let some row := unique wire tree ⟨49,58⟩ | return 1
  if row.map (fun o => o.occurrence.path) != [[1],[2],[3]] then return 1
  if !(outside [0] row) || outside [] row then return 1
  if (unique wire tree ⟨49,57⟩).isSome then return 1
  IO.println "Externally recorded range 49..58 uniquely attaches to original Error token paths [1], [2], [3]."
  IO.println "Those paths are unrelated to selected [0], not unrelated to []. Partial range 49..57 is refused."
  return 0
