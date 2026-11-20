import Yulang.GeneralSourceRoleCstRunControls294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (decode)
open GeneralSourceRoleCstOriginalMarks294 (original Origin)
open GeneralSourceRoleCstErrorRuns294 (runs)
open GeneralSourceRoleCstRunExtent294 (extent)

def main (argv : List String) : IO UInt32 := do
  let [file] := argv | return 2
  let text ← IO.FS.readFile file
  let .ok json := Json.parse text | return 2
  let some wire := read 64 json | return 2
  let some tree := decode wire | return 2
  let rows := original wire tree
  let got := rows.map fun x => (x.occurrence.path,x.originalTag,x.originalMode)
  let expect : List (List Nat × String × GeneralSourceRoleCstOriginalMarks294.Element) :=
    [([1],"Error",.token),([2],"Error",.token),([3],"Error",.token)]
  if got != expect then return 1
  let [row] := runs rows | return 1
  let some span := extent row | return 1
  if span != ⟨49,58⟩ then return 1
  IO.println "Three original Error tokens at [1], [2], [3]; portable touching sibling run 49..58."
  IO.println "The checked-in Rust fixture separately records one structural recovery 49..58; no Rust diagnostics ran here."
  return 0
