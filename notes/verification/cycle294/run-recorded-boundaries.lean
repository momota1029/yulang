import Yulang.GeneralSourceRoleCstMissingReceipt294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (decode)
open GeneralSourceRoleCstOriginalMarks294 (original Element)
open GeneralSourceRoleCstMissingReceipt294 (MissingAnchor verified independentlyOutside)
open GeneralSourceRoleCstVisibleRange294 (checkVisible)
open GeneralSourceRoleCstGroupAnchor294 (unique)

def main (args : List String) : IO UInt32 := do
  let [caseFile,nestedFile] := args | return 2
  let .ok j := Json.parse (← IO.FS.readFile caseFile) | return 2
  let some cw := read 64 j | return 2
  let some ct := decode cw | return 2
  let lhs : MissingAnchor := ⟨[0,0,1,0,0],⟨4,4⟩⟩
  let rhs : MissingAnchor := ⟨[0,0,2,0],⟨4,4⟩⟩
  let found := original cw ct
  let some a := found[0]? | return 1
  let some b := found[1]? | return 1
  unless found.length == 2 && a.occurrence.extent == lhs.span &&
      b.occurrence.extent == rhs.span && a.occurrence.path == lhs.path &&
      b.occurrence.path == rhs.path &&
      a.originalTag == "Missing" && b.originalTag == "Missing" &&
      a.originalMode == .node && b.originalMode == .node do return 1
  unless verified cw lhs && verified cw rhs do return 1
  if verified cw ⟨[0,0,1,0,1],⟨4,4⟩⟩ || verified cw ⟨lhs.path,⟨4,5⟩⟩ then return 1
  if independentlyOutside cw [0,0,1] lhs || !(independentlyOutside cw [0,0,1] rhs) then return 1
  if (unique cw ct ⟨4,4⟩).isSome then return 1
  IO.println "Archived case: confirmed Missing nodes [0,0,1,0,0] and [0,0,2,0] share 4..4."
  IO.println "A focus on [0,0,1] contains one but is unrelated to the other; the range does not decide scope."
  let .ok j := Json.parse (← IO.FS.readFile nestedFile) | return 2
  let some fw := read 64 j | return 2
  let some ft := decode fw | return 2
  let some row := unique fw ft ⟨13,14⟩ | return 1
  unless row.map (fun o => o.occurrence.path) == [[0,0,9,0]] do return 1
  unless checkVisible fw ⟨13,14⟩ [0,0,2] do return 1
  if checkVisible fw ⟨13,14⟩ [0,0,9] then return 1
  IO.println "Archived for statement: singleton Error run at [0,0,9,0], 13..14, visible out of sibling focus."
  IO.println "These are recorded Rust CST values, not freshly parsed programs or role projections."
  return 0
