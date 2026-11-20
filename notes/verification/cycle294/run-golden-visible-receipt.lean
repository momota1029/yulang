import Yulang.GeneralSourceRoleCstVisibleReceipt294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstMixedReceipt294 (Evidence Receipt)
open GeneralSourceRoleCstVisibleReceipt294 (project)
open GeneralSourceRoleCstSnapshot293 (Address)

def main (args : List String) : IO UInt32 := do
  let [file] := args | return 2
  let source ← IO.FS.readFile file
  let .ok j := Json.parse source | return 2
  let some wire := read 64 j | return 2
  let chosen : Address Nat := ⟨17,[0]⟩
  let reported : Receipt Nat := .reported 17 [.errorGroupRange ⟨49,58⟩]
  let partialRows : Receipt Nat := .reported 17 [.errorGroupRange ⟨49,57⟩]
  let bogus : Receipt Nat :=
    .reported 17 [.errorGroupRange ⟨49,58⟩,.otherDiagnostic ⟨.other,some [999]⟩]
  unless (project .selectedBranch () wire 17 chosen reported).isSome do return 1
  if (project .whole () wire 17 chosen reported).isSome then return 1
  if (project .selectedBranch () wire 17 chosen (.absent : Receipt Nat)).isSome then return 1
  if (project .selectedBranch () wire 17 chosen (.reported 18 [.errorGroupRange ⟨49,58⟩])).isSome then return 1
  if (project .selectedBranch () wire 17 chosen partialRows).isSome then return 1
  if (project .selectedBranch () wire 17 chosen bogus).isSome then return 1
  IO.println "One externally supplied source-visible plain token range: selected role admitted, whole-wire policy denied."
  IO.println "Absent receipt, wrong brand, partial range, and invented owner [999]: all denied."
  IO.println "Receipt completeness/authenticity was not checked; this is a replay, not a Rust execution."
  return 0
