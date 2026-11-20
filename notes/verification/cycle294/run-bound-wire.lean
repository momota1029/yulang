import Yulang.GeneralSourceRoleCstBindingControl294

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWireBinding294 (same BoundReceipt useBound)
open GeneralSourceRoleCstVisibleReceipt294 (project)
open GeneralSourceRoleCstMixedReceipt294 (Receipt)
open GeneralSourceRoleCstSnapshot293 (Address)

def main (args : List String) : IO UInt32 := do
  let [fixture] := args | return 2
  let .ok j := Json.parse (← IO.FS.readFile fixture) | return 2
  let some (Wire.node "Root" children) := read 64 j | return 2
  let event : Receipt Nat := .reported 17 [.errorGroupRange ⟨49,58⟩]
  let a : Address Nat := ⟨17,[0]⟩
  unless children.getLast?.any (same (.token "Newline" "\n")) do return 1
  let base : Wire := .node "Root" children
  let variant : Wire := .node "Root" (children.dropLast ++ [.token "Whitespace" "\n"])
  let tied : BoundReceipt Nat := ⟨base,event⟩
  unless (useBound .selectedBranch () base 17 a tied).isSome do return 1
  unless (project .selectedBranch () variant 17 a event).isSome do return 1
  if (useBound .selectedBranch () variant 17 a tied).isSome then return 1
  IO.println "Original checked-in role wire accepts its attached recorded range."
  IO.println "Changing only the final Newline label to Whitespace does not change compact decode or legacy branch admission."
  IO.println "The wire-bound receipt still refuses the altered snapshot with the same external brand."
  IO.println "Wire equality cannot authenticate diagnostic results or their parser environment."
  return 0
