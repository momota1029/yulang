import Yulang.GeneralSourceRoleCstRecoveredCatalog296

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstCatalogExport296 (run Exported Failure)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstRecoveredCatalog296 (recoverCatalog)
open GeneralSourceMetadataBareRole291 (forgetRow)

def rejected (expected : Failure) : Except Failure Exported → Bool
  | .error found => decide (expected = found)
  | _ => false

def main (args : List String) : IO UInt32 := do
  let [filename] := args | return 2
  let .ok j := Json.parse (← IO.FS.readFile filename) | return 2
  let some w := read 64 j | return 2
  let a : Address Nat := ⟨17,[0]⟩
  let bound : Boundary Nat Nat := ⟨11,⟨a,.selectedBranch,⟨w,.reported 17 [.errorGroupRange ⟨49,58⟩]⟩⟩⟩
  let c : Catalog := [(.role "a",some 7)]
  let .ok out := run .selectedBranch 11 w 17 a bound c 1 | return 1
  let [row] := out.table.rows | return 1
  unless out.trace == c && row.role == 7 && row.arity == 1 && row.outputs.isEmpty do return 1
  let some p := handoff .selectedBranch 11 w 17 a bound | return 1
  let some r := symbolic p | return 1
  unless recoverCatalog r.role (forgetRow row) == some c do return 1
  unless rejected (.evidence (.missing (.role "a"))) (run .selectedBranch 11 w 17 a bound [] 1) do return 1
  unless rejected .oldExport (run .selectedBranch 11 w 17 a bound [(.role "a",none)] 1) do return 1
  unless rejected (.evidence (.ambiguous (.role "a")))
      (run .selectedBranch 11 w 17 a bound (c ++ [(.role "a",some 8)]) 1) do return 1
  unless rejected .selection (run .selectedBranch 11 w 17 ⟨17,[1]⟩ bound c 1) do return 1
  IO.println "Archived role a [0]: catalog row a -> 7, reproduced arity-1 table with no associated outputs."
  IO.println "Inverse of selected symbolic role and genuine old table recovered exactly the same one-row catalog."
  IO.println "Unobserved, explicitly absent, conflicting, and retargeted cases stayed distinct."
  IO.println "Finite ID observation and diagnostic range are supplied evidence; no Rust name resolver or parser executed."
  return 0
