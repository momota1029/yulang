import Yulang.GeneralSourceRoleCstKnownOnSuccess296

open Lean (Json)
open Yulang
open GeneralSourceRoleCstJson293 (read)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstIssuePacket296 (issue)
open GeneralSourceRoleCstIssuedScope296 (accept checks)
open GeneralSourceMetadataRoles291 (RoleRow)

def main (args : List String) : IO UInt32 := do
  let [fname] := args | return 2
  let .ok json := Json.parse (← IO.FS.readFile fname) | return 2
  let some source := read 64 json | return 2
  let addr : Address Nat := ⟨17,[0]⟩
  let chosen : Boundary Nat Nat :=
    ⟨11,⟨addr,.selectedBranch,⟨source,.reported 17 [.errorGroupRange ⟨49,58⟩]⟩⟩⟩
  let c1 : Catalog := [(.role "a",some 7)]
  let c2 : Catalog := [(.role "a",some 8)]
  let fresh := fun c => issue .selectedBranch 11 source 17 addr (41 : Nat) chosen c 1
  let .error (.evidence (.ambiguous (.role "a"))) := fresh (c1 ++ c2) | return 1
  let .ok out1 := fresh c1 | return 1
  let .ok out2 := fresh c2 | return 1
  unless checks out1.packet source 11 addr .selectedBranch 41 1 &&
      checks out2.packet source 11 addr .selectedBranch 41 1 do return 1
  let .ok table1 := accept out1.packet source 11 17 addr .selectedBranch 41 chosen 1 | return 1
  let .ok table2 := accept out2.packet source 11 17 addr .selectedBranch 41 chosen 1 | return 1
  unless table1.table.rows.map RoleRow.role == [7] &&
      table2.table.rows.map RoleRow.role == [8] do return 1
  IO.println "Same archived wire, role [0], and revision 41 accept two separately supplied contradictory catalogs."
  IO.println "One replay yields a row with ID 7 and the other with ID 8."
  IO.println "Combining both observations is rejected as ambiguous; matching revision fields cannot attest either ID."
  IO.println "Archived syntax is real fixture data; the alternate numeric observations are explicitly synthetic."
  return 0
