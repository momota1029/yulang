import Yulang.GeneralObservedLadderJournalCompiler301

open Yulang
open GeneralObservedLadderAdvance301 (run)
open GeneralObservedLadderJournalCompiler301 (receipt table RowReceipt)
open GeneralObservedLadderEvidence301 (dictionary)

def check (n : Nat) : IO Unit := do
  let depth := n+1
  for phase in List.range (depth+1) do
    if bound : phase ≤ depth then
      let state := (run n phase bound).state
      for i in List.range (depth+2) do
        let wanted : RowReceipt :=
          if i > phase then .absent
          else if i < phase then .attached ⟨1,[i+1]⟩
          else if i = depth then .attached ⟨3,[]⟩
          else .awaitingChild (i+1)
        unless decide (receipt state i = wanted) do
          throw (IO.userError s!"wrong journal receipt depth {depth}, phase {phase}, row {i}")
      for fuel in List.range (depth+4) do
        let result := GeneralGeneratedDictionaryRun299.run (table state) fuel 0
        if phase = depth && depth < fuel then
          unless result.isSome do
            throw (IO.userError s!"missing final read depth {depth}, fuel {fuel}")
        else
          unless result.isNone do
            throw (IO.userError s!"premature read depth {depth}, phase {phase}, fuel {fuel}")
    else throw (IO.userError "test phase outside source")
  IO.println s!"PASS journal depth {depth}: absent vs awaitingChild vs attached, actual-edge gated readback"

def main : IO Unit := do
  for n in [0,2,4,7] do check n
