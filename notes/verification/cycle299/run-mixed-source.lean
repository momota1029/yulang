import Yulang.GeneralGeneratedDisplayPhase299

open Yulang
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDisplayObserved299 (observedTable)
open GeneralGeneratedDictionaryMemo299 (checkMemo)
open GeneralGeneratedDictionaryMemoCheck299 (bitFirst)

def check (t : Bool) (msg : String) : IO Unit :=
  if t then IO.println ("PASS " ++ msg) else throw (IO.userError msg)

def main : IO Unit := do
  check (checkMemo observedTable [0,1] 2) "recorded C277 frontiers admit a computed rank at the two-row bound"
  check (bitFirst observedTable [0,1] 0 2 == some 2) "C277 parent certificate requires exactly two fuel units"
  check (bitFirst observedTable [0,1] 1 2 == some 1) "C277 generated child certificate requires one fuel unit"
  check ((run observedTable 1 0).isNone) "short budget does not emit an unsound partial dictionary"
  match run observedTable 2 0 with
  | some (.node 1 [.node 3 []]) => IO.println "PASS C277 ordered dictionary is node 1 with child node 3"
  | _ => throw (IO.userError "unexpected C277 dictionary")
  IO.println "The separate Lean proofs attach evidence only at the actual post-install snapshot."
