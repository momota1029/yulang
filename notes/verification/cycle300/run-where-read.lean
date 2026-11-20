import Yulang.GeneralDepthTwoCertifiedRead300

open Yulang
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDictionaryRankBook299 (ready ranks get)
open GeneralDepthTwoObserved300 (table)

def main : IO Unit := do
  let book := ranks table [0,1,2] 3
  unless [get 0 book,get 1 book,get 2 book] == [some 3,some 2,some 1] do
    throw (IO.userError "incorrect selected ranks")
  unless ready table [0,1,2] 3 && !(ready table [0,1,2] 2) do
    throw (IO.userError "bad fuel boundary")
  IO.println "PASS independently checked V8 frontier has first-success fuels [3,2,1]"
  match run table 3 0 with
  | some (.node 1 [.node 1 [.node 3 []]]) =>
    IO.println "PASS compiled reader produces actual dictionary keys 1 → 1 → 3"
  | _ => throw (IO.userError "incorrect dictionary")
  unless (run table 2 0).isNone do
    throw (IO.userError "unexpected partial dictionary")
  IO.println "PASS two fuel units cannot produce the complete dictionary"
