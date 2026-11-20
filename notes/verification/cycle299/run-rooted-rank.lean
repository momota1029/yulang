import Yulang.GeneralGeneratedDictionaryRootedFixtures299

open Yulang
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDictionarySlice299 (keys)
open GeneralGeneratedDictionaryRankBook299 (ready ranks get)
open GeneralGeneratedDictionaryRootedFixtures299 (unrelated rootSlice)
open GeneralGeneratedDisplayObserved299 (observedTable)

def main : IO Unit := do
  let book := ranks observedTable [0,1] 2
  unless ((get 0 book) == some 2) && ((get 1 book) == some 1) do
    throw (IO.userError "incorrect earliest-rank book")
  IO.println "PASS one layered rank book retains first successful C277 values [2,1]"
  unless keys unrelated 2 0 == [0,1] do
    throw (IO.userError "unexpected visited index list")
  if ready unrelated [0,1,8] 3 || !(ready rootSlice [0,1] 2) then
    throw (IO.userError "slice and full table status were conflated")
  match run rootSlice 2 0 with
  | some (.node 2 [.node 4 []]) => IO.println "PASS rooted slice retains its exact tree despite a disconnected cyclic row"
  | _ => throw (IO.userError "rooted tree did not replay")
  IO.println "The disconnected-cycle example is synthetic and does not assert a new raw source step."
