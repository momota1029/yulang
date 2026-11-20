import Yulang.GeneralGeneratedDictionaryControls299

open Yulang
open GeneralGeneratedDictionaryRun299 (run)
open GeneralGeneratedDictionaryMemo299 (checkMemo)
open GeneralGeneratedDictionaryControls299 (cyclic missing repeated)

def main : IO Unit := do
  if checkMemo cyclic [0] 5 || checkMemo missing [0,1] 5 then
    throw (IO.userError "bad graph unexpectedly accepted")
  IO.println "PASS cyclic and absent-child tables do not pass the bounded certificate check"
  match run repeated 2 0 with
  | some (.node 8 [.node 9 [],.node 9 []]) =>
    IO.println "PASS repeat entry occurs twice in the actual ordered output"
  | _ => throw (IO.userError "repeated entry lost")
  match GeneralGeneratedFrontierReceipt299.compile
      GeneralGeneratedDisplayObserved299.lookup (fun _ => none) 0 with
  | .unindexed => IO.println "PASS an unindexed selected child is not reported as semantic rejection"
  | _ => throw (IO.userError "metadata fault incorrectly classified")
