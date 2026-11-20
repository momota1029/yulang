import Yulang.GeneralDeferredLadderControlBridge304
import Yulang.GeneralDeferredLadderWideFixture303

open Yulang
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderRelay304 (initial)
open GeneralDeferredLadderRelayCount304 (runAfter)
open GeneralDeferredLadderWideFixture303 (context certificate known)
open GeneralDeferredLadderControl304 (Control view successors remaining)

def check (n k : Nat) (cap : k ≤ n+1) : IO Unit := do
  let p := run n k cap
  let x := view n p.state
  unless x == (⟨k,false⟩ : Control) do throw (IO.userError "bad unseen control")
  let rel := initial n k cap (context p) (certificate p) (known p)
  let y := view n (GeneralNominalVersionedRefresh232.refresh p.state (context p))
  unless y == (⟨k,true⟩ : Control) do throw (IO.userError "bad seen control")
  let t := (runAfter rel (n+1-k) (by omega)).1
  let z := view n t
  unless z == (⟨n+1,true⟩ : Control) && (successors n z).isEmpty && remaining n z == 0 do
    throw (IO.userError "bad terminal control")
  let expectedBefore := (if k ≤ n then [⟨k+1,false⟩] else []) ++ [⟨k,true⟩]
  let expectedAfter := if k ≤ n then [⟨k+1,true⟩] else []
  unless successors n x == expectedBefore && successors n y == expectedAfter do
    throw (IO.userError "bad projected successor list")
  IO.println s!"PASS n={n}, k={k}; {repr (successors n x)} -> {repr (successors n y)} -> halt"

def main : IO Unit := do
  check 0 0 (by decide)
  check 3 2 (by decide)
  check 3 4 (by decide)
  check 6 1 (by decide)
