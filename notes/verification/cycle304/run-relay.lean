import Yulang.GeneralDeferredLadderClosed304
import Yulang.GeneralDeferredLadderWideFixture303

open Yulang
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderRelay304 (initial)
open GeneralDeferredLadderRelayCount304 (runAfter)
open GeneralDeferredLadderWideFixture303 (context certificate known)
open GeneralObservedLadderJournalCompiler301 (table)

def isSpine : Nat → CommonRoleOutermostResolver.Dictionary → Bool
  | 0, .node key [] => key == 3
  | n+1, .node key [child] => key == 1 && isSpine n child
  | _, _ => false

def checkWide (n k : Nat) (fit : k ≤ n+1) : IO Unit := do
  let p := run n k fit
  let relay := initial n k fit (context p) (certificate p) (known p)
  let t := (runAfter relay (n+1-k) (by omega)).1
  let core := t.core.erased.current
  unless core.context.state.view.kinds == 1 && core.edges.length == n+1 &&
      core.sites.length == n+2 && t.plans.length == n+1 do
    throw (IO.userError "wrong raw rows, edges, plans or catalogue")
  unless (GeneralGeneratedDictionaryRun299.run (table t) (n+2) 0).any (isSpine (n+1)) &&
      (GeneralGeneratedDictionaryRun299.run (table t) (n+1) 0).isNone do
    throw (IO.userError "dictionary or fuel threshold mismatch")
  IO.println s!"PASS n={n}, promotion at k={k}, {n+1-k} subsequent installs; wider catalogue and dictionary verified"

def main : IO Unit := do
  checkWide 0 0 (by decide)
  checkWide 3 0 (by decide)
  checkWide 3 2 (by decide)
  checkWide 3 4 (by decide)
  checkWide 5 1 (by decide)
