import Yulang.GeneralDeferredLadderWideFixture303

open Yulang
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderWideFixture303 (context certificate)
open GeneralDeferredLadderEarlyInstall303 (effect)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedInstall232 (install)

def check (n k : Nat) (fit : k ≤ n) : IO Unit := do
  let p := run n k (by omega)
  let fresh := refresh p.state (context p)
  let before := fresh.core.erased.current
  unless before.context.state.view.kinds == 1 && before.edges.length == k do
    throw (IO.userError "wider legal refresh has the wrong catalogue or lineage")
  let next := install fresh (effect p fit (context p) (certificate p))
  let after := next.core.erased.current
  unless after.context.state.view.kinds == 1 && after.edges.length == k+1 &&
      after.sites.length == k+2 && next.plans.length == k+1 do
    throw (IO.userError "post-refresh install lost the catalogue or installed the wrong row")
  IO.println s!"PASS n={n}, k={k}: wide catalogue stayed, exactly one row and edge appended"

def main : IO Unit := do
  check 0 0 (by decide)
  check 3 0 (by decide)
  check 3 2 (by decide)
