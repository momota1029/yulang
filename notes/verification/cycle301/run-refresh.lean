import Yulang.GeneralObservedLadderRefreshProgram301

open Yulang
open GeneralObservedLadderRefresh301 (before after)
open GeneralObservedLadderRefreshChain301 (settled)
open GeneralObservedLadderSource301 (endpoint)
open GeneralObservedLadderJournalCompiler301 (probe table)

def test (n : Nat) : IO Unit := do
  let original := (before n).core.erased.current
  let observed := (after n).core.erased.current
  let final := (settled n).state
  let oldProbe := probe original.context [(endpoint n,endpoint n)]
  let newProbe := probe observed.context [(endpoint n,endpoint n)]
  unless oldProbe.isNone && decide (newProbe = some ⟨3,[]⟩) do
    throw (IO.userError "wrong concrete terminal observation around refresh")
  unless original.edges.isEmpty && observed.edges.isEmpty &&
      original.sites.length == 1 && observed.sites.length == 1 do
    throw (IO.userError "refresh must not generate a child")
  unless original.context.state.ordinary.length == 2 &&
      observed.context.state.ordinary.length == 2 &&
      observed.context.state.base.ordinary.length == 2 do
    throw (IO.userError "the promoted ground equation did not retain its ordinary origin")
  unless final.core.erased.current.edges.length == n+1 &&
      final.core.erased.current.sites.length == n+2 &&
      (GeneralGeneratedDictionaryRun299.run (table final) (n+2) 0).isSome do
    throw (IO.userError "refresh-first path did not reach computed dictionary")
  IO.println s!"PASS depth {n+1}: old scalar blocked, actual refreshed scalar available, original equations and zero edges retained, install chain compiled"

def main : IO Unit := do
  for n in [0,1,2,4,7] do test n
