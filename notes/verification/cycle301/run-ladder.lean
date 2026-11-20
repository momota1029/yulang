import Yulang.GeneralObservedLadderReadback301

open Yulang
open GeneralObservedLadderRoute301 (focus invocation)
open GeneralObservedLadderAdvance301 (run)
open GeneralObservedLadderObserver301 (table)
open GeneralObservedLadderEvidence301 (dictionary)
open CommonRoleOutermostResolver (Dictionary)

def traceKeys (n k : Nat) (cap : k ≤ n+1) : List (Nat × Nat) :=
  (run n k cap).state.core.erased.current.edges.map (fun (a,b) => (a.identity,b.identity))

def traceSites (n k : Nat) (cap : k ≤ n+1) : List Nat :=
  (run n k cap).state.core.sites.map (·.occurrence.identity)

def branchKeys : Dictionary → List Nat
  | .node k [] => [k]
  | .node k (d::_) => k :: branchKeys d

def testDepth (n : Nat) : IO Unit := do
  let depth := n+1
  for k in List.range (depth+1) do
    if cap : k ≤ depth then
      let wanted := (List.range k).map (fun i => (invocation n i,invocation n (i+1)))
      unless traceKeys n k cap == wanted do
        throw (IO.userError s!"wrong edges at depth {depth}, phase {k}")
      unless traceSites n k cap == (List.range (k+1)).map (invocation n) do
        throw (IO.userError s!"wrong recorded sites at depth {depth}, phase {k}")
    else throw (IO.userError "test phase outside source")
  let readD := GeneralGeneratedDictionaryRun299.run (table n)
  for i in List.range (depth+1) do
    let remaining := depth-i
    unless (readD remaining i).isNone do
      throw (IO.userError s!"premature success at slot {i}")
    let some d := readD (remaining+1) i | throw (IO.userError s!"no result at slot {i}")
    unless branchKeys d == List.replicate remaining 1 ++ [3] do
      throw (IO.userError s!"wrong implementation keys at slot {i}")
  unless (table n (depth+1)).isNone && (readD (depth+2) (depth+1)).isNone do
    throw (IO.userError "compiler accepted an out-of-range node")
  IO.println s!"PASS depth {depth}: exact raw edge/center prefixes, compiler minimum fuel, out-of-range rejected"

def main : IO Unit := do
  for depth in [0,1,2,4,7] do
    testDepth depth
