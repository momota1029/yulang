import Yulang.GeneralDeferredLadderUniversalLeaf302

open Yulang
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderBranch302 (successor)
open GeneralDeferredLadderAfterVariants302 (variantOwned)
open GeneralDeferredLadderOutcomes302 (terminal)
open GeneralObservedLadderJournalCompiler301 (receipt table RowReceipt)
open GeneralObservedLadderEvidence301 (dictionary)
open CommonRoleOutermostResolver (Dictionary)

def keys : Dictionary → List Nat
  | .node k [] => [k]
  | .node k (d::_) => k :: keys d

def check (n : Nat) : IO Unit := do
  let h := n+1
  for k in List.range (h+1) do
    if cap : k ≤ h then
      let p := run n k cap
      let data := p.state.core.erased.current
      unless data.edges.length == k && data.sites.length == k+1 do
        throw (IO.userError "wrong raw pre-observation prefix")
      unless (GeneralGeneratedDictionaryRun299.run (table p.state) (h+2) 0).isNone do
        throw (IO.userError "unobserved state compiled a dictionary")
      let expected : RowReceipt := if k < h then .awaitingChild (k+1) else .unresolved
      unless decide (receipt p.state k = expected) do
        throw (IO.userError "wrong pre-observation frontier receipt")
      for extra in [0,1,4] do
        let jump := (successor p extra).core.erased.current
        unless jump.edges.length == k && jump.sites.length == k+1 do
          throw (IO.userError "refresh changed the emitted edge/row prefix")
        unless jump.context.state.ordinary.length == data.context.state.ordinary.length + extra do
          throw (IO.userError "raw variant erased the redundant equations")
        let f := (terminal (variantOwned n k cap extra) cap).state
        unless f.core.erased.current.edges.length == h do
          throw (IO.userError "wrong actual scheduled leaf path")
        let r := GeneralGeneratedDictionaryRun299.run (table f)
        unless (r h 0).isNone do
          throw (IO.userError "early reader fuel accepted")
        let some d := r (h+1) 0 | throw (IO.userError "missing terminal result")
        unless keys d == List.replicate h 1 ++ [3] do
          throw (IO.userError "wrong dictionary in legal schedule")
    else throw (IO.userError "test phase out of range")
  IO.println s!"PASS depth {h}: every first-promotion phase with 0/1/4 extra equations; raw distinction and compiled dictionary"

def main : IO Unit := do
  for n in [0,1,2,4,7] do check n
