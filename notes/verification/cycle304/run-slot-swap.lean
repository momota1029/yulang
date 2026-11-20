import Yulang.GeneralNominalSlotSwapFixture304

open Yulang
open GeneralNominalSlotSwapFixture304 (snapshot)
open GeneralNominalTotalLocation304 (status SlotStatus)
open GeneralDictionaryBinderLocations (sourceSlot)

def main : IO Unit := do
  let a := snapshot false
  let b := snapshot true
  let old := ([0,1,2] : List Nat).map (fun id => (sourceSlot a.base id).map Fin.val)
  let new := ([0,1,2] : List Nat).map (fun id => (sourceSlot b.base id).map Fin.val)
  unless old == [some 0,some 1,none] && new == [some 1,some 0,none] do
    throw (IO.userError "slot coordinates did not reverse")
  let reports := ([0,1,2] : List Nat).map (status a)
  unless reports == [.known,.unresolved,.missing] &&
      reports == ([0,1,2] : List Nat).map (status b) do
    throw (IO.userError "source observations changed under slot reversal")
  let location := fun (c : GeneralNominalRecursiveCandidates.Context) =>
    (GeneralNominalRecursiveCandidates.arguments c GeneralNominalExamples.displayRoot).map
      (List.map fun b => (b.1.val,b.2.val))
  let argsA := location ⟨a,GeneralNominalExamples.interpretation⟩
  let argsB := location ⟨b,GeneralNominalExamples.interpretation⟩
  unless argsA == some [(0,0)] && argsB == some [(1,1)] do
    throw (IO.userError "argument lookup was not transported")
  IO.println s!"PASS slots {repr old} -> {repr new}; observations {repr reports}; bounds {repr argsA} -> {repr argsB}"
