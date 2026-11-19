import Yulang.GeneralRebaseClassLocality283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCacheCounterexamples283
open Core.PresenceGeneration (TyTerm)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralRebaseCrossProbe283 (refresh)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

def earlier : List (Entry Nat) := [(3,.var 1),(5,.var 3),(6,.var 2)]
def full : List (Entry Nat) := [(1,.var 0),(3,.var 1),(5,.var 3),(6,.var 2)]

/-- A newly assigned free variable invalidates both transitive old consumers
but does not invalidate the unrelated definition. This is a generic compiler
test, not a claim that every actual novel packet back-references old entries. -/
theorem overlap : ((changes earlier full).map Prod.fst) = [1,3,5] := rfl

theorem sparse_writes : (GeneralRebaseDirtyHistory283.select (earlier.map Prod.fst) earlier [1]).map Prod.fst =
  [3,5] := rfl

theorem slice_keeps_dependencies : ((GeneralRebaseSlice283.build full [5]).keep.map Prod.fst) = [1,3,5] := rfl

def rowDependent : List (Entry Nat) := [(5,.arrow .top (.var 1) .top .empty)]

def empty : Assignment := fun _ => (.top, Common.rowEmpty)
def universal : Assignment := fun _ => (.top,fun _ => True)

theorem rows_cannot_be_dropped :
    (∀ n, (empty n).1 = (universal n).1) ∧
    (refresh rowDependent rowDependent [] (solve model rowDependent empty) universal 5).1 ≠
      (solve model rowDependent universal 5).1 := by
  constructor
  · intro _; rfl
  · intro bad
    change CommonNominalSyntax.Layer.arrow (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty =
      CommonNominalSyntax.Layer.arrow (CommonNominalSyntax.State.node (Row := Common.Row) .top) (fun _ => True) (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty at bad
    have wrong := congrFun (CommonNominalSyntax.Layer.arrow.inj bad).2.1 (0,[])
    exact Eq.mp wrong.symm True.intro

end Yulang.GeneralRebaseCacheCounterexamples283
