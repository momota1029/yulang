import Yulang.GeneralRebaseRowProjection298
import Yulang.GeneralNominalRebaseObservedSite243
namespace Yulang.GeneralRebaseRowObserved298
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseObservedSite243

def argumentReads (argument : Argument) : List Nat :=
 GeneralRebaseRowProjection298.boundsReads argument.bounds ++
 GeneralRebaseRowProjection298.originReads argument.origin

def support (arguments : List Argument) : List Nat := arguments.flatMap argumentReads

theorem argument_iff (argument : Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ argumentReads argument, (first n).2 = (last n).2) :
 argument.Holds first ↔ argument.Holds last := by
 apply forall_congr'; intro origin
 apply forall_congr'; intro found
 have originTypes : ∀ n ∈ GeneralRebaseRowOrigin298.support origin,
     (first n).2 = (last n).2 := by
   intro n member
   apply rows n
   apply List.mem_append_right
   exact List.mem_flatMap.mpr ⟨origin,by simp [found],member⟩
 simp only [GeneralRebaseRowOrigin298.observes_iff origin first last types originTypes,
   GeneralRebaseRowProjection298.bounds_iff argument.bounds first last types
     (fun n h => rows n (List.mem_append_left _ h))]

theorem holds_iff (arguments : List Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support arguments, (first n).2 = (last n).2) :
 Holds arguments first ↔ Holds arguments last := by
 apply forall_congr'; intro argument
 apply forall_congr'; intro member
 exact argument_iff argument first last types
   (fun n h => rows n (List.mem_flatMap.mpr ⟨argument,member,h⟩))
end Yulang.GeneralRebaseRowObserved298
