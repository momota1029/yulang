import Yulang.GeneralNominalProjectionSupport249
import Yulang.GeneralNominalRebaseObservedSite243
namespace Yulang.GeneralNominalObservedSupport249
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseObservedSite243

def argumentReads (argument : Argument) : List Nat :=
 GeneralNominalProjectionSupport249.boundsReads argument.bounds ++
 GeneralNominalProjectionSupport249.originReads argument.origin

def support (arguments : List Argument) : List Nat := arguments.flatMap argumentReads

theorem argument_iff (argument : Argument) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ argumentReads argument, (first n).1 = (last n).1) :
 argument.Holds first ↔ argument.Holds last := by
 apply forall_congr'; intro origin
 apply forall_congr'; intro found
 have originTypes : ∀ n ∈ GeneralNominalOriginSupport249.support origin,
     (first n).1 = (last n).1 := by
   intro n member
   apply types n
   apply List.mem_append_right
   exact List.mem_flatMap.mpr ⟨origin,by simp [found],member⟩
 simp only [GeneralNominalOriginSupport249.observes_iff origin first last rows originTypes,
   GeneralNominalProjectionSupport249.bounds_iff argument.bounds first last rows
     (fun n h => types n (List.mem_append_left _ h))]

theorem holds_iff (arguments : List Argument) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support arguments, (first n).1 = (last n).1) :
 Holds arguments first ↔ Holds arguments last := by
 apply forall_congr'; intro argument
 apply forall_congr'; intro member
 exact argument_iff argument first last rows
   (fun n h => types n (List.mem_flatMap.mpr ⟨argument,member,h⟩))
end Yulang.GeneralNominalObservedSupport249
