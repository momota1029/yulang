import Yulang.GeneralRebaseRowView298
import Yulang.GeneralNominalRebaseLiveView243

namespace Yulang.GeneralRebaseRowLive298
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseLiveView243
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralRebaseRowBasis298

def argumentReads (a : GeneralNominalRebaseLiveView243.Argument) : List Nat :=
 rowReads a.lower ++ rowReads a.upper ++ rowReads a.center

def support (site : Site) : List Nat :=
 site.arguments.flatMap argumentReads ++ site.outputs.flatMap (fun output => rowReads output.target)

theorem argument_iff (a : GeneralNominalRebaseLiveView243.Argument) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ argumentReads a, (first n).2 = (last n).2) : a.Holds first ↔ a.Holds last := by
 have lo := type_eval_equal model first last types a.lower
   (fun n h => rows n (List.mem_append_left _ (List.mem_append_left _ h)))
 have hi := type_eval_equal model first last types a.upper
   (fun n h => rows n (List.mem_append_left _ (List.mem_append_right _ h)))
 have center := type_eval_equal model first last types a.center
   (fun n h => rows n (List.mem_append_right _ h))
 simp only [Argument.Holds,lo,hi,center]

theorem site_iff (site : Site) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support site, (first n).2 = (last n).2) : site.Holds first ↔ site.Holds last := by
 apply forall_congr'; intro a
 apply forall_congr'; intro member
 exact argument_iff a first last types (fun n h => rows n
   (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a,member,h⟩)))

theorem output_equal (site : Site) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support site, (first n).2 = (last n).2)
 (output : Output) (member : output ∈ site.outputs) :
 output.target.eval model first = output.target.eval model last :=
 type_eval_equal model first last types _ (fun n h => rows n
   (List.mem_append_right _ (List.mem_flatMap.mpr ⟨output,member,h⟩)))
end Yulang.GeneralRebaseRowLive298
