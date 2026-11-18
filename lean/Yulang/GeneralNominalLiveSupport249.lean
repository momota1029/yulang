import Yulang.GeneralNominalViewSupport249
import Yulang.GeneralNominalRebaseLiveView243

/-! Concrete finite live-site support includes output values, although the
site Holds predicate itself only constrains arguments. -/
namespace Yulang.GeneralNominalLiveSupport249
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseLiveView243
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

def argumentReads (a : GeneralNominalRebaseLiveView243.Argument) : List Nat :=
 typedReads a.lower ++ typedReads a.upper ++ typedReads a.center

def support (site : Site) : List Nat :=
 site.arguments.flatMap argumentReads ++ site.outputs.flatMap (fun output => typedReads output.target)

theorem argument_iff (a : GeneralNominalRebaseLiveView243.Argument) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ argumentReads a, (first n).1 = (last n).1) : a.Holds first ↔ a.Holds last := by
 have lo := type_eval_equal model first last rows a.lower
   (fun n h => types n (List.mem_append_left _ (List.mem_append_left _ h)))
 have hi := type_eval_equal model first last rows a.upper
   (fun n h => types n (List.mem_append_left _ (List.mem_append_right _ h)))
 have center := type_eval_equal model first last rows a.center
   (fun n h => types n (List.mem_append_right _ h))
 simp only [Argument.Holds,lo,hi,center]

theorem site_iff (site : Site) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support site, (first n).1 = (last n).1) : site.Holds first ↔ site.Holds last := by
 apply forall_congr'; intro a
 apply forall_congr'; intro member
 exact argument_iff a first last rows (fun n h => types n
   (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a,member,h⟩)))

theorem output_equal (site : Site) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support site, (first n).1 = (last n).1)
 (output : Output) (member : output ∈ site.outputs) :
 output.target.eval model first = output.target.eval model last :=
 type_eval_equal model first last rows _ (fun n h => types n
   (List.mem_append_right _ (List.mem_flatMap.mpr ⟨output,member,h⟩)))
end Yulang.GeneralNominalLiveSupport249
