import Yulang.GeneralRebaseRowOrigin298
import Yulang.GeneralNominalRebaseProjectionView243

namespace Yulang.GeneralRebaseRowProjection298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseProjectionView243
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralRebaseRowBasis298

def boundsReads (b : Bounds) : List Nat := rowReads b.lower ++ rowReads b.upper
def originReads (o : Option Origin) : List Nat := o.toList.flatMap GeneralRebaseRowOrigin298.support
def captureReads (c : Capture) : List Nat := boundsReads c.bounds ++ originReads c.origin
def support (report : Report) : List Nat :=
 report.anchors.flatMap (fun a => GeneralRebaseRowOrigin298.support a.1 ++ boundsReads a.2) ++
 report.tests.flatMap (fun t => GeneralRebaseRowOrigin298.support t.1) ++
 report.captures.flatMap captureReads

theorem bounds_iff (b : Bounds) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ boundsReads b, (first n).2 = (last n).2) (actual : Ty) :
 b.Fits first actual ↔ b.Fits last actual := by
 simp only [Bounds.Fits,
   type_eval_equal model first last types b.lower (fun n h => rows n (List.mem_append_left _ h)),
   type_eval_equal model first last types b.upper (fun n h => rows n (List.mem_append_right _ h))]

theorem models_iff (report : Report) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support report, (first n).2 = (last n).2) :
 report.Models first ↔ report.Models last := by
 have anchors (a) (member : a ∈ report.anchors) :
     ∀ n ∈ GeneralRebaseRowOrigin298.support a.1 ++ boundsReads a.2,
       (first n).2 = (last n).2 := fun n h => rows n
   (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a,member,h⟩)))
 have tests (t) (member : t ∈ report.tests) :
     ∀ n ∈ GeneralRebaseRowOrigin298.support t.1, (first n).2 = (last n).2 := fun n h => rows n
   (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t,member,h⟩)))
 have captures (c) (member : c ∈ report.captures) :
     ∀ n ∈ captureReads c, (first n).2 = (last n).2 := fun n h => rows n
   (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,member,h⟩))
 have capOrigin (c) (member : c ∈ report.captures) (o : Origin) (found : c.origin = some o) :
     ∀ n ∈ GeneralRebaseRowOrigin298.support o, (first n).2 = (last n).2 := by
   intro n h
   apply captures c member n
   apply List.mem_append_right
   exact List.mem_flatMap.mpr ⟨o,by simp [found],h⟩
 have capBounds (c) (member : c ∈ report.captures) :
     ∀ n ∈ boundsReads c.bounds, (first n).2 = (last n).2 :=
   fun n h => captures c member n (List.mem_append_left _ h)
 unfold Report.Models
 apply and_congr
 · apply forall_congr'; intro a
   apply forall_congr'; intro member
   simp only [GeneralRebaseRowOrigin298.observes_iff a.1 first last types
     (fun n h => anchors a member n (List.mem_append_left _ h)),
     bounds_iff a.2 first last types (fun n h => anchors a member n (List.mem_append_right _ h))]
 apply and_congr
 · apply forall_congr'; intro t
   apply forall_congr'; intro member
   simp only [GeneralRebaseRowOrigin298.observes_iff t.1 first last types (tests t member)]
 apply and_congr
 · apply forall_congr'; intro a
   apply forall_congr'; intro one
   apply forall_congr'; intro b
   apply forall_congr'; intro two
   apply forall_congr'; intro _
   apply forall_congr'; intro o
   apply forall_congr'; intro found
   simp only [GeneralRebaseRowOrigin298.observes_iff o first last types (capOrigin a one o found),
     bounds_iff b.bounds first last types (capBounds b two)]
 · apply forall_congr'; intro a
   apply forall_congr'; intro one
   apply forall_congr'; intro b
   apply forall_congr'; intro two
   apply forall_congr'; intro _
   apply forall_congr'; intro x
   apply forall_congr'; intro y
   apply forall_congr'; intro atx
   apply forall_congr'; intro aty
   simp only [GeneralRebaseRowOrigin298.observes_iff x first last types (capOrigin a one x atx),
     GeneralRebaseRowOrigin298.observes_iff y first last types (capOrigin b two y aty)]
end Yulang.GeneralRebaseRowProjection298
