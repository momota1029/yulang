import Yulang.GeneralNominalOriginSupport249
import Yulang.GeneralNominalRebaseProjectionView243

/-! Finite support of every actual compiled projection report condition,
including cross-capture relations. All conditions share the same assignment. -/
namespace Yulang.GeneralNominalProjectionSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseProjectionView243
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

def boundsReads (b : Bounds) : List Nat := typedReads b.lower ++ typedReads b.upper
def originReads (o : Option Origin) : List Nat := o.toList.flatMap GeneralNominalOriginSupport249.support
def captureReads (c : Capture) : List Nat := boundsReads c.bounds ++ originReads c.origin
def support (report : Report) : List Nat :=
 report.anchors.flatMap (fun a => GeneralNominalOriginSupport249.support a.1 ++ boundsReads a.2) ++
 report.tests.flatMap (fun t => GeneralNominalOriginSupport249.support t.1) ++
 report.captures.flatMap captureReads

theorem bounds_iff (b : Bounds) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ boundsReads b, (first n).1 = (last n).1) (actual : Ty) :
 b.Fits first actual ↔ b.Fits last actual := by
 simp only [Bounds.Fits,
   type_eval_equal model first last rows b.lower (fun n h => types n (List.mem_append_left _ h)),
   type_eval_equal model first last rows b.upper (fun n h => types n (List.mem_append_right _ h))]

theorem models_iff (report : Report) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support report, (first n).1 = (last n).1) :
 report.Models first ↔ report.Models last := by
 have anchors (a) (member : a ∈ report.anchors) :
     ∀ n ∈ GeneralNominalOriginSupport249.support a.1 ++ boundsReads a.2,
       (first n).1 = (last n).1 := fun n h => types n
   (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨a,member,h⟩)))
 have tests (t) (member : t ∈ report.tests) :
     ∀ n ∈ GeneralNominalOriginSupport249.support t.1, (first n).1 = (last n).1 := fun n h => types n
   (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t,member,h⟩)))
 have captures (c) (member : c ∈ report.captures) :
     ∀ n ∈ captureReads c, (first n).1 = (last n).1 := fun n h => types n
   (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,member,h⟩))
 have capOrigin (c) (member : c ∈ report.captures) (o : Origin) (found : c.origin = some o) :
     ∀ n ∈ GeneralNominalOriginSupport249.support o, (first n).1 = (last n).1 := by
   intro n h
   apply captures c member n
   apply List.mem_append_right
   exact List.mem_flatMap.mpr ⟨o,by simp [found],h⟩
 have capBounds (c) (member : c ∈ report.captures) :
     ∀ n ∈ boundsReads c.bounds, (first n).1 = (last n).1 :=
   fun n h => captures c member n (List.mem_append_left _ h)
 unfold Report.Models
 apply and_congr
 · apply forall_congr'; intro a
   apply forall_congr'; intro member
   simp only [GeneralNominalOriginSupport249.observes_iff a.1 first last rows
     (fun n h => anchors a member n (List.mem_append_left _ h)),
     bounds_iff a.2 first last rows (fun n h => anchors a member n (List.mem_append_right _ h))]
 apply and_congr
 · apply forall_congr'; intro t
   apply forall_congr'; intro member
   simp only [GeneralNominalOriginSupport249.observes_iff t.1 first last rows (tests t member)]
 apply and_congr
 · apply forall_congr'; intro a
   apply forall_congr'; intro one
   apply forall_congr'; intro b
   apply forall_congr'; intro two
   apply forall_congr'; intro _
   apply forall_congr'; intro o
   apply forall_congr'; intro found
   simp only [GeneralNominalOriginSupport249.observes_iff o first last rows (capOrigin a one o found),
     bounds_iff b.bounds first last rows (capBounds b two)]
 · apply forall_congr'; intro a
   apply forall_congr'; intro one
   apply forall_congr'; intro b
   apply forall_congr'; intro two
   apply forall_congr'; intro _
   apply forall_congr'; intro x
   apply forall_congr'; intro y
   apply forall_congr'; intro atx
   apply forall_congr'; intro aty
   simp only [GeneralNominalOriginSupport249.observes_iff x first last rows (capOrigin a one x atx),
     GeneralNominalOriginSupport249.observes_iff y first last rows (capOrigin b two y aty)]
end Yulang.GeneralNominalProjectionSupport249
