import Yulang.GeneralNominalRebaseProjectionView243
import Yulang.GeneralNominalRebaseOriginActivation243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseProjectionSupport243
open GeneralNominalRebaseProjectionView243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseOriginActivation243 (sources observes_iff)
open GeneralNominalRebaseOriginView243 (Observes)
open GeneralNominalState (typeSources)

def boundsSources (bounds : Bounds) : List Nat := typeSources bounds.lower ++ typeSources bounds.upper

def captureSources (capture : Capture) : List Nat :=
 boundsSources capture.bounds ++ capture.origin.toList.flatMap sources

def reportSources (report : Report) : List Nat :=
 report.anchors.flatMap (fun anchor => sources anchor.1 ++ boundsSources anchor.2) ++
 report.tests.flatMap (fun test => sources test.1) ++ report.captures.flatMap captureSources

theorem bounds_iff (bounds : Bounds) {first last : Assignment}
 (same : Agree (boundsSources bounds) first last) (actual) :
 bounds.Fits first actual ↔ bounds.Fits last actual := by
 have lower := GeneralNominalCenteredModelExtension.type_eval_same bounds.lower
   (fun name member => same name (List.mem_append_left _ member))
 have upper := GeneralNominalCenteredModelExtension.type_eval_same bounds.upper
   (fun name member => same name (List.mem_append_right _ member))
 unfold Bounds.Fits
 rw [lower,upper]

theorem models_forward (report : Report) {first last : Assignment}
 (same : Agree (reportSources report) first last) (valid : report.Models first) : report.Models last := by
 have anchorSame (anchor) (member : anchor ∈ report.anchors) :
   Agree (sources anchor.1 ++ boundsSources anchor.2) first last := fun name present =>
   same name (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨anchor,member,present⟩)))
 have testSame (test) (member : test ∈ report.tests) : Agree (sources test.1) first last := fun name present =>
   same name (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨test,member,present⟩)))
 have captureSame (capture) (member : capture ∈ report.captures) :
   Agree (captureSources capture) first last := fun name present =>
   same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨capture,member,present⟩))
 have captureBounds (capture) (member : capture ∈ report.captures) (actual) :=
   bounds_iff capture.bounds (fun name present => captureSame capture member name (List.mem_append_left _ present)) actual
 have captureOrigin (capture) (member : capture ∈ report.captures) (origin)
   (recorded : capture.origin = some origin) (actual) :=
   observes_iff origin (fun name present => captureSame capture member name
     (List.mem_append_right _ (List.mem_flatMap.mpr ⟨origin,by simp [recorded],present⟩))) actual
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   have observed (actual) := observes_iff anchor.1
     (fun name present => anchorSame anchor member name (List.mem_append_left _ present)) actual
   obtain ⟨⟨actual,seen⟩,fits⟩ := valid.1 anchor member
   refine ⟨⟨actual,(observed actual).mp seen⟩,?_⟩
   intro value seen
   exact (bounds_iff anchor.2
     (fun name present => anchorSame anchor member name (List.mem_append_right _ present)) value).mp
     (fits value ((observed value).mpr seen))
 · intro test member actual seen
   exact valid.2.1 test member actual ((observes_iff test.1 (testSame test member) actual).mpr seen)
 · intro one member lastCapture included equal origin recorded actual seen
   exact (captureBounds lastCapture included actual).mp
     (valid.2.2.1 one member lastCapture included equal origin recorded actual
       ((captureOrigin one member origin recorded actual).mpr seen))
 · intro one member lastCapture included equal a b firstOrigin lastOrigin x y oneSeen lastSeen
   exact valid.2.2.2 one member lastCapture included equal a b firstOrigin lastOrigin x y
     ((captureOrigin one member a firstOrigin x).mpr oneSeen)
     ((captureOrigin lastCapture included b lastOrigin y).mpr lastSeen)

theorem models_iff (report : Report) {first last : Assignment}
 (same : Agree (reportSources report) first last) : report.Models first ↔ report.Models last :=
 ⟨models_forward report same,models_forward report (fun name member => (same name member).symm)⟩
end Yulang.GeneralNominalRebaseProjectionSupport243
