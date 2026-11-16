import Yulang.GeneralNominalCenteredEmptyFrame179

/-! Projection support reads base type slots and actual report origins only;
reservation bookkeeping and unrelated ordinary constraints are excluded. -/
namespace Yulang.GeneralDictionaryTightProjection224
open GeneralDeclarations GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
variable {first last : Assignment}

 def reportSources (state : GeneralNominalState.State) (report : Report state) : List Nat :=
  List.ofFn state.base.source ++ report.anchors.map (fun a => originSource a.1) ++
    report.tests.map (fun t => originSource t.1) ++
    report.captures.flatMap (fun c => c.origin.toList.map originSource)

 theorem report_slot (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) (slot : Fin state.base.slots) :
    first (state.base.source slot) = last (state.base.source slot) := by
  have member : state.base.source slot ∈ List.ofFn state.base.source :=
    List.mem_ofFn.mpr ⟨slot,rfl⟩
  exact same _ (by simp [reportSources,member])

 theorem report_capture (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last)
    (capture : GeneralNominalRecursiveInspection.Capture state) (member : capture ∈ report.captures)
    (origin : Origin) (recorded : capture.origin = some origin) :
    first (originSource origin) = last (originSource origin) := by
  have item : originSource origin ∈ report.captures.flatMap (fun c => c.origin.toList.map originSource) :=
    List.mem_flatMap.mpr ⟨capture,member,by simp [recorded]⟩
  exact same _ (by simp [reportSources,item])

 theorem projection_iff (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) :
    ProjectionModels state report first ↔ ProjectionModels state report last := by
  have slots := report_slot state report same
  unfold ProjectionModels
  apply and_congr
  · apply forall_congr'; intro anchor
    apply forall_congr'; intro member
    have item : originSource anchor.1 ∈ report.anchors.map (fun a => originSource a.1) :=
      List.mem_map.mpr ⟨anchor,member,rfl⟩
    have root := same _ (by simp [reportSources,item] : originSource anchor.1 ∈ reportSources state report)
    simp only [observes_iff anchor.1 root,Fits,GeneralNominalCaptureMerges.Fits,slots]
  apply and_congr
  · apply forall_congr'; intro test
    apply forall_congr'; intro member
    have item : originSource test.1 ∈ report.tests.map (fun t => originSource t.1) :=
      List.mem_map.mpr ⟨test,member,rfl⟩
    have root := same _ (by simp [reportSources,item] : originSource test.1 ∈ reportSources state report)
    simp only [observes_iff test.1 root]
  apply and_congr
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro _bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro origin
    apply forall_congr'; intro recorded
    have root := report_capture state report same a am origin recorded
    simp only [observes_iff origin root,Fits,GeneralNominalCaptureMerges.Fits,slots]
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro x
    apply forall_congr'; intro y
    apply forall_congr'; intro ax
    apply forall_congr'; intro byy
    simp only [observes_iff x (report_capture state report same a am x ax),
      observes_iff y (report_capture state report same b bm y byy)]


end Yulang.GeneralDictionaryTightProjection224
