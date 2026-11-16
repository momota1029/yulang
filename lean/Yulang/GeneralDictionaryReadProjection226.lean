import Yulang.GeneralDictionaryRelativeProvenance226

namespace Yulang.GeneralDictionaryReadProjection226
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Bounds)
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
variable {first last : Assignment}

def boundsSources (state : GeneralNominalState.State) (bounds : Bounds state) : List Nat :=
  [state.base.source bounds.1,state.base.source bounds.2]

def reportSources (state : GeneralNominalState.State) (report : Report state) : List Nat :=
  report.anchors.flatMap (fun a => originSource a.1 :: boundsSources state a.2) ++
    report.tests.map (fun t => originSource t.1) ++
    report.captures.flatMap (fun c => boundsSources state c.bounds ++ c.origin.toList.map originSource)

theorem fits_iff (state : GeneralNominalState.State) (bounds : Bounds state)
    (same : Agree (boundsSources state bounds) first last) (actual) :
    Fits state first bounds actual ↔ Fits state last bounds actual := by
  have low := same _ (by simp [boundsSources] : state.base.source bounds.1 ∈ boundsSources state bounds)
  have high := same _ (by simp [boundsSources] : state.base.source bounds.2 ∈ boundsSources state bounds)
  simp only [Fits,GeneralNominalCaptureMerges.Fits,low,high]

theorem report_capture (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last)
    (capture : Capture state) (member : capture ∈ report.captures) :
    Agree (boundsSources state capture.bounds ++ capture.origin.toList.map originSource) first last := by
  intro n present
  exact same n (List.mem_append_right _ (List.mem_flatMap.mpr ⟨capture,member,present⟩))

theorem projection_iff (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) :
    ProjectionModels state report first ↔ ProjectionModels state report last := by
  unfold ProjectionModels
  apply and_congr
  · apply forall_congr'; intro anchor
    apply forall_congr'; intro member
    have support : Agree (originSource anchor.1 :: boundsSources state anchor.2) first last := by
      intro n present
      exact same n (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨anchor,member,present⟩)))
    have root := support _ (List.mem_cons_self ..)
    simp only [observes_iff anchor.1 root,
      fits_iff state anchor.2 (fun n present => support n (List.mem_cons_of_mem _ present))]
  apply and_congr
  · apply forall_congr'; intro test
    apply forall_congr'; intro member
    have root := same _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨test,member,rfl⟩)))
    simp only [observes_iff test.1 root]
  apply and_congr
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro origin
    apply forall_congr'; intro recorded
    have root := report_capture state report same a am (originSource origin) (by simp [recorded])
    have bounds : Agree (boundsSources state b.bounds) first last :=
      fun n present => report_capture state report same b bm n (List.mem_append_left _ present)
    simp only [observes_iff origin root,fits_iff state b.bounds bounds]
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro x
    apply forall_congr'; intro y
    apply forall_congr'; intro ax
    apply forall_congr'; intro byy
    have one := report_capture state report same a am (originSource x) (by simp [ax])
    have two := report_capture state report same b bm (originSource y) (by simp [byy])
    simp only [observes_iff x one,observes_iff y two]

end Yulang.GeneralDictionaryReadProjection226

namespace Yulang.GeneralDictionaryReadProjection226
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralNominalAllocationSupport GeneralNominalState
open GeneralDictionaryHeadSharingRawSupport220
open GeneralDictionaryRelativePacket225 (ordinaryAtoms)
open GeneralDictionaryRelativeProvenance226 (localSources)
variable {roles : Roles.RoleDecls}

def readBounds (state : GeneralNominalState.State) (report : Report state) : List Nat :=
  report.captures.flatMap (fun capture => boundsSources state capture.bounds) ++
    report.checked.flatMap (boundsSources state)

theorem read_endpoints (state : GeneralNominalState.State) (report : Report state) :
    Endpoints (bindings state report) (readBounds state report) := by
  intro entry member
  obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
  constructor
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨capture,present,by simp [boundsSources]⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨capture,present,by simp [boundsSources]⟩)

theorem checks_read (state : GeneralNominalState.State) (report : Report state)
    (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ selfChecks state report) :
    atomSources atom ⊆ readBounds state report := by
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  intro name within
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨bounds,present,by simpa [boundsSources,atomSources,typeSources] using within⟩

theorem ordinary_read (plan : Plan roles) :
    (ordinaryAtoms plan).flatMap atomSources ⊆
      readBounds plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) ++ localSources plan := by
  intro name member
  obtain ⟨atom,present,read⟩ := List.mem_flatMap.mp member
  have endpoints := read_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)
  have widened : Endpoints plan.packet.bindings
      (readBounds plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) ++ localSources plan) := by
    intro entry member
    exact ⟨List.mem_append_left _ (endpoints entry member).1,List.mem_append_left _ (endpoints entry member).2⟩
  rcases List.mem_append.mp present with ordinary | check
  · rcases List.mem_append.mp ordinary with cross | merge
    · exact cross_sources widened atom cross read
    · exact merges_sources_tight plan.packet.context.state widened
        (fun n declared => capture_targets_local plan.packet.context.state endpoints declared) atom merge read
  · exact checks_read plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) atom check read |>
      List.mem_append_left _

end Yulang.GeneralDictionaryReadProjection226
