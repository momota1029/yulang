import Yulang.GeneralNominalRawOrigin182
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSemanticRawFrame236
open GeneralDeclarations GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
variable {first last : Assignment}

/-- Reservations allocate identifiers but impose no semantic equation. -/
def erased (state : GeneralNominalState.State) : GeneralNominalState.State := {state with reserved := []}
def sources (state : GeneralNominalState.State) : List Nat := GeneralNominalState.sources (erased state)
theorem models_erased (state : GeneralNominalState.State) (model : Assignment) :
    GeneralNominalState.Models (erased state) model ↔ GeneralNominalState.Models state model := Iff.rfl

theorem slot_member (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    state.base.source slot ∈ sources state :=
  GeneralNominalAllocationSupport.slot_source (erased state) slot

theorem source_models_same (state : GeneralNominalState.State)
    (same : Agree (sources state) first last) :
    GeneralNominalState.Models state first ↔ GeneralNominalState.Models state last := by
  exact ⟨GeneralNominalCenteredModelExtension.source_models_same (erased state) same,
    GeneralNominalCenteredModelExtension.source_models_same (erased state) (fun n h => (same n h).symm)⟩

 def reportSources (state : GeneralNominalState.State) (report : Report state) : List Nat :=
  sources state ++ report.anchors.map (fun a => originSource a.1) ++
    report.tests.map (fun t => originSource t.1) ++
    report.captures.flatMap (fun c => c.origin.toList.map originSource)

 theorem report_slot (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) (slot : Fin state.base.slots) :
    first (state.base.source slot) = last (state.base.source slot) := by
  have member : state.base.source slot ∈ sources state :=
    slot_member state slot
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


theorem report_roots (context : GeneralNominalCandidates.Context) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    GeneralNominalRawOrigin182.ReportRoots (GeneralNominalRecursiveCandidates.report context declaration bounds)
      (sources context.state) :=
  GeneralNominalRawOrigin182.many_roots context.state _ (slot_member context.state)
    _ bounds _ 0 (fun _ _ impossible => by cases impossible)

theorem report_sources_subset (context : GeneralNominalCandidates.Context) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    reportSources context.state (GeneralNominalRecursiveCandidates.report context declaration bounds) ⊆ sources context.state := by
  intro name member
  have roots := report_roots context declaration bounds
  simp only [reportSources,List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact member
  · obtain ⟨anchor,present,rfl⟩ := List.mem_map.mp member
    exact roots.1 anchor present
  · obtain ⟨test,present,rfl⟩ := List.mem_map.mp member
    exact roots.2.1 test present
  · obtain ⟨capture,present,member⟩ := List.mem_flatMap.mp member
    obtain ⟨origin,recorded,rfl⟩ := List.mem_map.mp member
    exact roots.2.2 capture present origin (by simpa using recorded)

theorem report_endpoints (state : GeneralNominalState.State) (report : Report state) :
    GeneralNominalAllocationSupport.Endpoints (bindings state report) (sources state) := by
  intro entry member
  obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
  exact ⟨slot_member state capture.bounds.1,slot_member state capture.bounds.2⟩

theorem checks_sources (state : GeneralNominalState.State) (report : Report state) (atom)
    (member : atom ∈ selfChecks state report) : GeneralNominalState.atomSources atom ⊆ sources state := by
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  intro identity present
  rcases List.mem_append.mp present with first | last
  · cases List.mem_singleton.mp first; exact slot_member state bounds.1
  · cases List.mem_singleton.mp last; exact slot_member state bounds.2

theorem reserved_irrelevant (state : GeneralNominalState.State) (reserved : List Nat) :
    sources {state with reserved := reserved} = sources state := rfl

theorem allocated_irrelevant (state : GeneralNominalState.State) (allocated : List GeneralNominalIdentities.Origin) :
    sources {state with allocated := allocated} = sources state := rfl

theorem contained (state : GeneralNominalState.State) : sources state ⊆ GeneralNominalState.sources state := by
  intro identity member
  simp only [sources,erased,GeneralNominalState.sources,List.mem_append,List.not_mem_nil,or_false] at member ⊢
  rcases member with (one | two) | three
  · exact Or.inl (Or.inl (Or.inl one))
  · exact Or.inl (Or.inl (Or.inr two))
  · exact Or.inr three
end Yulang.GeneralNominalSemanticRawFrame236
