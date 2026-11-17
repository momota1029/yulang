import Yulang.GeneralNominalInspectionSupport237
set_option backward.isDefEq.respectTransparency false
/-! Exact read support of a report excludes unused slots and ordinary atoms. -/
namespace Yulang.GeneralNominalReportSupport237
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
variable {first last : Assignment}
def endpoints (state : GeneralNominalState.State) (bounds : GeneralNominalInspection.Bounds state) : List Nat :=
 [state.base.source bounds.1,state.base.source bounds.2]
def captureSources (state : GeneralNominalState.State) (capture : Capture state) : List Nat :=
 endpoints state capture.bounds ++ capture.origin.toList.map originSource
def sources (state : GeneralNominalState.State) (report : Report state) : List Nat :=
 report.anchors.flatMap (fun anchor => originSource anchor.1 :: endpoints state anchor.2) ++
 report.tests.map (fun test => originSource test.1) ++
 report.captures.flatMap (captureSources state) ++ report.checked.flatMap (endpoints state)

theorem fits_iff (state : GeneralNominalState.State) (bounds : GeneralNominalInspection.Bounds state)
 (same : Agree (endpoints state bounds) first last) : Fits state first bounds value ↔ Fits state last bounds value := by
 have one := same _ (List.mem_cons_self ..)
 have two := same _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
 simp only [Fits,GeneralNominalCaptureMerges.Fits,one,two]

theorem capture_agree (state : GeneralNominalState.State) (report : Report state)
 (same : Agree (sources state report) first last) (capture : Capture state) (member : capture ∈ report.captures) :
 Agree (captureSources state capture) first last := by
 intro identity within
 exact same identity (by simp only [sources,List.mem_append]; exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨capture,member,within⟩)))

theorem capture_origin (state : GeneralNominalState.State) (report : Report state)
 (same : Agree (sources state report) first last) (capture : Capture state) (member : capture ∈ report.captures)
 (recorded : capture.origin = some origin) : first (originSource origin) = last (originSource origin) :=
 capture_agree state report same capture member _ (List.mem_append_right _ (by simp [recorded]))

theorem projection_iff (state : GeneralNominalState.State) (report : Report state)
 (same : Agree (sources state report) first last) : ProjectionModels state report first ↔ ProjectionModels state report last := by
 unfold ProjectionModels
 apply and_congr
 · apply forall_congr'; intro anchor
   apply forall_congr'; intro member
   have inner : Agree (originSource anchor.1 :: endpoints state anchor.2) first last := by
     intro n h
     exact same n (by simp only [sources,List.mem_append]; exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨anchor,member,h⟩))))
   have root := inner _ (List.mem_cons_self ..)
   have fits (value) := fits_iff state anchor.2 (value := value) (fun n h => inner n (List.mem_cons_of_mem _ h))
   simp only [observes_iff anchor.1 root,fits]
 apply and_congr
 · apply forall_congr'; intro test
   apply forall_congr'; intro member
   have root := same (originSource test.1) (by
     simp only [sources,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨test,member,rfl⟩))))
   simp only [observes_iff test.1 root]
 apply and_congr
 · apply forall_congr'; intro a
   apply forall_congr'; intro am
   apply forall_congr'; intro b
   apply forall_congr'; intro bm
   apply forall_congr'; intro _names
   apply forall_congr'; intro origin
   apply forall_congr'; intro recorded
   have root := capture_origin state report same a am recorded
   have fits (value) := fits_iff state b.bounds (value := value)
     (fun n h => capture_agree state report same b bm n (List.mem_append_left _ h))
   simp only [observes_iff origin root,fits]
 · apply forall_congr'; intro a
   apply forall_congr'; intro am
   apply forall_congr'; intro b
   apply forall_congr'; intro bm
   apply forall_congr'; intro _names
   apply forall_congr'; intro x
   apply forall_congr'; intro y
   apply forall_congr'; intro ax
   apply forall_congr'; intro byy
   simp only [observes_iff x (capture_origin state report same a am ax),
     observes_iff y (capture_origin state report same b bm byy)]

theorem report_endpoints (state : GeneralNominalState.State) (report : Report state) :
 GeneralNominalAllocationSupport.Endpoints (bindings state report) (sources state report) := by
 intro entry member
 obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
 have included : captureSources state capture ⊆ sources state report := by
   intro n h
   simp only [sources,List.mem_append]
   exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨capture,present,h⟩))
 exact ⟨included (List.mem_append_left _ (List.mem_cons_self ..)),
   included (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem checks_sources (state : GeneralNominalState.State) (report : Report state) (atom)
 (member : atom ∈ selfChecks state report) : GeneralNominalState.atomSources atom ⊆ sources state report := by
 obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
 intro n h
 have within : n ∈ endpoints state bounds := by simpa [endpoints,GeneralNominalState.atomSources,GeneralNominalState.typeSources] using h
 exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨bounds,present,within⟩)
end Yulang.GeneralNominalReportSupport237
