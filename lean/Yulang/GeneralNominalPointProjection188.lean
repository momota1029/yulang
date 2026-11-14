import Yulang.GeneralNominalHeadBranchFrame187

/-! Point-variable inspection retains repeated-name constraints from the real
cross matrix. No projection-model premise is required for this query class. -/
namespace Yulang.GeneralNominalPointProjection188
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

structure PointReport (report : Report state) : Prop where
  tests : report.tests = []
  anchors : ∀ entry ∈ report.anchors,
    entry.1 = .source (state.base.source entry.2.1) ∧ entry.2.1 = entry.2.2
  captures : ∀ entry ∈ report.captures,
    entry.origin = some (.source (state.base.source entry.bounds.1)) ∧ entry.bounds.1 = entry.bounds.2

theorem point_append (first last : Report state)
    (one : PointReport first) (two : PointReport last) : PointReport (first.append last) := by
  refine ⟨by simp [Report.append,one.tests,two.tests],?_,?_⟩
  · intro entry present
    rcases List.mem_append.mp present with h | h
    · exact one.anchors entry h
    · exact two.anchors entry h
  · intro entry present
    rcases List.mem_append.mp present with h | h
    · exact one.captures entry h
    · exact two.captures entry h

theorem point_many (state : GeneralNominalState.State)
    (names : List (List Nat)) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1))) :
    PointReport (inspectMany state (names.map Query.variables) bounds origins offset) := by
  induction names generalizing bounds offset with
  | nil => cases bounds <;> exact ⟨by simp [inspectMany],by simp [inspectMany],by simp [inspectMany]⟩
  | cons names rest ih =>
    cases bounds with
    | nil => exact ⟨by simp [inspectMany],by simp [inspectMany],by simp [inspectMany]⟩
    | cons head tail =>
      have p := point 0 head (by simp)
      simp only [Nat.add_zero] at p
      simp only [List.map_cons,inspectMany]
      apply point_append
      · refine ⟨by simp [inspect],?_,?_⟩
        · intro entry present
          simp only [inspect,p.2,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton] at present
          subst entry
          exact ⟨rfl,p.1⟩
        · intro entry present
          simp only [inspect] at present
          obtain ⟨name,_,rfl⟩ := List.mem_map.mp present
          exact ⟨p.2,p.1⟩
      · apply ih tail (offset+1)
        intro index interval present
        simpa only [Nat.add_assoc,Nat.add_comm 1] using point (index+1) interval (by simpa using present)

theorem point_projection (state : GeneralNominalState.State) (report : Report state)
    (point : PointReport report) (model : Assignment)
    (compatible : GeneralNominalAllocation.Compatible (bindings state report) model) :
    ProjectionModels state report model := by
  have binding (entry : Capture state) (present : entry ∈ report.captures) :
      (entry.name,state.base.source entry.bounds.1,state.base.source entry.bounds.2) ∈ bindings state report :=
    List.mem_map.mpr ⟨entry,present,rfl⟩
  have cross (first last : Capture state) (one : first ∈ report.captures)
      (two : last ∈ report.captures) (same : first.name = last.name) :
      Equivalent (model (state.base.source first.bounds.1)).1 (model (state.base.source last.bounds.1)).1 := by
    constructor
    · simpa only [← (point.captures last two).2] using compatible _ (binding first one) _ (binding last two) same
    · simpa only [← (point.captures first one).2] using compatible _ (binding last two) _ (binding first one) same.symm
  refine ⟨?_,?_,?_,?_⟩
  · intro entry present
    obtain ⟨origin,equal⟩ := point.anchors entry present
    rw [origin]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    exact ⟨subtype_refl _,by rw [← equal]; exact subtype_refl _⟩
  · intro test present
    rw [point.tests] at present
    cases present
  · intro first one last two same ref origin actual observed
    have source := (point.captures first one).1.symm.trans origin
    cases Option.some.inj source
    cases observed
    have equal := cross first last one two same
    exact ⟨equal.2,by rw [← (point.captures last two).2]; exact equal.1⟩
  · intro first one last two same a b originA originB x y seenX seenY
    have sourceA := (point.captures first one).1.symm.trans originA
    have sourceB := (point.captures last two).1.symm.trans originB
    cases Option.some.inj sourceA
    cases Option.some.inj sourceB
    cases seenX
    cases seenY
    exact cross first last one two same

theorem point_projection_iff (state : GeneralNominalState.State) (report : Report state)
    (point : PointReport report) (model : Assignment) :
    ProjectionModels state report model ↔
      GeneralNominalAllocation.Compatible (bindings state report) model := by
  constructor
  · intro projected first one last two same
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp one
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp two
    exact (projected.2.2.1 a ha b hb same _ (point.captures a ha).1 _ (.source _)).2
  · exact point_projection state report point model

end Yulang.GeneralNominalPointProjection188
