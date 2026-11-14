import Yulang.GeneralNominalStructuralOrigin188

/-! Semantic origin transport preserves the complete inspection projection
judgment, including cross-name constraints and both existence and universal
parts of each anchor. Origin syntax need not agree. -/
namespace Yulang.GeneralNominalReportTransport188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalStructuralOrigin188
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

inductive Optional (model : Assignment) : Option Origin → Option Origin → Prop
  | none : Optional model none none
  | some {first last} : Similar model first last → Optional model (some first) (some last)

 theorem optional_some (related : Optional model (some first) last) :
    ∃ origin, last = some origin ∧ Similar model first origin := by
  cases related with
  | some same => exact ⟨_,rfl,same⟩

structure Related (model : Assignment) (first last : Report state) : Prop where
  captures : ∀ a ∈ first.captures, ∃ b ∈ last.captures,
    a.name = b.name ∧ a.bounds = b.bounds ∧ Optional model a.origin b.origin
  anchors : ∀ a ∈ first.anchors, ∃ b ∈ last.anchors,
    a.2 = b.2 ∧ Similar model a.1 b.1
  tests : ∀ a ∈ first.tests, ∃ b ∈ last.tests,
    a.2 = b.2 ∧ Similar model a.1 b.1

 theorem test_transport (test : Test) (same : Equivalent first last) (valid : test.Holds last) : test.Holds first := by
  cases test with
  | scalar base => exact ⟨subtype_trans same.1 valid.1,subtype_trans valid.2 same.2⟩
  | structural shape =>
    obtain ⟨values,length,equal⟩ := valid
    exact ⟨values,length,subtype_trans same.1 equal.1,subtype_trans equal.2 same.2⟩
  | nominal name arity =>
    obtain ⟨values,length,equal⟩ := valid
    exact ⟨values,length,subtype_trans same.1 equal.1,subtype_trans equal.2 same.2⟩

 theorem projection (state : GeneralNominalState.State) (first last : Report state)
    (related : Related model first last) (valid : ProjectionModels state last model) :
    ProjectionModels state first model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    obtain ⟨old,present,bounds,same⟩ := related.anchors anchor member
    obtain ⟨⟨value,seen⟩,fits⟩ := valid.1 old present
    obtain ⟨actual,observed,_⟩ := same.2 value seen
    refine ⟨⟨actual,observed⟩,?_⟩
    intro actual observed
    obtain ⟨other,seen,equal⟩ := same.1 actual observed
    have result := fits other seen
    rw [bounds]
    exact ⟨subtype_trans result.1 equal.2,subtype_trans equal.1 result.2⟩
  · intro test member actual observed
    obtain ⟨old,present,testEq,same⟩ := related.tests test member
    obtain ⟨other,seen,equal⟩ := same.1 actual observed
    rw [testEq]
    exact test_transport old.2 equal (valid.2.1 old present other seen)
  · intro a ha b hb names origin located actual observed
    obtain ⟨oldA,presentA,nameA,boundsA,originA⟩ := related.captures a ha
    obtain ⟨oldB,presentB,nameB,boundsB,originB⟩ := related.captures b hb
    rw [located] at originA
    obtain ⟨oldOrigin,oldAt,similar⟩ := optional_some originA
    obtain ⟨other,seen,equal⟩ := similar.1 actual observed
    have result := valid.2.2.1 oldA presentA oldB presentB
      (nameA.symm.trans (names.trans nameB)) _ oldAt other seen
    rw [boundsB]
    exact ⟨subtype_trans result.1 equal.2,subtype_trans equal.1 result.2⟩
  · intro a ha b hb names first last firstAt lastAt x y one two
    obtain ⟨oldA,presentA,nameA,_,originA⟩ := related.captures a ha
    obtain ⟨oldB,presentB,nameB,_,originB⟩ := related.captures b hb
    rw [firstAt] at originA
    rw [lastAt] at originB
    obtain ⟨oldFirst,oldFirstAt,similarA⟩ := optional_some originA
    obtain ⟨oldLast,oldLastAt,similarB⟩ := optional_some originB
    obtain ⟨oldX,seenX,equalX⟩ := similarA.1 x one
    obtain ⟨oldY,seenY,equalY⟩ := similarB.1 y two
    have result := valid.2.2.2 oldA presentA oldB presentB
      (nameA.symm.trans (names.trans nameB)) _ _ oldFirstAt oldLastAt oldX oldY seenX seenY
    exact ⟨subtype_trans equalX.1 (subtype_trans result.1 equalY.2),
      subtype_trans equalY.1 (subtype_trans result.2 equalX.2)⟩

 theorem optional_refl (model : Assignment) (origin : Option Origin) : Optional model origin origin := by
  cases origin with
  | none => exact .none
  | some origin => exact .some (similar_refl model origin)

 theorem related_refl (model : Assignment) (report : Report state) : Related model report report :=
  ⟨fun a h => ⟨a,h,rfl,rfl,optional_refl model a.origin⟩,
    fun a h => ⟨a,h,rfl,similar_refl model a.1⟩,
    fun a h => ⟨a,h,rfl,similar_refl model a.1⟩⟩

 theorem related_append (one : Related model a b) (two : Related model c d) :
    Related model (a.append c) (b.append d) := by
  refine ⟨?_,?_,?_⟩
  · intro item member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨old,present,link⟩ := one.captures item member
      exact ⟨old,List.mem_append_left _ present,link⟩
    · obtain ⟨old,present,link⟩ := two.captures item member
      exact ⟨old,List.mem_append_right _ present,link⟩
  · intro item member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨old,present,link⟩ := one.anchors item member
      exact ⟨old,List.mem_append_left _ present,link⟩
    · obtain ⟨old,present,link⟩ := two.anchors item member
      exact ⟨old,List.mem_append_right _ present,link⟩
  · intro item member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨old,present,link⟩ := one.tests item member
      exact ⟨old,List.mem_append_left _ present,link⟩
    · obtain ⟨old,present,link⟩ := two.tests item member
      exact ⟨old,List.mem_append_right _ present,link⟩

 theorem related_visit (first last : Report state) (bounds) (test)
    (related : Related model first last) (origins : Optional model one two) :
    Related model (first.visit bounds one test) (last.visit bounds two test) := by
  cases origins with
  | none => exact ⟨related.captures,related.anchors,related.tests⟩
  | @some a b same =>
    refine ⟨related.captures,?_,?_⟩
    · intro anchor member
      simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨(b,bounds),by simp [Report.visit],rfl,same⟩
      · obtain ⟨old,present,link⟩ := related.anchors anchor member
        exact ⟨old,by simp [Report.visit,present],link⟩
    · intro checked member
      simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨(b,test),by simp [Report.visit],rfl,same⟩
      · obtain ⟨old,present,link⟩ := related.tests checked member
        exact ⟨old,by simp [Report.visit,present],link⟩

end Yulang.GeneralNominalReportTransport188
