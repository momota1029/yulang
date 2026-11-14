import Yulang.GeneralNominalPointOriginEnrichment188

/-! Adding actual origins to point variable captures preserves cross-name
constraints, including sharing with preexisting nominal projection captures. -/
namespace Yulang.GeneralNominalCaptureEnrichment188
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

structure Link (old fresh : Capture state) : Prop where
  name : old.name = fresh.name
  bounds : old.bounds = fresh.bounds
  origin : old.origin = fresh.origin ∨
    old.origin = none ∧ fresh.bounds.1 = fresh.bounds.2 ∧
      fresh.origin = some (.source (state.base.source fresh.bounds.1))

 theorem projection (state : GeneralNominalState.State) (old fresh : Report state)
    (model : Assignment) (raw : ProjectionModels state old model)
    (compatible : GeneralNominalAllocation.Compatible (bindings state old) model)
    (links : ∀ capture ∈ fresh.captures, ∃ previous ∈ old.captures, Link previous capture)
    (anchors : ∀ anchor ∈ fresh.anchors, (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits state model anchor.2 value)
    (tests : ∀ test ∈ fresh.tests, ∀ value, Observes model test.1 value → test.2.Holds value) :
    ProjectionModels state fresh model := by
  have binding (entry : Capture state) (present : entry ∈ old.captures) :
      (entry.name,state.base.source entry.bounds.1,state.base.source entry.bounds.2) ∈ bindings state old :=
    List.mem_map.mpr ⟨entry,present,rfl⟩
  have fits (a : Capture state) (ha : a ∈ fresh.captures) (b : Capture state) (hb : b ∈ fresh.captures)
      (same : a.name = b.name) (origin : Origin) (located : a.origin = some origin)
      (actual : Ty) (seen : Observes model origin actual) : Fits state model b.bounds actual := by
    obtain ⟨x,hx,lx⟩ := links a ha
    obtain ⟨y,hy,ly⟩ := links b hb
    have names : x.name = y.name := lx.name.trans (same.trans ly.name.symm)
    rcases lx.origin with previous | ⟨_,point,source⟩
    · rw [← ly.bounds]
      exact raw.2.2.1 x hx y hy names origin (previous.trans located) actual seen
    · cases Option.some.inj (source.symm.trans located)
      cases seen
      constructor
      · have below := compatible _ (binding y hy) _ (binding x hx) names.symm
        simpa only [lx.bounds,ly.bounds,← point] using below
      · have above := compatible _ (binding x hx) _ (binding y hy) names
        simpa only [lx.bounds,ly.bounds] using above
  refine ⟨anchors,tests,fits,?_⟩
  intro a ha b hb same first last firstAt lastAt x y one two
  obtain ⟨oldA,presentA,linkA⟩ := links a ha
  obtain ⟨oldB,presentB,linkB⟩ := links b hb
  rcases linkA.origin with sameA | ⟨_,pointA,sourceA⟩
  · rcases linkB.origin with sameB | ⟨_,pointB,sourceB⟩
    · exact raw.2.2.2 oldA presentA oldB presentB
        (linkA.name.trans (same.trans linkB.name.symm)) first last
        (sameA.trans firstAt) (sameB.trans lastAt) x y one two
    · cases Option.some.inj (sourceB.symm.trans lastAt)
      cases two
      have fit := fits a ha b hb same first firstAt x one
      exact ⟨by simpa only [← pointB] using fit.2,fit.1⟩
  · cases Option.some.inj (sourceA.symm.trans firstAt)
    cases one
    have fit := fits b hb a ha same.symm last lastAt y two
    exact ⟨fit.1,by simpa only [← pointA] using fit.2⟩

end Yulang.GeneralNominalCaptureEnrichment188
