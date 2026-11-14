import Yulang.GeneralNominalCaptureEnrichment188
import Yulang.GeneralNominalInspectionTransport188

/-! Semantic capture enrichment composes point-origin insertion with recursive
origin transport. Cross constraints retain both recorded and newly named uses. -/
namespace Yulang.GeneralNominalSemanticEnrichment188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

 theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

 theorem similar_trans (one : Similar model a b) (two : Similar model b c) : Similar model a c := by
  constructor
  · intro value seen
    obtain ⟨middle,seenM,equalM⟩ := one.1 value seen
    obtain ⟨last,seenL,equalL⟩ := two.1 middle seenM
    exact ⟨last,seenL,equivalent_trans equalM equalL⟩
  · intro value seen
    obtain ⟨middle,seenM,equalM⟩ := two.2 value seen
    obtain ⟨last,seenL,equalL⟩ := one.2 middle seenM
    exact ⟨last,seenL,equivalent_trans equalM equalL⟩

 theorem similar_source (same : Similar model origin (.source source)) (seen : Observes model origin value) :
    Equivalent value (model source).1 := by
  obtain ⟨other,observed,equal⟩ := same.1 value seen
  cases observed
  exact equal

structure Link (model : Assignment) (old fresh : Capture state) : Prop where
  name : old.name = fresh.name
  bounds : old.bounds = fresh.bounds
  origins : ∀ origin, fresh.origin = some origin →
    (∃ previous, old.origin = some previous ∧ Similar model origin previous) ∨
    (old.origin = none ∧ fresh.bounds.1 = fresh.bounds.2 ∧
      Similar model origin (.source (state.base.source fresh.bounds.1)))

 theorem from_syntactic (link : GeneralNominalCaptureEnrichment188.Link old fresh) : Link model old fresh := by
  refine ⟨link.name,link.bounds,?_⟩
  intro origin found
  rcases link.origin with same | ⟨missing,point,source⟩
  · exact Or.inl ⟨origin,same.trans found,GeneralNominalStructuralOrigin188.similar_refl _ _⟩
  · cases Option.some.inj (source.symm.trans found)
    exact Or.inr ⟨missing,point,GeneralNominalStructuralOrigin188.similar_refl _ _⟩

 theorem transported (link : Link model old middle)
    (name : fresh.name = middle.name) (bounds : fresh.bounds = middle.bounds)
    (origins : GeneralNominalReportTransport188.Optional model fresh.origin middle.origin) : Link model old fresh := by
  refine ⟨link.name.trans name.symm,link.bounds.trans bounds.symm,?_⟩
  intro origin found
  rw [found] at origins
  obtain ⟨mid,midAt,similar⟩ := GeneralNominalReportTransport188.optional_some origins
  rcases link.origins mid midAt with ⟨previous,present,same⟩ | ⟨missing,point,same⟩
  · exact Or.inl ⟨previous,present,similar_trans similar same⟩
  · apply Or.inr
    rw [bounds]
    exact ⟨missing,point,similar_trans similar same⟩

 theorem projection (state : GeneralNominalState.State) (old fresh : Report state)
    (model : Assignment) (raw : ProjectionModels state old model)
    (compatible : GeneralNominalAllocation.Compatible (bindings state old) model)
    (links : ∀ capture ∈ fresh.captures, ∃ previous ∈ old.captures, Link model previous capture)
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
    rcases lx.origins origin located with ⟨previous,present,relation⟩ | ⟨_,point,relation⟩
    · obtain ⟨other,observed,equal⟩ := relation.1 actual seen
      have result := raw.2.2.1 x hx y hy names previous present other observed
      rw [ly.bounds] at result
      exact ⟨subtype_trans result.1 equal.2,subtype_trans equal.1 result.2⟩
    · have equal := similar_source relation seen
      have below := compatible _ (binding y hy) _ (binding x hx) names.symm
      have above := compatible _ (binding x hx) _ (binding y hy) names
      simp only [lx.bounds,ly.bounds,← point] at below
      simp only [lx.bounds,ly.bounds] at above
      exact ⟨subtype_trans below equal.2,subtype_trans equal.1 above⟩
  refine ⟨anchors,tests,fits,?_⟩
  intro a ha b hb same first last firstAt lastAt x y one two
  obtain ⟨oldA,presentA,linkA⟩ := links a ha
  obtain ⟨oldB,presentB,linkB⟩ := links b hb
  rcases linkA.origins first firstAt with ⟨beforeA,atA,relationA⟩ | ⟨_,pointA,relationA⟩
  · rcases linkB.origins last lastAt with ⟨beforeB,atB,relationB⟩ | ⟨_,pointB,relationB⟩
    · obtain ⟨oldX,seenX,equalX⟩ := relationA.1 x one
      obtain ⟨oldY,seenY,equalY⟩ := relationB.1 y two
      have result := raw.2.2.2 oldA presentA oldB presentB
        (linkA.name.trans (same.trans linkB.name.symm)) beforeA beforeB atA atB oldX oldY seenX seenY
      exact equivalent_trans equalX (equivalent_trans result ⟨equalY.2,equalY.1⟩)
    · have fit := fits a ha b hb same first firstAt x one
      have source : Equivalent x (model (state.base.source b.bounds.1)).1 :=
        ⟨by simpa only [← pointB] using fit.2,fit.1⟩
      have lastEq := similar_source relationB two
      exact equivalent_trans source ⟨lastEq.2,lastEq.1⟩
  · have fit := fits b hb a ha same.symm last lastAt y two
    have source : Equivalent y (model (state.base.source a.bounds.1)).1 :=
      ⟨by simpa only [← pointA] using fit.2,fit.1⟩
    exact equivalent_trans (similar_source relationA one) ⟨source.2,source.1⟩

end Yulang.GeneralNominalSemanticEnrichment188
