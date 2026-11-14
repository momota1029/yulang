import Yulang.GeneralNominalSemanticEnrichment188
import Yulang.GeneralNominalMixedOriginEnrichment188

/-! Recursive point-root origin enrichment. Structural children are related
semantically to physical source slots; nominal boundaries retain arbitrary
nonpoint descendants. No restricted query class is required. -/
namespace Yulang.GeneralNominalRecursiveEnrichment188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalStructuralOrigin188 GeneralNominalReportTransport188
open GeneralNominalPointOriginEnrichment188
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

structure Facts (state : GeneralNominalState.State) (old fresh : Report state) (model : Assignment) : Prop where
  links : ∀ capture ∈ fresh.captures, ∃ previous ∈ old.captures,
    GeneralNominalSemanticEnrichment188.Link model previous capture
  anchors : ∀ anchor ∈ fresh.anchors, (∃ value, Observes model anchor.1 value) ∧
    ∀ value, Observes model anchor.1 value → Fits state model anchor.2 value
  tests : ∀ test ∈ fresh.tests, ∀ value, Observes model test.1 value → test.2.Holds value

 theorem from_mixed (valid : GeneralNominalMixedOriginEnrichment188.Facts state old fresh model) :
    Facts state old fresh model := by
  refine ⟨?_,valid.anchors,valid.tests⟩
  intro entry member
  obtain ⟨previous,present,link⟩ := valid.links entry member
  exact ⟨previous,present,GeneralNominalSemanticEnrichment188.from_syntactic link⟩

 theorem append (one : Facts state a b model) (two : Facts state c d model) :
    Facts state (a.append c) (b.append d) model := by
  refine ⟨?_,?_,?_⟩
  · intro capture member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨previous,present,link⟩ := one.links capture member
      exact ⟨previous,List.mem_append_left _ present,link⟩
    · obtain ⟨previous,present,link⟩ := two.links capture member
      exact ⟨previous,List.mem_append_right _ present,link⟩
  · intro anchor member
    rcases List.mem_append.mp member with member | member
    · exact one.anchors anchor member
    · exact two.anchors anchor member
  · intro test member
    rcases List.mem_append.mp member with member | member
    · exact one.tests test member
    · exact two.tests test member

 theorem transport (valid : Facts state old middle model) (related : Related model fresh middle) :
    Facts state old fresh model := by
  refine ⟨?_,?_,?_⟩
  · intro entry member
    obtain ⟨mid,present,name,bounds,origins⟩ := related.captures entry member
    obtain ⟨previous,inhabited,link⟩ := valid.links mid present
    exact ⟨previous,inhabited,GeneralNominalSemanticEnrichment188.transported link name bounds origins⟩
  · intro anchor member
    obtain ⟨mid,present,bounds,same⟩ := related.anchors anchor member
    obtain ⟨⟨value,seen⟩,fits⟩ := valid.anchors mid present
    obtain ⟨actual,observed,_⟩ := same.2 value seen
    refine ⟨⟨actual,observed⟩,?_⟩
    intro actual observed
    obtain ⟨other,seen,equal⟩ := same.1 actual observed
    have result := fits other seen
    rw [bounds]
    exact ⟨subtype_trans result.1 equal.2,subtype_trans equal.1 result.2⟩
  · intro test member actual observed
    obtain ⟨mid,present,testEq,same⟩ := related.tests test member
    obtain ⟨other,seen,equal⟩ := same.1 actual observed
    rw [testEq]
    exact test_transport mid.2 equal (valid.tests mid present other seen)

 theorem visit (valid : Facts state old fresh model) (slot : Fin state.base.slots) (test : Test)
    (tested : test.Holds (model (state.base.source slot)).1) :
    Facts state (old.visit (slot,slot) none test)
      (fresh.visit (slot,slot) (some (.source (state.base.source slot))) test) model := by
  refine ⟨valid.links,?_,?_⟩
  · intro anchor member
    simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨⟨_,.source _⟩,by intro value seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
    · exact valid.anchors anchor member
  · intro item member value seen
    simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
    rcases member with rfl | member
    · cases seen; exact tested
    · exact valid.tests item member value seen

mutual
 theorem single_facts (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query)
    (slot : Fin state.base.slots) (finished : Finished (inspect state query (slot,slot) none))
    (raw : ProjectionModels state (inspect state query (slot,slot) none) model) :
    Facts state (inspect state query (slot,slot) none)
      (inspect state query (slot,slot) (some (.source (state.base.source slot)))) model := by
  cases query with
  | variables names => exact from_mixed (GeneralNominalMixedOriginEnrichment188.single_facts state model valid _ (.variables names) slot finished raw)
  | scalar base => exact from_mixed (GeneralNominalMixedOriginEnrichment188.single_facts state model valid _ (.scalar base) slot finished raw)
  | nominal name patterns => exact from_mixed (GeneralNominalMixedOriginEnrichment188.single_facts state model valid _ (.nominal name patterns) slot finished raw)
  | deferred reason => simp [inspect,Finished,block] at finished
  | node shape patterns =>
    cases head : state.view.heads slot with
    | scalar base => simp [inspect,head,Finished,Report.visit] at finished
    | deferred reason => simp [inspect,head,Finished,Report.visit,block] at finished
    | structural kind children =>
      by_cases same : state.view.shapes kind = shape
      · subst shape
        let bounds : List (Bounds state) := List.ofFn fun index => (children index,children index)
        let origins : Nat → Option Origin := fun index =>
          if h : index < (state.view.shapes kind).arity then
            some (.source (state.base.source (children ⟨index,h⟩)))
          else some (.structural (.source (state.base.source slot)) (state.view.shapes kind) index)
        have zipped : (List.ofFn children).zip (List.ofFn children) = bounds :=
          GeneralNominalInspectionPositions.zip_reindex rfl rfl children children
        have bodyFinished : Finished (inspectMany state patterns bounds (fun _ => none) 0) := by
          simpa only [inspect,head,and_self,↓reduceIte,zipped,Option.map_none,
            GeneralNominalInspectionAlignment.finished_visit] using finished
        have body : ProjectionModels state (inspectMany state patterns bounds (fun _ => none) 0) model := by
          simpa only [inspect,head,and_self,↓reduceIte,zipped,Option.map_none,projection_visit_none] using raw
        have points : ∀ index interval, bounds[index]? = some interval →
            interval.1 = interval.2 ∧ origins (0+index) = some (.source (state.base.source interval.1)) := by
          intro index interval found
          simp only [bounds,List.getElem?_ofFn] at found
          split at found
          · rename_i bounded
            cases Option.some.inj found
            exact ⟨rfl,by simp only [origins,Nat.zero_add,bounded,↓reduceDIte]⟩
          · cases found
        have sourceFacts := many_facts state model valid patterns bounds origins 0 points bodyFinished body
        have related : ∀ index, Optional model
            (some (.structural (.source (state.base.source slot)) (state.view.shapes kind) index)) (origins index) := by
          intro index
          unfold origins
          split
          · rename_i bounded
            exact .some (same_similar (structural_slot_same state model valid slot kind children head ⟨index,bounded⟩))
          · exact .some (similar_refl _ _)
        have projected := transport sourceFacts
          (GeneralNominalInspectionTransport188.many_related state patterns bounds _ origins 0 related)
        simp only [inspect,head,and_self,↓reduceIte,zipped,Option.map_some,Option.map_none]
        apply visit projected slot (.structural (state.view.shapes kind))
        exact ⟨List.ofFn (fun index => (model (state.base.source (children index))).1),List.length_ofFn,
          GeneralNominalFiniteBracket.structural_slot state model valid slot kind children head rfl⟩
      · simp [inspect,head,same,Finished,Report.visit,block] at finished
 termination_by sizeOf query

 theorem many_facts (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1)))
    (finished : Finished (inspectMany state queries bounds (fun _ => none) 0))
    (raw : ProjectionModels state (inspectMany state queries bounds (fun _ => none) 0) model) :
    Facts state (inspectMany state queries bounds (fun _ => none) 0)
      (inspectMany state queries bounds origins offset) model := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany] <;> exact ⟨by simp,by simp,by simp⟩
  | cons query rest =>
    cases bounds with
    | nil => simp only [inspectMany]; exact ⟨by simp,by simp,by simp⟩
    | cons head tail =>
      simp only [inspectMany] at raw finished ⊢
      have p := point 0 head (by simp)
      simp only [Nat.add_zero] at p
      obtain ⟨slot,other⟩ := head
      dsimp only at p
      have equal := p.1
      subst other
      have old := projection_parts state _ _ model raw
      have done := (GeneralNominalInspectionAlignment.finished_append _ _).mp finished
      have tailOffset := none_offset state rest tail 1
      have next := many_facts state model valid rest tail origins (offset+1) (by
        intro index interval member
        simpa only [Nat.add_assoc,Nat.add_comm 1] using point (index+1) interval (by simpa using member))
        (tailOffset ▸ done.2) (tailOffset ▸ old.2)
      rw [← tailOffset] at next
      have first := single_facts state model valid query slot done.1 old.1
      rw [p.2]
      exact append first next
 termination_by sizeOf queries
end

 theorem point_many (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1)))
    (finished : Finished (inspectMany state queries bounds (fun _ => none) 0))
    (raw : ProjectionModels state (inspectMany state queries bounds (fun _ => none) 0) model)
    (compatible : GeneralNominalAllocation.Compatible (bindings state (inspectMany state queries bounds (fun _ => none) 0)) model) :
    ProjectionModels state (inspectMany state queries bounds origins offset) model := by
  have facts := many_facts state model valid queries bounds origins offset point finished raw
  exact GeneralNominalSemanticEnrichment188.projection state _ _ model raw compatible facts.links facts.anchors facts.tests

end Yulang.GeneralNominalRecursiveEnrichment188
