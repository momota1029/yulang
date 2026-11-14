import Yulang.GeneralNominalCaptureEnrichment188

/-! Arbitrarily many point roots may mix variable, scalar and nominal queries.
Nominal descendants are unrestricted. Existing cross-capture constraints link
new point origins to retained nominal origins; no distinct-name premise occurs. -/
namespace Yulang.GeneralNominalMixedOriginEnrichment188
open GeneralNominalRecursiveInspection GeneralNominalCaptureEnrichment188
open GeneralNominalPointOriginEnrichment188
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

inductive Supported : Query → Prop
  | variables (names : List Nat) : Supported (.variables names)
  | scalar (base : Inference.Base) : Supported (.scalar base)
  | nominal (name : Nat) (patterns : List Query) : Supported (.nominal name patterns)

structure Facts (state : GeneralNominalState.State) (old fresh : Report state) (model : Assignment) : Prop where
  links : ∀ capture ∈ fresh.captures, ∃ previous ∈ old.captures, Link previous capture
  anchors : ∀ anchor ∈ fresh.anchors, (∃ value, Observes model anchor.1 value) ∧
    ∀ value, Observes model anchor.1 value → Fits state model anchor.2 value
  tests : ∀ test ∈ fresh.tests, ∀ value, Observes model test.1 value → test.2.Holds value

 theorem facts_same (state : GeneralNominalState.State) (old fresh : Report state) (model : Assignment)
    (valid : ProjectionModels state fresh model) (same : fresh.captures = old.captures) :
    Facts state old fresh model := by
  refine ⟨?_,valid.1,valid.2.1⟩
  intro capture member
  rw [same] at member
  exact ⟨capture,member,rfl,rfl,Or.inl rfl⟩

 theorem scalar_point (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (base : Inference.Base) (finished : Finished (inspect state (.scalar base) (slot,slot) none)) :
    ProjectionModels state (inspect state (.scalar base) (slot,slot)
      (some (.source (state.base.source slot)))) model := by
  cases recorded : state.nominals slot with
  | some descriptor => simp [inspect,recorded,Finished,Report.visit] at finished
  | none =>
    simp only [inspect,recorded] at finished ⊢
    cases head : state.view.heads slot with
    | scalar actual =>
      simp only [] at finished ⊢
      by_cases same : base = actual
      · subst actual
        simp only [↓reduceIte]
        apply projection_visit state _ _ _ _ model
        · exact ⟨by simp,by simp,by simp,by simp⟩
        · exact ⟨⟨_,.source _⟩,by intro value seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
        · intro value seen
          cases seen
          exact GeneralNominalInspectionFiniteValues.scalar_slot state model valid slot head
      · simp [head,same,Finished,Report.visit] at finished
    | structural kind children => simp [head,Finished,Report.visit] at finished
    | deferred reason => simp [head,Finished,Report.visit,block] at finished

 theorem single_facts (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query) (supported : Supported query)
    (slot : Fin state.base.slots) (finished : Finished (inspect state query (slot,slot) none))
    (raw : ProjectionModels state (inspect state query (slot,slot) none) model) :
    Facts state (inspect state query (slot,slot) none)
      (inspect state query (slot,slot) (some (.source (state.base.source slot)))) model := by
  cases supported with
  | variables names =>
    refine ⟨?_,?_,?_⟩
    · intro capture member
      simp only [inspect] at member
      obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
      refine ⟨⟨name,(slot,slot),none⟩,(by simpa only [inspect] using (List.mem_map.mpr ⟨name,present,rfl⟩ : (⟨name,(slot,slot),none⟩ : Capture state) ∈ names.map (fun name => ⟨name,(slot,slot),none⟩))),rfl,rfl,?_⟩
      exact Or.inr ⟨rfl,rfl,rfl⟩
    · intro anchor member
      simp only [inspect,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton] at member
      subst anchor
      exact ⟨⟨_,.source _⟩,by intro value seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
    · intro test member; simp only [inspect] at member; cases member
  | scalar base =>
    apply facts_same state _ _ model (scalar_point state model valid slot base finished)
    simp only [inspect,Report.visit]
  | nominal name patterns =>
    exact facts_same state _ _ model (nominal_point state model valid slot name patterns finished raw)
      (nominal_captures state slot name patterns)

 theorem facts_append (state : GeneralNominalState.State) (oldA oldB newA newB : Report state)
    (model : Assignment) (one : Facts state oldA newA model) (two : Facts state oldB newB model) :
    Facts state (oldA.append oldB) (newA.append newB) model := by
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

 theorem many_facts (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query)
    (supported : ∀ query ∈ queries, Supported query) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1)))
    (finished : Finished (inspectMany state queries bounds (fun _ => none) 0))
    (raw : ProjectionModels state (inspectMany state queries bounds (fun _ => none) 0) model) :
    Facts state (inspectMany state queries bounds (fun _ => none) 0)
      (inspectMany state queries bounds origins offset) model := by
  induction queries generalizing bounds offset with
  | nil => cases bounds <;> simp only [inspectMany] <;> exact ⟨by simp,by simp,by simp⟩
  | cons query rest ih =>
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
      have next := ih (fun q member => supported q (List.mem_cons_of_mem _ member)) tail (offset+1) (by
        intro index interval member
        simpa only [Nat.add_assoc,Nat.add_comm 1] using point (index+1) interval (by simpa using member))
        (tailOffset ▸ done.2) (tailOffset ▸ old.2)
      rw [← tailOffset] at next
      have first := single_facts state model valid query (supported query (List.mem_cons_self)) slot done.1 old.1
      rw [p.2]
      exact facts_append state _ _ _ _ model first next

 theorem mixed_many (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query)
    (supported : ∀ query ∈ queries, Supported query) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1)))
    (finished : Finished (inspectMany state queries bounds (fun _ => none) 0))
    (raw : ProjectionModels state (inspectMany state queries bounds (fun _ => none) 0) model)
    (compatible : GeneralNominalAllocation.Compatible
      (bindings state (inspectMany state queries bounds (fun _ => none) 0)) model) :
    ProjectionModels state (inspectMany state queries bounds origins offset) model := by
  have facts := many_facts state model valid queries supported bounds origins offset point finished raw
  exact projection state _ _ model raw compatible facts.links facts.anchors facts.tests

end Yulang.GeneralNominalMixedOriginEnrichment188
