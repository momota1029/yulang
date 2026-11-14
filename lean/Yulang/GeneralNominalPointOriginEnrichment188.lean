import Yulang.GeneralNominalHeadInitialCommon188
import Yulang.GeneralNominalInspectionAlignment

/-! Enriching a completed point-root nominal inspection with its actual source
origin retains arbitrary descendant constraints, including nonpoint invariant
arguments. No pointness condition is imposed on nested descriptors. -/
namespace Yulang.GeneralNominalPointOriginEnrichment188
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

 theorem projection_visit (state : GeneralNominalState.State) (report : Report state)
    (bounds : Bounds state) (origin : Origin) (test : Test) (model : Assignment)
    (valid : ProjectionModels state report model)
    (anchor : (∃ actual, Observes model origin actual) ∧
      ∀ actual, Observes model origin actual → Fits state model bounds actual)
    (tested : ∀ actual, Observes model origin actual → test.Holds actual) :
    ProjectionModels state (report.visit bounds (some origin) test) model := by
  refine ⟨?_,?_,valid.2.2.1,valid.2.2.2⟩
  · intro entry member
    simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
    rcases member with rfl | member
    · exact anchor
    · exact valid.1 entry member
  · intro entry member
    simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
    rcases member with rfl | member
    · exact tested
    · exact valid.2.1 entry member

 theorem projection_visit_none (state : GeneralNominalState.State) (report : Report state)
    (bounds : Bounds state) (test : Test) (model : Assignment) :
    ProjectionModels state (report.visit bounds none test) model ↔ ProjectionModels state report model := Iff.rfl

 theorem nominal_enrichment (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (patterns : List Query)
    (intervals : List (Bounds state))
    (arguments : typeArguments descriptor.arguments = some intervals)
    (finished : Finished (inspect state (.nominal descriptor.declaration.name patterns) (slot,slot) none))
    (raw : ProjectionModels state (inspect state (.nominal descriptor.declaration.name patterns) (slot,slot) none) model) :
    ProjectionModels state (inspect state (.nominal descriptor.declaration.name patterns) (slot,slot)
      (some (.source (state.base.source slot)))) model := by
  have bodyFinished : Finished (inspectMany state patterns intervals
      (fun index => some (.nominal (.source (state.base.source slot)) descriptor.declaration.name index)) 0) := by
    simpa only [inspect,recorded,arguments,↓reduceIte,Option.getD_none,
      GeneralNominalInspectionAlignment.finished_visit] using finished
  have length := GeneralNominalInspectionAlignment.finished_length state patterns intervals _ 0 bodyFinished
  have body : ProjectionModels state (inspectMany state patterns intervals
      (fun index => some (.nominal (.source (state.base.source slot)) descriptor.declaration.name index)) 0) model := by
    simpa only [inspect,recorded,arguments,↓reduceIte,Option.getD_none,projection_visit_none] using raw
  simp only [inspect,recorded,arguments,↓reduceIte,Option.getD_some]
  apply projection_visit state _ (slot,slot) _ _ model body
  · exact ⟨⟨_,.source _⟩,by intro actual observed; cases observed; exact ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro actual observed
    cases observed
    obtain ⟨values,fits,equal⟩ := valid.2.1 slot descriptor recorded
    rw [GeneralNominalInspectionFiniteValues.type_arguments _ arguments] at fits
    have size := GeneralNominalInspectionFiniteValues.fits_types_length fits
    exact ⟨values,size.symm.trans length.symm,equal⟩

 theorem nominal_point (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (name : Nat) (patterns : List Query)
    (finished : Finished (inspect state (.nominal name patterns) (slot,slot) none))
    (raw : ProjectionModels state (inspect state (.nominal name patterns) (slot,slot) none) model) :
    ProjectionModels state (inspect state (.nominal name patterns) (slot,slot)
      (some (.source (state.base.source slot)))) model := by
  cases recorded : state.nominals slot with
  | none =>
    simp only [inspect,recorded] at finished
    split at finished <;> simp [Finished,block,Report.visit] at finished
  | some descriptor =>
    by_cases same : descriptor.declaration.name = name
    · subst name
      cases arguments : typeArguments descriptor.arguments with
      | none => simp [inspect,recorded,arguments,Finished,block,Report.visit] at finished
      | some intervals => exact nominal_enrichment state model valid slot descriptor recorded patterns intervals arguments finished raw
    · simp [inspect,recorded,same,Finished,Report.visit] at finished

 theorem nominal_captures (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name : Nat) (patterns : List Query) :
    (inspect state (.nominal name patterns) (slot,slot)
      (some (.source (state.base.source slot)))).captures =
    (inspect state (.nominal name patterns) (slot,slot) none).captures := by
  simp only [inspect,Report.visit,Option.getD_none,Option.getD_some]

 theorem projection_subset (state : GeneralNominalState.State) (first last : Report state)
    (model : Assignment) (valid : ProjectionModels state last model)
    (anchors : first.anchors ⊆ last.anchors) (tests : first.tests ⊆ last.tests)
    (captures : first.captures ⊆ last.captures) : ProjectionModels state first model :=
  ⟨fun entry member => valid.1 entry (anchors member),
    fun entry member => valid.2.1 entry (tests member),
    fun a ha b hb => valid.2.2.1 a (captures ha) b (captures hb),
    fun a ha b hb => valid.2.2.2 a (captures ha) b (captures hb)⟩

 theorem projection_parts (state : GeneralNominalState.State) (first last : Report state)
    (model : Assignment) (valid : ProjectionModels state (first.append last) model) :
    ProjectionModels state first model ∧ ProjectionModels state last model :=
  ⟨projection_subset state first _ model valid
      (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h),
    projection_subset state last _ model valid
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)⟩

 theorem projection_recombine (state : GeneralNominalState.State) (raw : Report state)
    (first last : Report state) (model : Assignment)
    (valid : ProjectionModels state raw model)
    (one : ProjectionModels state first model) (two : ProjectionModels state last model)
    (captures : (first.append last).captures = raw.captures) :
    ProjectionModels state (first.append last) model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact one.1 entry member
    · exact two.1 entry member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact one.2.1 entry member
    · exact two.2.1 entry member
  · intro a ha b hb
    rw [captures] at ha hb
    exact valid.2.2.1 a ha b hb
  · intro a ha b hb
    rw [captures] at ha hb
    exact valid.2.2.2 a ha b hb

 theorem none_offset (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (offset : Nat) :
    inspectMany state queries bounds (fun _ => none) offset =
      inspectMany state queries bounds (fun _ => none) 0 := by
  induction queries generalizing bounds offset with
  | nil => cases bounds <;> simp only [inspectMany]
  | cons query rest ih =>
    cases bounds with
    | nil => simp only [inspectMany]
    | cons head tail =>
      simp only [inspectMany]
      rw [ih tail (offset+1),ih tail 1]

 theorem nominal_many (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (items : List (Nat × List Query))
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (point : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (offset + index) = some (.source (state.base.source interval.1)))
    (finished : Finished (inspectMany state (items.map fun item => Query.nominal item.1 item.2) bounds (fun _ => none) 0))
    (raw : ProjectionModels state (inspectMany state (items.map fun item => Query.nominal item.1 item.2) bounds (fun _ => none) 0) model) :
    ProjectionModels state (inspectMany state (items.map fun item => Query.nominal item.1 item.2) bounds origins offset) model ∧
      (inspectMany state (items.map fun item => Query.nominal item.1 item.2) bounds origins offset).captures =
      (inspectMany state (items.map fun item => Query.nominal item.1 item.2) bounds (fun _ => none) 0).captures := by
  induction items generalizing bounds offset with
  | nil => cases bounds <;> simp only [List.map_nil,inspectMany] at raw ⊢ <;> exact ⟨raw,True.intro⟩
  | cons item rest ih =>
    cases bounds with
    | nil => simp only [List.map_cons,inspectMany] at raw ⊢; exact ⟨raw,True.intro⟩
    | cons head tail =>
      simp only [List.map_cons,inspectMany] at raw finished ⊢
      have p := point 0 head (by simp)
      simp only [Nat.add_zero] at p
      obtain ⟨slot,other⟩ := head
      dsimp only at p
      have equal := p.1
      subst other
      have old := projection_parts state _ _ model raw
      have done := (GeneralNominalInspectionAlignment.finished_append _ _).mp finished
      have tailOffset : inspectMany state (rest.map fun item => Query.nominal item.1 item.2) tail (fun _ => none) 1 =
          inspectMany state (rest.map fun item => Query.nominal item.1 item.2) tail (fun _ => none) 0 := by
        exact none_offset state _ tail 1
      have next := ih tail (offset+1) (by
        intro index interval member
        simpa only [Nat.add_assoc,Nat.add_comm 1] using point (index+1) interval (by simpa using member))
        (tailOffset ▸ done.2) (tailOffset ▸ old.2)
      have first := nominal_point state model valid slot item.1 item.2 done.1 old.1
      have firstCaptures := nominal_captures state slot item.1 item.2
      simp only [p.2]
      have captures : ((inspect state (.nominal item.1 item.2) (slot,slot) (some (.source (state.base.source slot)))).append
          (inspectMany state (rest.map fun item => Query.nominal item.1 item.2) tail origins (offset+1))).captures = (inspectMany state (List.map (fun item => Query.nominal item.1 item.2) (item::rest))
          ((slot,slot)::tail) (fun _ => none) 0).captures := by
        simp only [List.map_cons,inspectMany,Report.append,firstCaptures,next.2,tailOffset]
      simp only [List.map_cons,inspectMany] at captures
      exact ⟨projection_recombine state _ _ _ model raw first next.1 captures,captures⟩

end Yulang.GeneralNominalPointOriginEnrichment188
