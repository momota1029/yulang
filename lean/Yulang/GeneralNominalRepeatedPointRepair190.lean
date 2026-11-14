import Yulang.GeneralNominalSourceLinearShape190

/-! Repeated variable head centers determine their raw point captures in the
same assignment. No private branch or merge-equation premise is used. These
facts isolate the semantic input for fresh merge-endpoint reconstruction. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRepeatedPointRepair190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalMaterialization
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem schema_variable_at (names : List Nat) (origins : Nat → Origin) (offset index name : Nat)
    (found : names[index]? = some name) :
    (⟨name,origins (offset+index),.actual⟩ : Use) ∈
      (schemas (names.map fun name => .variables [name]) origins .actual offset).variables := by
  induction names generalizing offset index with
  | nil => simp at found
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst name
      simp [schemas,schema,Schema.append]
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      have inner := ih (offset+1) index found
      simp only [List.map_cons,schemas,Schema.append]
      apply List.mem_append_right
      simpa only [Nat.add_assoc,Nat.add_comm 1] using inner

theorem source_equivalent (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (model : Assignment) (head : HeadEquations candidate model)
    (entry : Nat × Fin candidate.packet.context.state.base.slots) (member : entry ∈ entries) :
    Equivalent (model (candidate.packet.context.state.base.source entry.2)).1 (model (candidate.binder entry.1)).1 := by
  obtain ⟨index,bounded,foundEq⟩ := List.mem_iff_getElem.mp member
  have found : entries[index]? = some entry := List.getElem?_eq_some_iff.mpr ⟨bounded,foundEq⟩
  have nameFound : (entries.map Prod.fst)[index]? = some entry.1 := by
    simp only [List.getElem?_map,found,Option.map_some]
  have use := schema_variable_at (entries.map Prod.fst)
    (fun index => .source ((List.ofFn candidate.input.center)[index]?.getD 0)) 0 index entry.1 nameFound
  have present : (⟨entry.1,.source ((List.ofFn candidate.input.center)[index]?.getD 0),.actual⟩ : Use) ∈
      candidate.headSchema.variables := by
    simpa only [Plan.headSchema,query,List.map_map,Function.comp_def,Nat.zero_add] using use
  have same := head.2.2.2 _ present
  have located : candidate.packet.bounds[index]? = some (entry.2,entry.2) := by
    simp only [bounds,List.getElem?_map,found,Option.map_some]
  have center := (GeneralNominalHeadPointBounds188.boundary_initial_point_bounds state source candidate frame
    index (entry.2,entry.2) located).2
  have centers : (List.ofFn candidate.input.center)[index]?.getD 0 =
      candidate.packet.context.state.base.source entry.2 := by
    exact Origin.source.inj (Option.some.inj center)
  simp only [ite_true,centers] at same
  exact same.2.2 _ _ (.source _) (.source _)

theorem repeated_sources_equivalent (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (model : Assignment) (head : HeadEquations candidate model)
    (first last : Nat × Fin candidate.packet.context.state.base.slots)
    (one : first ∈ entries) (two : last ∈ entries) (equal : first.1 = last.1) :
    Equivalent (model (candidate.packet.context.state.base.source first.2)).1
      (model (candidate.packet.context.state.base.source last.2)).1 := by
  have a := source_equivalent source candidate frame entries query bounds model head first one
  have b := source_equivalent source candidate frame entries query bounds model head last two
  rw [equal] at a
  exact ⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩

private theorem variable_report (state : GeneralNominalState.State)
    (entries : List (Nat × Fin state.base.slots)) (index : Nat) :
    inspectMany state (entries.map fun entry => .variables [entry.1])
      (entries.map fun entry => (entry.2,entry.2)) (fun _ => none) index =
    { captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
      checked := entries.map (fun entry => (entry.2,entry.2)) } := by
  induction entries generalizing index with
  | nil => simp [inspectMany]
  | cons first rest ih => simp [inspectMany,inspect,Report.append,ih]

theorem bindings_eq (candidate : Plan roles)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2)) :
    candidate.packet.bindings = entries.map (fun entry =>
      (entry.1,candidate.packet.context.state.base.source entry.2,candidate.packet.context.state.base.source entry.2)) := by
  simp [GeneralNominalSaturationState.Packet.bindings,GeneralNominalRecursiveCandidates.report,
    query,bounds,variable_report,bindings,List.map_map]

theorem cross_compatible (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (model : Assignment) (head : HeadEquations candidate model) :
    GeneralNominalAllocation.Compatible candidate.packet.bindings model := by
  rw [bindings_eq candidate entries query bounds]
  intro first one last two same
  obtain ⟨a,am,rfl⟩ := List.mem_map.mp one
  obtain ⟨b,bm,rfl⟩ := List.mem_map.mp two
  exact (repeated_sources_equivalent source candidate frame entries query bounds model head a b am bm same).1

theorem occurrence_equivalent (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (model : Assignment) (head : HeadEquations candidate model)
    (pair : GeneralSourceState.Interval)
    (member : pair ∈ GeneralNominalAllocation.occurrences candidate.packet.bindings name) :
    Equivalent (model pair.1).1 (model (candidate.binder name)).1 ∧
      Equivalent (model pair.2).1 (model (candidate.binder name)).1 := by
  obtain ⟨binding,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨present,same⟩ := List.mem_filter.mp present
  rw [bindings_eq candidate entries query bounds] at present
  obtain ⟨entry,entryMem,rfl⟩ := List.mem_map.mp present
  have nameEq : entry.1 = name := by simpa using same
  have equal := source_equivalent source candidate frame entries query bounds model head entry entryMem
  rw [nameEq] at equal
  exact ⟨equal,equal⟩

/-- The computed extrema of all repeated point occurrences already have the
correct denotation. Only the allocated endpoint identities still need repair. -/
theorem computed_extrema (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (model : Assignment) (head : HeadEquations candidate model)
    (nonempty : GeneralNominalAllocation.occurrences candidate.packet.bindings name ≠ []) :
    Equivalent ((GeneralNominalAllocation.lower (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval
      CommonNominalFullCarrier.model model) (model (candidate.binder name)).1 ∧
    Equivalent ((GeneralNominalAllocation.upper (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval
      CommonNominalFullCarrier.model model) (model (candidate.binder name)).1 := by
  have each := occurrence_equivalent (name := name) source candidate frame entries query bounds model head
  obtain ⟨pair,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have point := each pair member
  have lowerAll := GeneralNominalCaptureMerges.lower_exact model _ nonempty
  have upperAll := GeneralNominalCaptureMerges.upper_exact model _ nonempty
  refine ⟨⟨(lowerAll _).mpr (fun interval within => (each interval within).1.1),?_⟩,
    ⟨?_,(upperAll _).mpr (fun interval within => (each interval within).2.2)⟩⟩
  · exact subtype_trans point.1.2 ((lowerAll _).mp (subtype_refl _) pair member)
  · exact subtype_trans ((upperAll _).mp (subtype_refl _) pair member) point.2.1

/-- Both fresh extrema reservations are updated for every declared input name.
Singleton captures do not read these reservations. Duplicate declarations of
one name deliberately write the same binder value. -/
def mergeAssignments (candidate : Plan roles) : List (Nat × Nat) :=
  candidate.packet.declaration.inputNames.flatMap fun name =>
    [(fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 0 name 0,name),
     (fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 1 name 0,name)]

private theorem assignments_coherent (candidate : Plan roles) (first last : Nat × Nat)
    (one : first ∈ mergeAssignments candidate) (two : last ∈ mergeAssignments candidate)
    (equal : first.1 = last.1) : first.2 = last.2 := by
  obtain ⟨a,_,one⟩ := List.mem_flatMap.mp one
  obtain ⟨b,_,two⟩ := List.mem_flatMap.mp two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  all_goals
    have same := (GeneralNominalIdentities.source_identity candidate.packet.context.state.seed _ _).mp equal
    exact congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same

noncomputable def repair (candidate : Plan roles) (model : Assignment) : Assignment :=
  GeneralNominalCenteredModelExtension.assign model
    (fun index : Fin (mergeAssignments candidate).length => (mergeAssignments candidate)[index].1)
    (fun index : Fin (mergeAssignments candidate).length => (model (candidate.binder (mergeAssignments candidate)[index].2)).1)

theorem repair_assigned (candidate : Plan roles) (model : Assignment) (assignment : Nat × Nat)
    (member : assignment ∈ mergeAssignments candidate) :
    (repair candidate model assignment.1).1 = (model (candidate.binder assignment.2)).1 := by
  obtain ⟨index,bounded,equal⟩ := List.mem_iff_getElem.mp member
  have fixed := GeneralNominalCenteredModelExtension.assign_value model
    (fun index : Fin (mergeAssignments candidate).length => (mergeAssignments candidate)[index].1)
    (fun index : Fin (mergeAssignments candidate).length => (model (candidate.binder (mergeAssignments candidate)[index].2)).1)
    (fun first last same => congrArg (fun name => (model (candidate.binder name)).1)
      (assignments_coherent candidate _ _ (List.getElem_mem ..) (List.getElem_mem ..) same)) ⟨index,bounded⟩
  change (repair candidate model ((mergeAssignments candidate)[index]'bounded).1).1 =
    (model (candidate.binder ((mergeAssignments candidate)[index]'bounded).2)).1 at fixed
  simpa only [equal] using fixed

theorem repair_outside (candidate : Plan roles) (model : Assignment)
    (outside : ∀ assignment ∈ mergeAssignments candidate, assignment.1 ≠ name) :
    repair candidate model name = model name :=
  GeneralNominalCenteredModelExtension.assign_outside model _ _
    (fun _index => outside _ (List.getElem_mem ..))

theorem repair_below_seed (candidate : Plan roles) (model : Assignment)
    (below : name ≤ candidate.packet.context.state.seed) : repair candidate model name = model name := by
  apply repair_outside
  intro assignment member
  obtain ⟨binder,_,member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · have above := GeneralNominalIdentities.source_above_seed candidate.packet.context.state.seed
      (candidate.packet.site.occurrence.identity,candidate.packet.declaration.id,0,binder,0)
    exact Nat.ne_of_gt (Nat.lt_of_le_of_lt below above)
  · have above := GeneralNominalIdentities.source_above_seed candidate.packet.context.state.seed
      (candidate.packet.site.occurrence.identity,candidate.packet.declaration.id,1,binder,0)
    exact Nat.ne_of_gt (Nat.lt_of_le_of_lt below above)

theorem repair_current_source (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (member : name ∈ GeneralNominalState.sources candidate.packet.context.state) :
    repair candidate model name = model name := by
  apply repair_below_seed
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  rw [frame.context_eq] at member ⊢
  exact formed.below_seed name member

theorem repair_models (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (valid : Models state model) : Models state (repair candidate model) := by
  have current := GeneralNominalCenteredModelExtension.source_models_same candidate.packet.context.state
    (fun name member => (repair_current_source source candidate frame model member).symm) (by simpa only [frame.context_eq] using valid.1.1.1)
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  apply (GeneralNominalHeadInitialCommon188.initial_models_iff context point _).mpr
  simpa only [frame.context_eq,initial,GeneralNominalCenteredSteps.initial,
    GeneralNominalCenteredSteps.initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] using current

theorem occurrences_nonempty (candidate : Plan roles)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (declared : name ∈ candidate.packet.declaration.inputNames) :
    GeneralNominalAllocation.occurrences candidate.packet.bindings name ≠ [] := by
  rw [names] at declared
  obtain ⟨entry,member,equal⟩ := List.mem_map.mp declared
  have present : (candidate.packet.context.state.base.source entry.2,candidate.packet.context.state.base.source entry.2) ∈
      GeneralNominalAllocation.occurrences candidate.packet.bindings name := by
    apply List.mem_map.mpr
    refine ⟨(entry.1,candidate.packet.context.state.base.source entry.2,candidate.packet.context.state.base.source entry.2),?_,rfl⟩
    apply List.mem_filter.mpr
    constructor
    · rw [bindings_eq candidate entries query bounds]
      exact List.mem_map.mpr ⟨entry,member,rfl⟩
    · simpa using equal
  exact List.ne_nil_of_mem present

theorem repair_extrema_terms (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (name : Nat) :
    (GeneralNominalAllocation.lower (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval
      CommonNominalFullCarrier.model (repair candidate model) =
      (GeneralNominalAllocation.lower (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval CommonNominalFullCarrier.model model ∧
    (GeneralNominalAllocation.upper (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval
      CommonNominalFullCarrier.model (repair candidate model) =
      (GeneralNominalAllocation.upper (GeneralNominalAllocation.occurrences candidate.packet.bindings name)).eval CommonNominalFullCarrier.model model := by
  have endpoints := GeneralNominalAllocationSupport.occurrences_endpoints
    (GeneralNominalAllocationSupport.report_endpoints candidate.packet.context.state
      (GeneralNominalPacketSupport.report candidate.packet)) name
  constructor
  · apply GeneralNominalCenteredModelExtension.type_eval_same
    intro identity member
    exact repair_current_source source candidate frame model
      (GeneralNominalAllocationSupport.lower_sources _ endpoints member)
  · apply GeneralNominalCenteredModelExtension.type_eval_same
    intro identity member
    exact repair_current_source source candidate frame model
      (GeneralNominalAllocationSupport.upper_sources _ endpoints member)

/-- Constructed endpoint values satisfy the actual private merge equations,
without taking those equations as premises and without changing current sources. -/
theorem repair_merges (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (model : Assignment) (head : HeadEquations candidate model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (repair candidate model)
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings) := by
  intro atom member
  obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp member
  have nonempty := occurrences_nonempty candidate entries query bounds names declared
  have extrema := computed_extrema source candidate frame entries query bounds model head nonempty
  have terms := repair_extrema_terms source candidate frame model name
  have lower := repair_assigned candidate model
    (fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 0 name 0,name)
    (List.mem_flatMap.mpr ⟨name,declared,by simp⟩)
  have upper := repair_assigned candidate model
    (fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 1 name 0,name)
    (List.mem_flatMap.mpr ⟨name,declared,by simp⟩)
  cases observed : GeneralNominalAllocation.occurrences candidate.packet.bindings name with
  | nil => exact False.elim (nonempty observed)
  | cons first rest =>
    cases rest with
    | nil => simp only [observed,List.not_mem_nil] at member
    | cons second tail =>
      have both : PresenceNormalForm.All CommonNominalFullCarrier.model (repair candidate model)
          (GeneralNominalAllocation.equations
            ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1
            (GeneralNominalAllocation.lower (first :: second :: tail)) ++
           GeneralNominalAllocation.equations
            ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2
            (GeneralNominalAllocation.upper (first :: second :: tail))) := by
        apply (PresenceNormalForm.all_append ..).mpr
        constructor
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed] at *
          simp only [GeneralNominalAllocation.source,GeneralNominalAllocation.origin,fresh] at lower ⊢
          rw [lower,terms.1]
          exact ⟨extrema.1.2,extrema.1.1⟩
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed] at *
          simp only [GeneralNominalAllocation.source,GeneralNominalAllocation.origin,fresh] at upper ⊢
          rw [upper,terms.2]
          exact ⟨extrema.2.2,extrema.2.1⟩
      exact both atom (by simpa only [observed] using member)

theorem repair_other_namespace (candidate : Plan roles) (model : Assignment)
    (differentZero : purpose ≠ 0) (differentOne : purpose ≠ 1) :
    repair candidate model (fresh candidate.packet.context.state.seed invocation declaration purpose owner position) =
      model (fresh candidate.packet.context.state.seed invocation declaration purpose owner position) := by
  apply repair_outside
  intro assignment member
  obtain ⟨name,_,member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact GeneralNominalCenteredAllocation.fresh_namespaces (Ne.symm differentZero)
  · exact GeneralNominalCenteredAllocation.fresh_namespaces (Ne.symm differentOne)

theorem repair_binder (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (name : Nat) :
    repair candidate model (candidate.binder name) = model (candidate.binder name) := by
  by_cases output : name ∈ candidate.packet.declaration.outputNames
  · simpa only [Plan.binder,output,ite_true,GeneralNominalPacketSupport.capture,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.source,GeneralNominalAllocation.origin,fresh] using
      (repair_other_namespace candidate model (purpose := 2)
        (invocation := candidate.packet.site.occurrence.identity) (declaration := candidate.packet.declaration.id)
        (owner := name) (position := 0) (by omega) (by omega))
  · by_cases point : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2
    · have singleton : ∃ pair, GeneralNominalAllocation.occurrences candidate.packet.bindings name = [pair] := by
        cases observed : GeneralNominalAllocation.occurrences candidate.packet.bindings name with
        | nil =>
          simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed,
            GeneralNominalAllocation.source,GeneralNominalAllocation.origin] at point
          have same := (GeneralNominalIdentities.source_identity candidate.packet.context.state.seed _ _).mp point
          simp at same
        | cons first rest =>
          cases rest with
          | nil => exact ⟨first,rfl⟩
          | cons second tail =>
            simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed,
              GeneralNominalAllocation.source,GeneralNominalAllocation.origin] at point
            have same := (GeneralNominalIdentities.source_identity candidate.packet.context.state.seed _ _).mp point
            simp at same
      obtain ⟨pair,singleton⟩ := singleton
      have support := GeneralNominalAllocationSupport.occurrences_endpoints
        (GeneralNominalAllocationSupport.report_endpoints candidate.packet.context.state
          (GeneralNominalPacketSupport.report candidate.packet)) name pair (by
            change pair ∈ GeneralNominalAllocation.occurrences candidate.packet.bindings name
            rw [singleton]; simp)
      have binderEq : candidate.binder name = ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 := by
        simp only [Plan.binder,output,ite_false,point,ite_true]
      rw [binderEq]
      simpa only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,singleton] using
        repair_current_source source candidate frame model support.1
    · simpa only [Plan.binder,output,ite_false,point] using
        (repair_other_namespace candidate model (purpose := 8)
          (invocation := candidate.packet.site.occurrence.identity) (declaration := candidate.packet.declaration.id)
          (owner := name) (position := 0) (by omega) (by omega))

theorem repair_actual_schema (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (body : Schema)
    (actual : GeneralDictionaryActualSchema.ActualOnly body)
    (roots : GeneralNominalGeneratedSupport184.Roots body (GeneralNominalState.sources candidate.packet.context.state)) :
    candidate.SchemaHolds body (repair candidate model) ↔ candidate.SchemaHolds body model := by
  apply GeneralNominalModeFrame181.schema_iff
  intro name member
  rcases List.mem_append.mp member with test | useMember
  · obtain ⟨testEntry,present,rfl⟩ := List.mem_map.mp test
    exact repair_current_source source candidate frame model (roots.1 testEntry present)
  · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp useMember
    simp only [GeneralNominalModeFrame181.variableSources,actual entry present,ite_true,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact repair_current_source source candidate frame model (roots.2 entry present)
    · exact repair_binder source candidate frame model entry.name

private theorem initial_center_source (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (member : name ∈ List.ofFn candidate.input.center) :
    name ∈ GeneralNominalState.sources candidate.packet.context.state := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  have siteEq : candidate.input = rootSite context.state.seed root := List.mem_singleton.mp frame.center_recorded
  rw [siteEq] at member
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
  rw [frame.context_eq,← equal]
  simpa only [rootSite,point,ite_true,initial,GeneralNominalCenteredSteps.initial,
    GeneralNominalCenteredSteps.initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] using (formed.linked.1 index).1

theorem repair_head_schema (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate) (model : Assignment) :
    candidate.SchemaHolds candidate.headSchema (repair candidate model) ↔ candidate.SchemaHolds candidate.headSchema model := by
  apply repair_actual_schema source candidate frame model candidate.headSchema
  · exact fun entry present => GeneralNominalHeadSchemaNames186.head_actual candidate entry present
  · apply GeneralNominalGeneratedSupport184.roots_mono
      (GeneralNominalHeadCandidateSupport186.head_roots candidate (frame.role_eq.trans (congrArg (fun x => x.demand.role) (candidate.input_exact.trans frame.occurrence_eq)).symm))
    intro name member
    exact initial_center_source source candidate frame member

theorem repair_capture_fit (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (model : Assignment) (head : HeadEquations candidate model)
    (declared : name ∈ candidate.packet.declaration.inputNames)
    (nonempty : GeneralNominalAllocation.occurrences candidate.packet.bindings name ≠ []) :
    GeneralNominalCaptureMerges.Fits (repair candidate model)
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name)
      (repair candidate model (candidate.binder name)).1 := by
  rw [repair_binder source candidate frame model name]
  cases observed : GeneralNominalAllocation.occurrences candidate.packet.bindings name with
  | nil => exact False.elim (nonempty observed)
  | cons first rest =>
    cases rest with
    | nil =>
      have endpoints := GeneralNominalAllocationSupport.occurrences_endpoints
        (GeneralNominalAllocationSupport.report_endpoints candidate.packet.context.state
          (GeneralNominalPacketSupport.report candidate.packet)) name first (by
            change first ∈ GeneralNominalAllocation.occurrences candidate.packet.bindings name
            rw [observed]; simp)
      have old := head.2.1 name declared
      simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed,
        GeneralNominalCaptureMerges.Fits] at old ⊢
      rw [repair_current_source source candidate frame model endpoints.1,
        repair_current_source source candidate frame model endpoints.2]
      exact old
    | cons second tail =>
      have lower := repair_assigned candidate model
        (fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 0 name 0,name)
        (List.mem_flatMap.mpr ⟨name,declared,by simp⟩)
      have upper := repair_assigned candidate model
        (fresh candidate.packet.context.state.seed candidate.packet.site.occurrence.identity candidate.packet.declaration.id 1 name 0,name)
        (List.mem_flatMap.mpr ⟨name,declared,by simp⟩)
      simp only [GeneralNominalPacketSupport.capture,GeneralNominalAllocation.capture,observed,
        GeneralNominalCaptureMerges.Fits,GeneralNominalAllocation.source,GeneralNominalAllocation.origin,fresh] at lower upper ⊢
      rw [lower,upper]
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem repair_head_equations (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (model : Assignment) (valid : Models state model) (head : HeadEquations candidate model) :
    HeadEquations candidate (repair candidate model) := by
  have models := repair_models source candidate frame model valid
  refine ⟨models.1.2.1 candidate.input frame.center_recorded,?_,(repair_head_schema source candidate frame model).mpr head.2.2⟩
  intro name declared
  exact repair_capture_fit source candidate frame model head declared
    (occurrences_nonempty candidate entries query bounds names declared)

theorem initial_output_source (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (member : output ∈ root.demand.outputs) :
    output.target ∈ GeneralNominalState.sources candidate.packet.context.state := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  rw [frame.context_eq]
  exact formed.linked.2 output member

theorem repair_named_schema (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (model : Assignment) :
    candidate.SchemaHolds (GeneralNominalPacketSupport.namedSchema candidate.packet) (repair candidate model) ↔
      candidate.SchemaHolds (GeneralNominalPacketSupport.namedSchema candidate.packet) model := by
  apply repair_actual_schema source candidate frame model _
  · rw [GeneralNominalSingleVariableModels189.leaf_named_schema candidate leaf]
    exact GeneralDictionaryActualSchema.root_generated_actual _ _ _ _
  · rw [GeneralNominalSingleVariableModels189.leaf_named_schema candidate leaf]
    apply GeneralNominalGeneratedSupport184.roots_mono (GeneralNominalGeneratedSupport184.generated_roots _ _ _)
    intro name member
    obtain ⟨request,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨output,outputMember,present⟩ := List.mem_flatMap.mp present
    obtain ⟨equation,_,equal⟩ := List.mem_map.mp present
    cases equal
    apply initial_output_source source candidate frame
    simpa only [frame.occurrence_eq] using outputMember

theorem repair_outputs (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (model : Assignment)
    (outputs : OutputEquations state.core root candidate model) :
    OutputEquations state.core root candidate (repair candidate model) := by
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  have schemaEq : GeneralNominalPacketSupport.namedSchema candidate.packet = outputSchema state.core root candidate := by
    rw [GeneralNominalSingleVariableModels189.leaf_named_schema candidate leaf]
    simp only [outputSchema,requestEq,Plan.schema,rootRequests,frame.occurrence_eq]
  refine ⟨?_,?_⟩
  · have named := outputs.1
    rw [← schemaEq] at named ⊢
    exact (repair_named_schema source candidate frame leaf model).mpr named
  · intro first one last two same
    have a := initial_output_source source candidate frame (requestEq ▸ one)
    have b := initial_output_source source candidate frame (requestEq ▸ two)
    rw [repair_current_source source candidate frame model a,repair_current_source source candidate frame model b]
    exact outputs.2 first one last two same

theorem repair_head_models (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (model : Assignment) (valid : Models state model) (head : HeadEquations candidate model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds (repair candidate model) := by
  have reportEq : GeneralNominalPacketSupport.report candidate.packet =
      ({ captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
         checked := (entries.map fun entry => (entry.2,entry.2)) ++
           (entries.map fun entry => (entry.2,entry.2)) } : Report candidate.packet.context.state) := by
    simp [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,query,bounds,variable_report]
  have repairedHead := repair_head_equations source candidate frame entries query bounds names model valid head
  rw [GeneralNominalHeadBranchFrame187.head_models_exact,GeneralNominalPacketSupport.private_exact]
  refine ⟨⟨?_,cross_compatible source candidate frame entries query bounds _ repairedHead,
    repair_merges source candidate frame entries query bounds names model head,?_⟩,?_⟩
  · have current := (repair_models source candidate frame model valid).1.1.1
    simpa only [frame.context_eq] using current
  · rw [reportEq]
    intro atom member
    unfold selfChecks at member
    obtain ⟨pair,pairMem,rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp pairMem with member | member <;>
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member <;> exact subtype_refl _
  · rw [reportEq]
    refine ⟨by simp,by simp,?_,?_⟩
    · intro first one last two same ref origin actual seen
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp one
      cases origin
    · intro first one last two same a b origin other x y seenX seenY
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp one
      cases origin

end Yulang.GeneralNominalRepeatedPointRepair190
