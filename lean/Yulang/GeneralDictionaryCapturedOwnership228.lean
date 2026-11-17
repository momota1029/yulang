import Yulang.GeneralDictionaryResidualOwnership228

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCapturedOwnership228
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
open GeneralNominalMaterialization (Mode Request)
variable {roles : Roles.RoleDecls}

/-- Only endpoints actually encountered in this plan's recursive captures,
not all slots of the current base. -/
def capturedSources (plan : Plan roles) : List Nat :=
  (headInspection plan).captures.flatMap fun captured =>
    [plan.packet.context.state.base.source captured.bounds.1,
     plan.packet.context.state.base.source captured.bounds.2]

abbrev LocalMerge := @GeneralDictionaryResidualOwnership228.LocalMerge

def Owned (plan : Plan roles) (identity : Nat) : Prop := identity ∈ capturedSources plan ∨ LocalMerge plan identity

theorem capture_endpoints (plan : Plan roles) (name : Nat) :
    Owned plan ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ∧
    Owned plan ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
  change Owned plan (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).1 ∧
    Owned plan (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).2
  unfold GeneralNominalAllocation.capture
  dsimp only
  split
  · rename_i bounds equal
    have present : bounds ∈ GeneralNominalAllocation.occurrences plan.packet.bindings name := by simp [equal]
    obtain ⟨binding,filtered,boundsEq⟩ := List.mem_map.mp present
    have member := (List.mem_filter.mp filtered).1
    rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at member
    obtain ⟨captured,capturedMember,bindingEq⟩ := List.mem_map.mp member
    have endpoints := (congrArg Prod.snd bindingEq).trans boundsEq
    rw [← endpoints]
    exact ⟨Or.inl (List.mem_flatMap.mpr ⟨captured,capturedMember,by simp⟩),
      Or.inl (List.mem_flatMap.mpr ⟨captured,capturedMember,by simp⟩)⟩
  · exact ⟨Or.inr ⟨name,Or.inl rfl⟩,Or.inr ⟨name,Or.inr rfl⟩⟩

theorem binder_owned (plan : Plan roles)
    (two : purpose ≠ 2) (eight : purpose ≠ 8)
    (equal : plan.binder name = fresh plan.packet.context.state.seed invocation declaration purpose owner position) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  by_cases output : name ∈ plan.packet.declaration.outputNames
  · exact False.elim (GeneralDictionaryBodyProvenance227.output_separate plan two output equal.symm)
  · unfold Plan.binder at equal
    simp only [output,ite_false] at equal
    split at equal
    · exact equal ▸ (capture_endpoints plan name).1
    · exact False.elim (GeneralNominalCenteredAllocation.fresh_namespaces eight equal.symm)

theorem resolve_owned (plan : Plan roles)
    (two : purpose ≠ 2) (eight : purpose ≠ 8)
    (equal : resolve plan mode name = fresh plan.packet.context.state.seed invocation declaration purpose owner position) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  unfold resolve at equal
  split at equal
  · exact binder_owned plan two eight equal
  · cases mode with
    | actual => exact binder_owned plan two eight equal
    | lower => exact equal ▸ (capture_endpoints plan name).1
    | upper => exact equal ▸ (capture_endpoints plan name).2

theorem reads_owned (plan : Plan roles)
    (two : purpose ≠ 2) (eight : purpose ≠ 8)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultModeSupport212.reads (resolve plan) mode expression) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  obtain ⟨mode,name,equal⟩ := GeneralDictionaryDefault214ActualTotalSources.reads_source _ _ _ member
  exact resolve_owned plan two eight equal

theorem emitted_target_owned (plan : Plan roles) (clause : Clause)
    (signature : clause.Signature roles) (mergePurpose : purpose = 0 ∨ purpose = 1)
    (request : Request)
    (member : request ∈ GeneralNominalCenteredHeadMatSchemas.emissionRequests
      (GeneralDeclarationDemands.emit plan.packet.site.occurrence.identity plan.packet.declaration clause signature
        (GeneralNominalPacketSupport.capture plan.packet)
        (GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity plan.packet.declaration.id clause)))
    (equal : fresh plan.packet.context.state.seed invocation declaration purpose owner position = request.target) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  classical
  by_cases owned : Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position)
  · exact owned
  · apply False.elim
    apply GeneralDictionaryDefault214ActualTotalSources.emitted_target_separate
      (identity := fresh plan.packet.context.state.seed invocation declaration purpose owner position)
      plan.packet.declaration clause signature (GeneralNominalPacketSupport.capture plan.packet)
      (GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id clause)
      (fun name => ⟨fun equal => owned (equal.symm ▸ (capture_endpoints plan name).1),
        fun equal => owned (equal.symm ▸ (capture_endpoints plan name).2)⟩)
      (fun _ => GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 2))
      (fun _ => ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3),
        GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4)⟩)
      (fun _ => GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 5))
      request member equal

theorem request_target_owned
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : request ∈ GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings)
    (equal : fresh plan.packet.context.state.seed invocation declaration purpose owner position = request.target) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  rcases List.mem_append.mp member with initial | emitted
  · obtain ⟨output,present,target⟩ := GeneralNominalGeneratedSupport184.root_request_target _ _ request initial
    have seed : plan.packet.context.state.seed = context.state.seed :=
      (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
        (GeneralDictionaryDefaultDepth208.configuration_trace path).1
    have separate := GeneralDictionaryRequestSeparation227.raw_target_separate
      (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
      source path (by omega : purpose ≠ 2) (by omega : purpose ≠ 5)
      plan.packet.site frame.raw_recorded output present
    rw [seed] at equal
    exact False.elim (separate (equal.trans target))
  · obtain ⟨emission,present,within⟩ := List.mem_flatMap.mp emitted
    have old := (GeneralCanonicalChildOrder.canonicalEmit_perm plan.packet.site.occurrence.identity
      plan.packet.declaration plan.packet.checked _ _).mem_iff.mpr present
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp old
    exact emitted_target_owned plan clause.val _ mergePurpose request within equal

theorem emitted_sources_owned
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan)
        (GeneralNominalCenteredHeadMatPlans.emittedSchema plan)) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  obtain ⟨equation,present,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp within with target | read
  · obtain ⟨request,requested,equal⟩ := GeneralDictionaryDefault214ActualTotalSources.generated_target present
    exact request_target_owned source path plan frame mergePurpose requested (target.trans equal)
  · exact reads_owned plan (by omega) (by omega) read

theorem child_center_owned (plan : Plan roles) (clause : Clause)
    (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (equal : fresh plan.packet.context.state.seed invocation declaration purpose owner position =
      (plan.childSite clause signature).center index) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  change _ = plan.emittedCenter _ _ _ at equal
  unfold Plan.emittedCenter at equal
  split at equal
  · exact binder_owned plan (by omega) (by omega) equal.symm
  · exact False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 9) equal)

theorem child_endpoints_owned (plan : Plan roles) (clause : Clause)
    (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (mergePurpose : purpose = 0 ∨ purpose = 1) :
    (fresh plan.packet.context.state.seed invocation declaration purpose owner position =
      ((plan.childSite clause signature).occurrence.demand.arguments index).1 →
      Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position)) ∧
    (fresh plan.packet.context.state.seed invocation declaration purpose owner position =
      ((plan.childSite clause signature).occurrence.demand.arguments index).2 →
      Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position)) := by
  change (_ = (GeneralDeclarationDemands.inputInterval _ _ _).1 → _) ∧
    (_ = (GeneralDeclarationDemands.inputInterval _ _ _).2 → _)
  unfold GeneralDeclarationDemands.inputInterval
  split
  · rename_i name equal
    exact ⟨fun equal => equal.symm ▸ (capture_endpoints plan name).1,
      fun equal => equal.symm ▸ (capture_endpoints plan name).2⟩
  · exact ⟨fun equal => False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3) equal),
      fun equal => False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4) equal)⟩

theorem child_site_owned (plan : Plan roles) (clause : Clause) (signature : clause.Signature roles)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalCenteredFrame179.siteSources (plan.childSite clause signature)) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  obtain ⟨xs,present,within⟩ := List.mem_flatten.mp member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with lower | upper | center
  · exact (child_endpoints_owned plan clause signature index mergePurpose).1 lower
  · exact (child_endpoints_owned plan clause signature index mergePurpose).2 upper
  · exact child_center_owned plan clause signature index mergePurpose center

theorem child_schema_owned (plan : Plan roles) (clause : Clause) (signature : clause.Signature roles)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan)
        (GeneralNominalCenteredHeadMatPlans.childSchema plan clause signature)) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  obtain ⟨equation,present,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp within with target | read
  · obtain ⟨request,requested,equal⟩ := GeneralDictionaryDefault214ActualTotalSources.generated_target present
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp requested
    exact child_center_owned plan clause signature index mergePurpose (target.trans equal)
  · exact reads_owned plan (by omega) (by omega) read

theorem child_sources_owned (plan : Plan roles)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryDefaultPacketSupport213.childSources plan) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) := by
  obtain ⟨clause,_,within⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp within with site | schema
  · exact child_site_owned plan clause.val _ mergePurpose site
  · exact child_schema_owned plan clause.val _ mergePurpose schema

theorem emitted_residual_subset (plan : Plan roles) :
    GeneralDictionaryFirstResidual227.emittedResidual plan ⊆
      GeneralDictionaryDefaultModeSupport213.schemaSources (resolve plan)
        (GeneralNominalCenteredHeadMatPlans.emittedSchema plan) := by
  intro identity member
  obtain ⟨equation,present,within⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨equation,present,?_⟩
  rcases List.mem_cons.mp within with target | range
  · exact List.mem_cons.mpr (Or.inl target)
  · apply List.mem_cons.mpr; apply Or.inr
    split at range
    · cases range
    · exact range

theorem emitted_residual_owned
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (member : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈
      GeneralDictionaryFirstResidual227.emittedResidual plan) :
    Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position) :=
  emitted_sources_owned source path plan frame mergePurpose (emitted_residual_subset plan member)

/-- Concrete local-key ownership is syntactic, not prior-footprint protection:
refresh/reobservation can change which captured endpoints are observed. -/
theorem key_of_not_captured (plan : Plan roles)
    (owned : Owned plan (fresh plan.packet.context.state.seed invocation declaration purpose owner position))
    (absent : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉ capturedSources plan) :
    invocation = plan.packet.site.occurrence.identity ∧ declaration = plan.packet.declaration.id ∧
      (purpose = 0 ∨ purpose = 1) ∧ position = 0 := by
  obtain ⟨name,lowerOrUpper⟩ := owned.resolve_left absent
  rcases lowerOrUpper with equal | equal
  all_goals
    have identities := (GeneralNominalIdentities.source_identity plan.packet.context.state.seed _ _).mp equal
    have inv := congrArg (fun key : GeneralNominalIdentities.Origin => key.1) identities
    have decl := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.1) identities
    have pur := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) identities
    have pos := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.2) identities
    exact ⟨inv,decl,by simp_all,pos⟩

theorem captured_witness (plan : Plan roles) (member : identity ∈ capturedSources plan) :
    ∃ captured ∈ (headInspection plan).captures, ∃ origin,
      captured.origin = some origin ∧
      (identity = plan.packet.context.state.base.source captured.bounds.1 ∨
       identity = plan.packet.context.state.base.source captured.bounds.2) := by
  obtain ⟨captured,present,within⟩ := List.mem_flatMap.mp member
  obtain ⟨origin,located,_⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨captured,present,origin,located,by simpa only [List.mem_cons,List.not_mem_nil,or_false] using within⟩

/-- A captured endpoint missing from the old semantic footprint has a concrete
observed origin at the corresponding semantic extremum. This is not a replay
construction: the lower/top and upper/bottom alternatives remain explicit. -/
theorem absent_captured_extreme
    (trace : GeneralDictionarySemanticTrace227.Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (nonzero : identity ≠ 0) (absent : identity ∉ pool)
    (member : identity ∈ capturedSources plan) :
    ∃ captured ∈ (headInspection plan).captures, ∃ origin, ∃ actual,
      captured.origin = some origin ∧ GeneralNominalRecursiveInspection.Observes model origin actual ∧
      ((identity = plan.packet.context.state.base.source captured.bounds.1 ∧ CommonNominalFullCarrier.Subtype .top actual) ∨
       (identity = plan.packet.context.state.base.source captured.bounds.2 ∧ CommonNominalFullCarrier.Subtype actual .bottom)) := by
  obtain ⟨captured,present,origin,located,endpoint⟩ := captured_witness plan member
  have anchored := GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state
    _ plan.packet.bounds _ 0 captured present origin located
  obtain ⟨actual,observed⟩ := (GeneralDictionaryReachableRest227.centered_projection plan frame model valid schema).1 _ anchored |>.1
  refine ⟨captured,present,origin,actual,located,observed,?_⟩
  rcases endpoint with lower | upper
  · exact Or.inl ⟨lower,GeneralDictionaryPointCaptureSupport227.absent_lower_top
      trace plan frame model valid schema captured present located
      (lower ▸ nonzero) (lower ▸ absent) observed⟩
  · exact Or.inr ⟨upper,GeneralDictionaryPointCaptureSupport227.absent_upper_bottom
      trace plan frame model valid schema captured present located
      (upper ▸ nonzero) (upper ▸ absent) observed⟩

theorem owned_absent_nonlocal_extreme
    (trace : GeneralDictionarySemanticTrace227.Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (nonzero : identity ≠ 0) (absent : identity ∉ pool)
    (owned : Owned plan identity) (nonlocal : ¬ LocalMerge plan identity) :
    ∃ captured ∈ (headInspection plan).captures, ∃ origin, ∃ actual,
      captured.origin = some origin ∧ GeneralNominalRecursiveInspection.Observes model origin actual ∧
      ((identity = plan.packet.context.state.base.source captured.bounds.1 ∧ CommonNominalFullCarrier.Subtype .top actual) ∨
       (identity = plan.packet.context.state.base.source captured.bounds.2 ∧ CommonNominalFullCarrier.Subtype actual .bottom)) :=
  absent_captured_extreme trace plan frame model valid schema nonzero absent (owned.resolve_right nonlocal)

end Yulang.GeneralDictionaryCapturedOwnership228
