import Yulang.GeneralLiveCompoundRoot316

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 22000
namespace Yulang.GeneralLiveCompoundInstall316
open GeneralDictionaryJournalRefinement228Source
open GeneralLiveCompoundRegistry316 GeneralLiveCompoundRoot316
open GeneralDictionaryOptionalInstall229 (model)
open GeneralDictionaryCompoundVersionedModel238 (extended initial_model)
open GeneralNominalVersionedJournal232
open GeneralNominalCenters

noncomputable abbrev before := initialState
noncomputable def installed := GeneralNominalVersionedInstall232.install before effect

theorem old_model_initial : Models before model :=
  (lift_models GeneralDictionaryCompoundSource238.start model).mpr GeneralDictionaryOptionalInstall229.inhabited

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic before origin :=
  GeneralNominalVersionedAcyclic232.acyclic old_model_initial
    (fun identity => ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩) origin

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady before root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry before root := by
  refine ⟨GeneralDictionaryCompoundPacket238.known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · rcases List.mem_cons.mp visible with same | member
      · cases same; exact unprepared prepared
      · cases List.mem_singleton.mp member
        rename_i role
        first | contradiction | (change (1 : Nat) = 0 at role; cases role)
    · exact unready administrative_ready

theorem positions : GeneralNominalVersionedCycles232.Safe before plan :=
  ⟨GeneralDictionaryOptionalEnable229.enabled.positions.1,fun entry _ => acyclic entry.1⟩

theorem frame_unique {candidate : Plan roles} {k : Nat}
    (framed : GeneralNominalVersionedEvidence231.Frame registry before.core root k candidate) :
    candidate = plan := by
  have decl : candidate.packet.declaration = declaration := by
    rcases List.mem_cons.mp framed.visible with yes | last
    · exact yes
    · have bad := List.mem_singleton.mp last
      exact False.elim (by
        have role := framed.role_eq
        rw [bad] at role
        cases role)
  rcases candidate with ⟨⟨r,ctx,site,d,h,b⟩,input,indexed⟩
  have a : r = registry := framed.registry_eq
  have c : ctx = context := framed.context_eq
  have ds : d = declaration := decl
  have s : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have i : input = rootSite context.state.seed root := List.mem_singleton.mp framed.center_recorded
  subst r; subst ctx; subst d; subst site; subst input
  have loc : GeneralNominalRecursiveCandidates.arguments context
      (GeneralNominalVersionedCandidates231.inputs root) = some b := framed.located
  have bs := Option.some.inj (loc.symm.trans frame.located)
  change b = [(0,0)] at bs
  subst b
  rfl

theorem schema_eq : GeneralNominalVersionedPlans231.emittedSchema plan =
    GeneralNominalVersionedPlans231.emittedSchema GeneralDictionaryCompoundPacket238.plan := by
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem variables_eq (m) : GeneralNominalVersionedPlans231.variables plan m =
    GeneralNominalVersionedPlans231.variables GeneralDictionaryCompoundPacket238.plan m := by
  funext mode name
  simp only [GeneralNominalVersionedPlans231.variables,
    show plan.packet.declaration.outputNames = GeneralDictionaryCompoundPacket238.plan.packet.declaration.outputNames from rfl]
  rfl

theorem needed (name) : GeneralNominalSharedCaptures.Needed plan.packet name ↔
    GeneralNominalSharedCaptures.Needed GeneralDictionaryCompoundPacket238.plan.packet name := by
  simp only [GeneralNominalSharedCaptures.Needed, List.mem_singleton]
  constructor
  · rintro ⟨_,rfl,seen⟩; exact ⟨_,rfl,seen⟩
  · rintro ⟨_,rfl,seen⟩; exact ⟨_,rfl,seen⟩

theorem inputs_iff (m) : GeneralNominalVersionedPlans231.Inputs plan m ↔
    GeneralNominalVersionedPlans231.Inputs GeneralDictionaryCompoundPacket238.plan m := by
  constructor
  · intro old
    refine ⟨old.1,old.2.1,old.2.2.1,?_,old.2.2.2.2.1,?_,?_⟩
    · intro name h
      rcases h with h | h
      · exact old.2.2.2.1 name (.inl h)
      · exact old.2.2.2.1 name (.inr ((needed _).mpr h))
    · rw [← schema_eq,← variables_eq]; exact old.2.2.2.2.2.1
    · intro clause member signature
      cases List.mem_singleton.mp member
      exact old.2.2.2.2.2.2 otherChild (List.mem_singleton_self _) ⟨rfl,by intro _ h; cases h⟩
  · intro old
    refine ⟨old.1,old.2.1,old.2.2.1,?_,old.2.2.2.2.1,?_,?_⟩
    · intro name h
      rcases h with h | h
      · exact old.2.2.2.1 name (.inl h)
      · exact old.2.2.2.1 name (.inr ((needed _).mp h))
    · simpa only [schema_eq,variables_eq] using old.2.2.2.2.2.1
    · intro clause member signature
      cases List.mem_singleton.mp member
      exact old.2.2.2.2.2.2 GeneralDictionaryCompoundSource238.child (List.mem_singleton_self _)
        GeneralDictionaryCompoundSites238.signature

theorem packet_iff (m) : GeneralNominalVersionedPlans231.Holds plan m ↔
    GeneralNominalVersionedPlans231.Holds GeneralDictionaryCompoundPacket238.plan m := by
  unfold GeneralNominalVersionedPlans231.Holds GeneralNominalVersionedPlans231.Outputs
  rw [inputs_iff,schema_eq,variables_eq]

theorem packet_holds : GeneralNominalVersionedPlans231.Holds plan extended :=
  (packet_iff extended).mpr GeneralDictionaryCompoundVersionedPacket238.packet_holds

theorem alternatives : GeneralNominalVersionedMixedKernel234.AlternativesSafe registry before plan.input := by
  intro candidate same framed
  have equal := frame_unique framed
  subst candidate
  exact positions

theorem initial_reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root before := ⟨before,initial,.refl⟩

theorem installation_models : GeneralNominalVersionedInstall232.InstallationModels before effect extended :=
  (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ initial_reachable rfl rfl).mpr
    ⟨initial_model,packet_holds,GeneralDictionaryCompoundFrame238.class_effects⟩

theorem installed_model : Models installed extended :=
  (GeneralNominalVersionedInstall232.install_models rfl).mpr installation_models

theorem installable : GeneralNominalVersionedMixedKernel234.Installable registry before effect := by
  refine ⟨rfl,rfl,safe,(GeneralNominalVersionedMixedObservations233.legacy_cache (GeneralDictionaryDefaultCache208.initial_valid context root)),?_,?_,positions,alternatives,
    extended,installation_models⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [schema_eq,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema]
  · intro prior member; cases member


theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed before plan :=
  fun committed => by
    have fits := (committed.1 model old_model_initial).1
    have merges := fits.2.1.1.2.1
    change PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges snapshot GeneralDictionaryCompoundSource238.registry
        root.identity GeneralDictionaryCompoundSource238.declaration GeneralDictionaryCompoundPacket238.packet.bindings) at merges
    rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merges
    change PresenceNormalForm.All CommonNominalFullCarrier.model model
      ((GeneralNominalAllocation.equations (GeneralDictionaryCompoundVersionedModel238.names 0)
        (.union (.var 4) (.var 4)) ++ _) ++ _) at merges
    have lower := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.1
    have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp lower
    change CommonNominalFullCarrier.Equivalent
      (model (GeneralDictionaryCompoundVersionedModel238.names 0)).1
      (.union GeneralDictionaryOptionalOutput229.value GeneralDictionaryOptionalOutput229.value) at equal
    rw [GeneralDictionaryCompoundStep238.unassigned_lower] at equal
    open CommonNominalFullCarrier in
    exact GeneralDictionaryOptionalOutput229.not_width
      ⟨GeneralDictionaryOptionalOutput229.below_width,
        subtype_trans equal.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩)⟩

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root before installed :=
  ⟨root,.root,.install effect installable not_committed⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root installed :=
  ⟨before,initial,.tail .refl step⟩

end Yulang.GeneralLiveCompoundInstall316
