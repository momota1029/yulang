import Yulang.GeneralDictionaryDefaultFreshProbe211Source

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultFreshProbe211Install
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryDefaultFreshProbe211Source
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations requests)

abbrev aClause := GeneralNominalCenteredHeadAllocEncoding.clause firstClause
abbrev cClause := GeneralNominalCenteredHeadAllocEncoding.clause thirdClause
abbrev bClause := GeneralNominalCenteredHeadAllocEncoding.clause lastClause
abbrev aSite := plan.childSite aClause (declaration_checked.signature.2.2.2 _ (List.mem_cons_self))
abbrev bSite := plan.childSite bClause (declaration_checked.signature.2.2.2 _ (by simp [declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]))
abbrev cSite := plan.childSite cClause (declaration_checked.signature.2.2.2 _ (by simp [declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]))
abbrev aTarget := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity 37 5 (GeneralNominalIdentities.pair 42 43) 0)
abbrev bTarget := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity 37 5 (GeneralNominalIdentities.pair 44 43) 0)

theorem targets_distinct : aTarget ≠ bTarget := by
  intro same
  have key := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp same
  have pair := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) key
  have bad := (GeneralNominalCenteredHeadAllocEncoding.equation_key.mp pair).1
  contradiction
theorem b_nonzero : bTarget ≠ 0 := by
  have above := GeneralNominalIdentities.source_above_seed snapshot.seed
    (GeneralNominalAllocation.origin root.identity 37 5 (GeneralNominalIdentities.pair 44 43) 0)
  change 0 < bTarget at above
  omega

def witness : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = bTarget then variant 0 (.base .int) else .base .int,Common.rowEmpty)
def uniform : GeneralNominalCommonBridge.Assignment := fun _ => (.base .int,Common.rowEmpty)
def counter : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then .base .int else .bottom,Common.rowEmpty)

theorem witness_zero : (witness 0).1 = .base .int := by simp [witness,Ne.symm b_nonzero]
theorem witness_a : (witness aTarget).1 = .base .int := by simp [witness,targets_distinct]
theorem witness_b : (witness bTarget).1 = variant 0 (.base .int) := by simp [witness]
theorem source_witness : GeneralNominalState.Models snapshot witness := source_model witness_zero
theorem source_uniform : GeneralNominalState.Models snapshot uniform := source_model rfl
theorem source_counter : GeneralNominalState.Models snapshot counter := source_model (by simp [counter])
theorem inhabited : Models start witness := (point_initial_models (fun _ => rfl)).mpr source_witness

theorem query : GeneralNominalInspection.queries snapshot context.interpretation declaration = [.scalar .int] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]
theorem report_exact : report context declaration [(0,0)] =
    { inspected := [((0 : Fin 1),(0 : Fin 1))], checked := [((0 : Fin 1),(0 : Fin 1)),((0 : Fin 1),(0 : Fin 1))] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append]
theorem bindings_empty : packet.bindings = [] := by
  change bindings snapshot (report context declaration [(0,0)]) = []
  rw [report_exact]; rfl

theorem head_model (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(0,0)] assignment := by
  constructor
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · change PresenceNormalForm.All _ _ ([] : List (PresenceNormalForm.Atom Nat))
      exact PresenceNormalForm.all_nil _ _
    · simp [selfChecks,PresenceNormalForm.All]; exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration :=
  ⟨source.metadata,source.linked,
    GeneralNominalSourceFormation.initial_fresh _ (GeneralNominalCenteredHeadAllocEncoding.initial_source source) _,
    [(0,0)],rfl,(by rw [report_exact]; exact ⟨rfl,rfl,rfl⟩),witness,head_model source_witness⟩
theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inl (by intro h; cases h)⟩
theorem parent_only (visible : d ∈ registry.declarations) (role : d.role = 0) : d = declaration := by
  rcases List.mem_cons.mp visible with same | member
  · exact same
  · rcases List.mem_cons.mp member with rfl | member
    · cases role
    · cases List.mem_singleton.mp member; cases role
theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root 37 children :=
  ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩
theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry context root 37 children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩
theorem frame : Frame registry start.core root 37 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,rfl,prepared⟩
theorem frame_plan (framed : Frame registry start.core root key candidate) : candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := parent_only framed.visible framed.role_eq
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have inputSame : input = rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(0,0)] = bounds := Option.some.inj framed.located
  subst bounds; rfl

theorem requests_empty : requests start.core root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present; cases within
theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root plan := by
  intro output member; simp [requests_empty] at member
theorem head_schema : plan.headSchema = { tests := [(.source 0,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]
theorem head_equations (valid : GeneralNominalState.Models snapshot assignment) : HeadEquations plan assignment := by
  refine ⟨point_root_holds _ root (fun _ => rfl) assignment,?_,?_⟩
  · intro name member; cases member
  · rw [head_schema]
    refine ⟨?_,by intro _ member; cases member⟩
    intro test member; cases List.mem_singleton.mp member
    exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact scalar valid⟩
theorem effects (assignment) : GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan assignment := by
  constructor <;> intro output member <;> simp [requests_empty] at member
def effect : Effect roles := ⟨registry,start.core,plan,frame,unique,ready⟩

theorem no_raw_recurs (slot : Fin snapshot.base.slots) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  intro cycle
  obtain ⟨next,edge,_⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  rcases edge with ⟨kind,_,_,_⟩ | argument
  · exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,_⟩ := GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument witness source_witness
    cases recorded
theorem scalar_acyclic : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic start (.source 0) := by
  rintro ⟨⟨last,⟨parent,test,index,headed,equal,_⟩,_⟩,_⟩
  have same := equal witness inhabited
  obtain ⟨actual,seen⟩ := same.2.1
  have value := same.2.2 _ actual (.source 0) seen
  have shape := (headed witness inhabited).2 actual seen
  rw [witness_zero] at value
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal name count =>
      obtain ⟨values,_,head⟩ := shape
      exact GeneralNominalPeelingOrigins.base_not_nominal .int name values (subtype_trans value.1 head.1)
  | structural kind =>
      obtain ⟨values,length,head⟩ := shape
      exact GeneralNominalCenteredHeadMatPairCycles.scalar_no_shape length
        ⟨subtype_trans value.1 head.1,subtype_trans head.2 value.2⟩
theorem inspection_exact : (GeneralNominalCenteredSteps.inspection plan).tests = [(.source 0,.scalar .int)] := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,Site.observed,rootSite,List.ofFn_succ]
theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _
theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry start root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact scalar_acyclic cycle
    · cases List.mem_singleton.mp present; exact scalar_acyclic cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · cases frame_plan framed
      rw [inspection_exact] at member; cases List.mem_singleton.mp member; exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases parent_only visible role; exact unprepared prepared
    · exact unclosed administrative_ready
theorem selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry start root (.selected 37 children) :=
  .selected safe unique (fun conflict => conflict.2
    ⟨witness,inhabited,⟨children,unique⟩,plan,frame,ready,head_equations source_witness,effects witness⟩)

theorem canonical_declaration : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
  have sorted : declaration.requirements.Pairwise (fun a b => decide (a.id ≤ b.id) = true) := by decide +kernel
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements, List.mergeSort_of_pairwise sorted]
theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨aTarget,.actual,.primitive (.scalar .int) []⟩,
      ⟨bTarget,.actual,.variant 0 (.primitive (.scalar .int) [])⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  change GeneralNominalCenteredHeadMatSchemas.generated GeneralDeclarationExamples.constructors
    GeneralNominalExamples.interpretation _ = _
  simp only [declaration,GeneralNominalCenteredHeadAllocEncoding.declaration,List.map_cons,List.map_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalCenteredHeadMatSchemas.emissionRequests,List.ofFn_zero,
    GeneralNominalCenteredHeadMatSchemas.generated,GeneralNominalCenteredHeadMatSchemas.materialize,
    GeneralNominalCenteredHeadMatSchemas.Schema.append,
    GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_translation,
    GeneralNominalCenteredHeadMatCompletionCollisionPackets.variant_translation,
    GeneralDeclarationDemands.outputTarget,normalize,normalizeArgs,GeneralNominalAllocation.allocation,
    GeneralNominalCenteredHeadAllocEncoding.clause,GeneralNominalCenteredHeadAllocEncoding.equation,
    aTarget,bTarget,GeneralNominalDemandMerging.pointSite]
theorem inputs (valid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Inputs plan assignment := by
  refine ⟨((GeneralNominalPacketSupport.private_exact packet assignment).mp (head_model valid).1).2,
    (head_model valid).2,(head_equations valid).1,?_,(head_equations valid).2.2,?_,?_⟩
  · intro name needed
    rcases needed with member | ⟨clause,member,used⟩
    · cases member
    · change clause ∈ [aClause,bClause,cClause] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> cases used
  · intro equation member nonactual
    rw [schema_exact] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact False.elim (nonactual rfl)
    · cases List.mem_singleton.mp member; exact False.elim (nonactual rfl)
  · intro clause member valid
    change clause ∈ [aClause,bClause,cClause] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨fun index => Fin.elim0 index,by intro equation present; cases present⟩
theorem packet_models : GeneralNominalCenteredHeadMatStepPackets.Holds plan witness := by
  refine ⟨source_witness,inputs source_witness,?_⟩
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs
  rw [schema_exact]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · change Equivalent (witness aTarget).1 (.base .int)
    rw [witness_a]; exact ⟨subtype_refl _,subtype_refl _⟩
  · cases List.mem_singleton.mp member
    change Equivalent (witness bTarget).1 (variant 0 (.base .int))
    rw [witness_b]; exact ⟨subtype_refl _,subtype_refl _⟩
theorem installation_models : InstallationModels start effect witness :=
  (GeneralNominalCenteredHeadMatCompletionLive.installation_models_iff checked compiled_reachable rfl rfl witness).mpr
    ⟨inhabited,packet_models,head_equations source_witness,effects witness⟩
theorem installable : GeneralNominalCenteredHeadMatStepKernel.Installable registry start effect :=
  (GeneralNominalCenteredHeadMatStepAvailability.selected_installable_iff compiled_reachable selected rfl rfl).mpr
    ⟨(by intro prior member; cases member),witness,installation_models⟩

theorem children_exact : children = [aSite.occurrence,bSite.occurrence,cSite.occurrence] := by
  change packet.children = _
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_declaration]
  rfl
theorem emitted_exact : plan.emitted = [aSite,bSite,cSite] := rfl
theorem novel : ¬ GeneralNominalCenteredHeadMatStepKernel.Committed start plan := by
  intro committed
  exact List.not_mem_nil (committed.2 aSite.occurrence (by change aSite.occurrence ∈ children; rw [children_exact]; exact List.mem_cons_self))
abbrev installed := install start effect
theorem install_step : GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root start installed :=
  ⟨root,.root,.install effect installable novel⟩
theorem installed_models : Models installed witness := (install_models rfl).mpr installation_models
theorem installed_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry root installed :=
  ⟨start,initial_source,.tail .refl install_step⟩

end Yulang.GeneralDictionaryDefaultFreshProbe211Install
