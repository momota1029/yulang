import Yulang.GeneralDictionaryGroundCopy218Stability

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Reinstall
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked clause model plan childSite)
open GeneralDictionaryGroundCopy218Reobserve
open GeneralDictionaryGroundCopy218Obstruction (stage initialAtoms stage_initial)
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations requests)
open GeneralDictionaryLooseVariant217 (first second)

abbrev currentContext : GeneralNominalCandidates.Context :=
  ⟨pointExtended installedAllocation installedReservation installedOrdinary,interpretation⟩

theorem context_eq : reobserved.core.erased.current.context = currentContext := by
  exact congrArg (fun data : GeneralNominalState.State => (⟨data,interpretation⟩ : GeneralNominalCandidates.Context))
    reobserved_snapshot

abbrev newPacket : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,currentContext,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(6,6)]⟩
abbrev newPlan : Plan roles := ⟨newPacket,plan.input,rfl⟩
abbrev newChild := newPlan.childSite clause (declaration_checked.signature.2.2.2 _ (List.mem_singleton_self _))
noncomputable abbrev newChildren := newPacket.children

theorem query : GeneralNominalInspection.queries currentContext.state interpretation declaration =
    [.nominal 5 [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem report_exact : report currentContext declaration [(6,6)] =
    { inspected := [(6,6)], checked := [(6,6),(6,6),(4,4),(5,5)],
      captures := [⟨0,(4,4),some (.nominal (.source 6) 5 0)⟩,
        ⟨1,(5,5),some (.nominal (.source 6) 5 1)⟩],
      anchors := [(.nominal (.source 6) 5 0,(4,4)),(.nominal (.source 6) 5 1,(5,5))] } := by
  have sub : inspectMany currentContext.state [.variables [0],.variables [1]] [(4,4),(5,5)]
      (fun index => some (.nominal (.source 6) 5 index)) 0 =
      { captures := [⟨0,(4,4),some (.nominal (.source 6) 5 0)⟩,
          ⟨1,(5,5),some (.nominal (.source 6) 5 1)⟩],
        checked := [(4,4),(5,5)],
        anchors := [(.nominal (.source 6) 5 0,(4,4)),(.nominal (.source 6) 5 1,(5,5))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : newPacket.bindings = [(0,4,4),(1,5,5)] := by
  change bindings currentContext.state (report currentContext declaration [(6,6)]) = _
  rw [report_exact]; rfl

theorem capture_zero : (GeneralNominalPacketSupport.capture newPacket).inputs 0 = (4,4) := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings_exact]; rfl
theorem capture_one : (GeneralNominalPacketSupport.capture newPacket).inputs 1 = (5,5) := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings_exact]; rfl

theorem binder_zero : newPlan.binder 0 = 4 := by
  unfold Plan.binder
  dsimp only
  rw [capture_zero]
  rfl

theorem binder_one : newPlan.binder 1 = 5 := by
  unfold Plan.binder
  dsimp only
  rw [capture_one]
  rfl

theorem child_arguments : ∀ i, newChild.occurrence.demand.arguments i =
    if i.val = 0 then (4,4) else (5,5) := by
  intro i
  change Fin 2 at i
  have positions : i = 0 ∨ i = 1 := by omega
  rcases positions with rfl | rfl
  all_goals
    change ((GeneralNominalAllocation.capture currentContext.state registry root.identity declaration.id newPacket.bindings).inputs _) = _
    rw [bindings_exact]
    rfl

theorem same_child_identity : newChild.occurrence.identity = childSite.occurrence.identity := rfl

theorem different_child : newChild.occurrence ≠ childSite.occurrence := by
  intro equal
  have same := congrArg (fun o : Occurrence roles => (List.ofFn o.demand.arguments)[0]?) equal
  change some (newChild.occurrence.demand.arguments ⟨0,by decide⟩) =
    some (childSite.occurrence.demand.arguments ⟨0,by decide⟩) at same
  rw [GeneralDictionaryGroundCopy218Install.child_arguments,child_arguments] at same
  cases same

theorem children_exact : newChildren = [newChild.occurrence] := by
  change newPacket.children = _
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration]
  rfl

theorem choice_compatible : GeneralNominalCycleSteps.ChoiceCompatible reobserved.core.erased.current newPacket := by
  intro prior member related
  cases List.mem_singleton.mp member
  rfl

theorem root_outside_child_closure :
    ¬ GeneralNominalSaturationState.Generated reobserved.core.erased.current childSite.occurrence root := by
  intro generated
  have same := GeneralDictionaryGroundCopy218Obstruction.generated_from_child_only
    (atoms := initialAtoms) (stage_initial.symm ▸ generated)
  have bad := congrArg (fun o : Occurrence roles => o.demand.role) same
  cases bad


theorem current_model : GeneralNominalState.Models currentContext.state model :=
  reobserved_snapshot ▸ reobserved_model.1

theorem projected_zero :
    (∃ actual, Observes model (.nominal (.source 6) 5 0) actual) ∧
    ∀ actual, Observes model (.nominal (.source 6) 5 0) actual →
      GeneralNominalCaptureMerges.Fits model (4,4) actual :=
  nominal_argument_bounds currentContext.state model current_model 6 exactCopy rfl 0 (4,4) rfl

theorem projected_one :
    (∃ actual, Observes model (.nominal (.source 6) 5 1) actual) ∧
    ∀ actual, Observes model (.nominal (.source 6) 5 1) actual →
      GeneralNominalCaptureMerges.Fits model (5,5) actual :=
  nominal_argument_bounds currentContext.state model current_model 6 exactCopy rfl 1 (5,5) rfl

theorem projections : ProjectionModels currentContext.state (report currentContext declaration [(6,6)]) model := by
  rw [report_exact]
  refine ⟨?_,(by intro test member; cases member),?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact projected_zero
    · cases List.mem_singleton.mp member; exact projected_one
  · intro a aMem b bMem same ref refEq actual observed
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj refEq
      first | exact projected_zero.2 actual observed | exact projected_one.2 actual observed
  · intro a aMem b bMem same x y firstEq lastEq u v firstSeen lastSeen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj firstEq
      cases Option.some.inj lastEq
      exact nominal_observation_unique model (.argument (.source 6) 5 _) u v firstSeen lastSeen

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry currentContext root declaration [(6,6)] model := by
  refine ⟨?_,projections⟩
  unfold privateState
  rw [report_exact]
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨current_model,?_,?_⟩,?_⟩
  · intro a one b two same
    change a ∈ [(0,4,4),(1,5,5)] at one
    change b ∈ [(0,4,4),(1,5,5)] at two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl
    all_goals first | exact subtype_refl _ | cases same
  · change PresenceNormalForm.All _ _ ([] : List (PresenceNormalForm.Atom Nat))
    exact PresenceNormalForm.all_nil _ _
  · intro atom member
    change atom ∈ [.tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
      .tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry currentContext root declaration := by
  refine ⟨source.metadata,?_,?_,[(6,6)],rfl,?_,model,head_model⟩
  · constructor
    · intro i; constructor <;>
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨6,rfl⟩)))
    · intro output member; cases member
  · intro key member _
    exact List.mem_append_right _ member
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem known : ¬ GeneralNominalState.RootPending currentContext.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨6,rfl,Or.inr ⟨exactCopy,rfl⟩⟩

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry currentContext root 0 newChildren :=
  ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(6,6)],rfl,prepared,rfl⟩

theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry currentContext root 0 newChildren := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases GeneralDictionaryGroundCopy218Install.parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩

theorem frame : Frame registry reobserved.core root 0 newPlan :=
  ⟨rfl,context_eq.symm,rfl,rfl,List.mem_cons_self,List.mem_cons_self,List.mem_cons_self,rfl,rfl,prepared⟩

theorem requests_empty : requests reobserved.core root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ [GeneralNominalDemandMerging.pointSite root,childSite.observed] at present
  rcases List.mem_cons.mp present with rfl | present
  · cases within
  · cases List.mem_singleton.mp present; cases within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready reobserved.core root newPlan := by
  intro output member; simp [requests_empty] at member

theorem effects (assignment) : GeneralNominalCenteredHeadMatEffects.ClassEffects reobserved.core root newPlan assignment := by
  constructor <;> intro output member <;> simp [requests_empty] at member

theorem head_schema : newPlan.headSchema =
    { tests := [(.source 6,.nominal 5 2)], variables :=
      [⟨0,.nominal (.source 6) 5 0,.actual⟩,⟨1,.nominal (.source 6) 5 1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,rootSite,List.ofFn_succ]

theorem heads : newPlan.SchemaHolds newPlan.headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    exact ⟨[.inl first,.inl second],rfl,GeneralDictionaryGroundCopy218Install.model_six ▸ ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 0) (.source (newPlan.binder 0))
      refine ⟨⟨first,GeneralDictionaryGroundCopy218Install.observed_first⟩,⟨_,.source _⟩,?_⟩
      intro a b observed seen; cases seen
      rw [binder_zero,GeneralDictionaryGroundCopy218Install.model_small 4 (by decide)]
      exact nominal_observation_unique model (.argument (.source 6) 5 0) a first observed
        GeneralDictionaryGroundCopy218Install.observed_first
    · cases List.mem_singleton.mp member
      change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 1) (.source (newPlan.binder 1))
      refine ⟨⟨second,GeneralDictionaryGroundCopy218Install.observed_second⟩,⟨_,.source _⟩,?_⟩
      intro a b observed seen; cases seen
      rw [binder_one,GeneralDictionaryGroundCopy218Install.model_small 5 (by decide)]
      exact nominal_observation_unique model (.argument (.source 6) 5 1) a second observed
        GeneralDictionaryGroundCopy218Install.observed_second

theorem binders_fit (name : Nat) (member : name = 0 ∨ name = 1) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture newPacket).inputs name)
      (model (newPlan.binder name)).1 := by
  rcases member with rfl | rfl
  · rw [capture_zero,binder_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [capture_one,binder_one]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem head_equations : HeadEquations newPlan model := by
  refine ⟨point_root_holds _ root (fun _ => rfl) model,?_,heads⟩
  intro name member
  apply binders_fit name
  change name ∈ [0,1] at member
  simpa using member

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady reobserved root := by
  refine ⟨⟨plan.input,List.mem_cons_self,rfl⟩,?_⟩
  intro first one same last two inputs
  change first ∈ [plan.input,childSite] at one
  change last ∈ [plan.input,childSite] at two
  rcases List.mem_cons.mp one with rfl | one
  · rcases List.mem_cons.mp two with rfl | two
    · exact .refl _
    · cases List.mem_singleton.mp two
      have impossible := inputs.1; cases impossible
  · cases List.mem_singleton.mp one
    have impossible := congrArg (fun o : Occurrence roles => o.demand.role) same
    cases impossible

theorem acyclic (origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic reobserved origin :=
  GeneralDictionaryGroundCopy218Cycles.acyclic reobserved_model GeneralDictionaryGroundCopy218Install.model_forms origin

theorem raw_acyclic (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt currentContext.state slot := by
  have result := GeneralDictionaryGroundCopy218Stability.no_raw_recurs
    GeneralDictionaryGroundCopy218Obstruction.atoms_initial slot
  exact result

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry reobserved root := by
  refine ⟨?_,?_,?_,?_⟩
  · change ¬ GeneralNominalState.RootPending _ root.demand
    rw [context_eq]
    exact known
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact raw_acyclic slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact raw_acyclic visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases GeneralDictionaryGroundCopy218Install.parent_only visible role
      rw [context_eq] at unprepared
      exact unprepared prepared
    · exact unclosed administrative_ready

theorem current_unique : GeneralNominalCenteredHeadCandidates.Unique registry
    reobserved.core.erased.current.context root 0 newChildren := by
  rw [context_eq]
  exact unique

theorem selected : GeneralDictionaryDefaultBoundary208.Local sourceRegistry reobserved root (.selected 0 newChildren) := by
  apply GeneralDictionaryDefaultBoundary208.local_iff.mpr
  apply GeneralNominalCenteredHeadAllocV7Boundary.local_iff.mpr
  apply B4TargetV7.selected_iff.mpr
  refine ⟨.selected safe current_unique ?_,?_⟩
  · intro conflict
    exact conflict.2 ⟨model,reobserved_model,⟨newChildren,current_unique⟩,newPlan,frame,ready,head_equations,effects model⟩
  · rintro ⟨⟨a,b,member,_⟩,_⟩
    cases member

def newEffect : Effect roles := ⟨registry,reobserved.core,newPlan,frame,current_unique,ready⟩

theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema newPlan =
    ⟨[⟨4,.lower,.variable 0⟩,⟨4,.upper,.variable 0⟩,
      ⟨5,.lower,.variable 1⟩,⟨5,.upper,.variable 1⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _
    (GeneralNominalCenteredHeadMatSchemas.requests currentContext.state registry
      (GeneralNominalDemandMerging.pointSite root).occurrence declaration declaration_checked newPacket.bindings) = _
  rw [bindings_exact]
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralDictionaryGroundCopy218Install.canonical_declaration]
  rfl

theorem child_schema (valid : clause.Signature roles) :
    GeneralNominalCenteredHeadMatPlans.childSchema newPlan clause valid =
      ⟨[⟨newPlan.binder 0,.actual,.variable 0⟩,⟨newPlan.binder 1,.actual,.variable 1⟩],false⟩ := rfl

theorem child_holds : newChild.Holds model := by
  intro i
  change Fin 2 at i
  have positions : i = 0 ∨ i = 1 := by omega
  rcases positions with rfl | rfl
  · change GeneralNominalCaptureMerges.Fits model _ (model (newPlan.binder 0)).1
    rw [child_arguments,binder_zero]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · change GeneralNominalCaptureMerges.Fits model _ (model (newPlan.binder 1)).1
    rw [child_arguments,binder_one]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_models : GeneralNominalCenteredHeadMatStepPackets.Holds newPlan model := by
  apply GeneralNominalCenteredHeadMatStepPackets.models_iff.mp
  refine ⟨head_model,head_equations.1,?_,heads,?_,?_⟩
  · intro name needed
    apply binders_fit name
    rcases needed with member | ⟨c,member,within⟩
    · change name ∈ [0,1] at member; simpa using member
    · cases List.mem_singleton.mp member
      change name ∈ [0,1] at within; simpa using within
  · rw [schema_exact]
    intro equation member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      change Equivalent _ _
      simp only [GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatEffects.variables]
      change Equivalent _ _
      first | rw [capture_zero] | rw [capture_one]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro c member valid
    cases List.mem_singleton.mp member
    refine ⟨child_holds,?_⟩
    rw [child_schema]
    intro equation present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp present
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem installable : GeneralDictionaryDefaultKernel208.Installable registry reobserved newEffect :=
  (GeneralDictionaryDefaultAvailability208.selected_installable_iff ⟨rfl,source_checked⟩ reobserved_reachable selected rfl rfl).mpr
    ⟨choice_compatible,model,reobserved_model,packet_models,head_equations,effects model⟩

theorem novel : ¬ GeneralDictionaryDefaultKernel208.Committed reobserved newPlan := by
  intro committed
  have member := committed.1.2 newChild.occurrence
    (by change newChild.occurrence ∈ newChildren; rw [children_exact]; exact List.mem_singleton_self _)
  have edges := GeneralDictionaryGroundCopy218Obstruction.edges_exact initialAtoms
  rw [stage_initial] at edges
  rw [edges] at member
  exact different_child (congrArg Prod.snd (List.mem_singleton.mp member))

abbrev reinstalled := install reobserved newEffect

theorem reinstall_step : GeneralDictionaryDefaultBoundary208.Step sourceRegistry root reobserved reinstalled :=
  ⟨root,.root,.install newEffect installable novel⟩

theorem reinstalled_models : Models reinstalled model :=
  GeneralDictionaryDefaultLive208.common_successor_model ⟨rfl,source_checked⟩ reobserved_reachable rfl rfl
    reobserved_model packet_models ⟨head_equations,effects model⟩

theorem reinstalled_reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root reinstalled := by
  obtain ⟨start,initial,path⟩ := reobserved_reachable
  exact ⟨start,initial,.tail path reinstall_step⟩


theorem reinstalled_sites : reinstalled.core.sites = [plan.input,childSite,newChild] := rfl
theorem reinstalled_raw_sites : reinstalled.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed,newChild.observed] := rfl

theorem reinstalled_edges : reinstalled.core.erased.current.edges =
    [(root,childSite.occurrence),(root,newChild.occurrence)] := by
  change reobserved.core.erased.current.edges ++ newPacket.children.map (fun c => (root,c)) = _
  have edges := GeneralDictionaryGroundCopy218Obstruction.edges_exact initialAtoms
  rw [stage_initial] at edges
  rw [edges,show newPacket.children = newChildren from rfl,children_exact]
  rfl

theorem reinstalled_generated_only {focus}
    (generated : GeneralNominalSaturationState.Generated reinstalled.core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence := by
  induction generated with
  | root => exact Or.inl rfl
  | child prior member ih =>
    rw [reinstalled_edges] at member
    rcases List.mem_cons.mp member with same | member
    · exact Or.inr (Or.inl (congrArg Prod.snd same))
    · exact Or.inr (Or.inr (congrArg Prod.snd (List.mem_singleton.mp member)))
  | alias prior one two related ih =>
    rw [reinstalled_raw_sites] at two
    rcases List.mem_cons.mp two with rfl | two
    · exact Or.inl rfl
    · rcases List.mem_cons.mp two with rfl | two
      · exact Or.inr (Or.inl rfl)
      · cases List.mem_singleton.mp two; exact Or.inr (Or.inr rfl)

theorem old_generated : GeneralNominalSaturationState.Generated reinstalled.core.erased.current root childSite.occurrence :=
  .child .root (reinstalled_edges ▸ List.mem_cons_self)
theorem new_generated : GeneralNominalSaturationState.Generated reinstalled.core.erased.current root newChild.occurrence :=
  .child .root (reinstalled_edges ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem new_generated_from_old : GeneralNominalSaturationState.Generated reinstalled.core.erased.current childSite.occurrence newChild.occurrence := by
  apply GeneralNominalSaturationState.Generated.alias (first := childSite.observed) (last := newChild.observed) .root
  · rw [reinstalled_raw_sites]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [reinstalled_raw_sites]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · rw [show newChild.observed.occurrence.identity = newChild.occurrence.identity from rfl,same_child_identity]
    exact .refl _

theorem new_child_pending : GeneralNominalState.RootPending reinstalled.core.erased.current.context.state newChild.occurrence.demand := by
  refine ⟨⟨0,by decide⟩,?_⟩
  rw [child_arguments]
  change ¬ GeneralNominalState.Known newPacket.privateContext.state 4
  rintro ⟨slot,sourceEq,head | ⟨descriptor,recorded⟩⟩
  · have equal : slot = (4 : Fin 8) := Fin.ext sourceEq
    subst slot
    exact head rfl
  · have equal : slot = (4 : Fin 8) := Fin.ext sourceEq
    subst slot
    cases recorded


theorem not_root_stable : ¬ GeneralDictionaryDefaultBoundary208.Stable sourceRegistry reobserved root := by
  intro stable
  exact stable root .root reinstalled (.install newEffect installable novel)

theorem old_impossible_after_reinstall (given : GeneralNominalCommonBridge.Assignment)
    (held : Models reinstalled given) :
    GeneralDictionarySharingObstruction217.Impossible registry reinstalled.core given childSite.occurrence 1 := by
  apply GeneralDictionaryTopLevelSharing217.impossible registry reinstalled given childSite.occurrence 1 0
  · intro declaration visible key
    cases GeneralDictionaryGroundCopy218Obstruction.key_leaf visible key
    exact GeneralDictionaryGroundCopy218Obstruction.leaf_queries _
  · intro site member equal
    rw [reinstalled_sites] at member
    rcases List.mem_cons.mp member with rfl | member
    · have impossible := congrArg (fun o : Occurrence roles => o.demand.role) equal
      cases impossible
    · rcases List.mem_cons.mp member with rfl | member
      · exact GeneralDictionaryGroundCopy218Obstruction.centers_different given
          (held.2.2.2.2.1 plan (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      · cases List.mem_singleton.mp member
        exact False.elim (different_child equal)

theorem old_no_evidence_after_reinstall (given : GeneralNominalCommonBridge.Assignment)
    (held : Models reinstalled given) (dictionaries) :
    ¬ GeneralDictionaryTotalEvidence206.Evidence registry reinstalled.core given childSite.occurrence (.node 1 dictionaries) :=
  GeneralDictionarySharingObstruction217.no_evidence (old_impossible_after_reinstall given held) dictionaries

end Yulang.GeneralDictionaryGroundCopy218Reinstall
