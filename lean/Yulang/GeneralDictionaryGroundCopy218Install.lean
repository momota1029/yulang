import Yulang.GeneralDictionaryGroundCopy218Source
import Yulang.GeneralDictionaryGroundCopy218Cycles

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Install
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations requests)
open GeneralDictionaryLooseVariant217 (low high first second fits_first fits_second)

abbrev declaration := GeneralNominalCenteredHeadAllocEncoding.declaration parent
abbrev declaration_checked := GeneralNominalCenteredHeadAllocEncoding.declaration_checked parent_checked
abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(6,6)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
abbrev clause := GeneralNominalCenteredHeadAllocEncoding.clause child
abbrev childSite := plan.childSite clause (declaration_checked.signature.2.2.2 _ (List.mem_singleton_self _))
noncomputable abbrev children := packet.children

theorem query : GeneralNominalInspection.queries snapshot interpretation declaration =
    [.nominal 5 [.variables [0],.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,declaration,GeneralNominalCenteredHeadAllocEncoding.declaration]

theorem report_exact : report context declaration [(6,6)] =
    { inspected := [(6,6)], checked := [(6,6),(6,6),(2,3),(2,3)],
      captures := [⟨0,(2,3),some (.nominal (.source 6) 5 0)⟩,
        ⟨1,(2,3),some (.nominal (.source 6) 5 1)⟩],
      anchors := [(.nominal (.source 6) 5 0,(2,3)),(.nominal (.source 6) 5 1,(2,3))] } := by
  have sub : inspectMany snapshot [.variables [0],.variables [1]] [(2,3),(2,3)]
      (fun index => some (.nominal (.source 6) 5 index)) 0 =
      { captures := [⟨0,(2,3),some (.nominal (.source 6) 5 0)⟩,
          ⟨1,(2,3),some (.nominal (.source 6) 5 1)⟩],
        checked := [(2,3),(2,3)],
        anchors := [(.nominal (.source 6) 5 0,(2,3)),(.nominal (.source 6) 5 1,(2,3))] } := by
    simp [inspectMany,inspect,Report.append]
  unfold report
  rw [query]
  simp [inspectMany,inspect,typeArguments,Report.append,Report.visit]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

theorem bindings_exact : packet.bindings = [(0,2,3),(1,2,3)] := by
  change bindings snapshot (report context declaration [(6,6)]) = _
  rw [report_exact]; rfl

theorem capture_exact (name : Nat) (member : name = 0 ∨ name = 1) :
    (GeneralNominalPacketSupport.capture packet).inputs name = (2,3) := by
  rcases member with rfl | rfl
  all_goals
    unfold GeneralNominalPacketSupport.capture
    rw [bindings_exact]
    rfl

theorem child_arguments : ∀ i, childSite.occurrence.demand.arguments i = (2,3) := by
  intro i
  change Fin 2 at i
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  all_goals
    change ((GeneralNominalAllocation.capture snapshot registry root.identity declaration.id packet.bindings).inputs _) = _
    rw [bindings_exact]
    rfl

theorem binder_zero : plan.binder 0 = fresh 7 0 0 8 0 0 := by
  unfold Plan.binder
  dsimp only
  rw [capture_exact 0 (Or.inl rfl)]
  rfl

theorem binder_one : plan.binder 1 = fresh 7 0 0 8 1 0 := by
  unfold Plan.binder
  dsimp only
  rw [capture_exact 1 (Or.inr rfl)]
  rfl

def model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = fresh 7 0 0 8 0 0 then first
    else if identity = fresh 7 0 0 8 1 0 then second else sourceValue identity,Common.rowEmpty)

theorem model_small (identity : Nat) (small : identity ≤ 7) : (model identity).1 = (witness identity).1 := by
  have a := GeneralNominalIdentities.source_above_seed 7 (0,0,8,0,0)
  have b := GeneralNominalIdentities.source_above_seed 7 (0,0,8,1,0)
  have one : identity ≠ fresh 7 0 0 8 0 0 := by unfold fresh; omega
  have two : identity ≠ fresh 7 0 0 8 1 0 := by unfold fresh; omega
  simp [model,one,two,witness]

theorem model_zero : (model (plan.binder 0)).1 = first := by rw [binder_zero]; simp [model]
theorem model_one : (model (plan.binder 1)).1 = second := by
  rw [binder_one]
  have different : fresh 7 0 0 8 1 0 ≠ fresh 7 0 0 8 0 0 := by
    intro h
    have bad := (GeneralNominalIdentities.source_identity 7 _ _).mp h
    have impossible := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) bad
    cases impossible
  simp [model,different]

theorem source_model : GeneralNominalState.Models snapshot model :=
  source_model_of_values model (fun identity small => model_small identity (by omega))

theorem start_model : Models start model :=
  (point_initial_models (fun _ => rfl)).mpr source_model


theorem low_high : Subtype (model 2).1 (model 3).1 := by
  rw [model_small 2 (by decide),model_small 3 (by decide)]
  exact subtype_trans fits_first.1 fits_first.2

theorem projected_fit (index : Nat) (inside : index = 0 ∨ index = 1) :
    (∃ actual, Observes model (.nominal (.source 6) 5 index) actual) ∧
    ∀ actual, Observes model (.nominal (.source 6) 5 index) actual →
      GeneralNominalCaptureMerges.Fits model (2,3) actual := by
  apply nominal_argument_bounds snapshot model source_model 6 loose rfl index (2,3)
  rcases inside with rfl | rfl <;> rfl

theorem projections : ProjectionModels snapshot (report context declaration [(6,6)]) model := by
  rw [report_exact]
  refine ⟨?_,(by intro test member; cases member),?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact projected_fit 0 (Or.inl rfl)
    · cases List.mem_singleton.mp member; exact projected_fit 1 (Or.inr rfl)
  · intro a aMem b bMem same ref refEq actual observed
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj refEq
      exact (projected_fit _ (by omega)).2 actual observed
  · intro a aMem b bMem same x y firstEq lastEq u v firstSeen lastSeen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj firstEq
      cases Option.some.inj lastEq
      exact nominal_observation_unique model (.argument (.source 6) 5 _) u v firstSeen lastSeen

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(6,6)] model := by
  refine ⟨?_,projections⟩
  unfold privateState
  rw [report_exact]
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_model,?_,?_⟩,?_⟩
  · intro a one b two same
    change a ∈ [(0,2,3),(1,2,3)] at one
    change b ∈ [(0,2,3),(1,2,3)] at two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl <;> exact low_high
  · change PresenceNormalForm.All _ _ ([] : List (PresenceNormalForm.Atom Nat))
    exact PresenceNormalForm.all_nil _ _
  · intro atom member
    change atom ∈ [.tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
      .tyLe (.var 2) (.var 3),.tyLe (.var 2) (.var 3)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact subtype_refl _
    · exact subtype_refl _
    · exact low_high
    · exact low_high

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration :=
  ⟨source.metadata,source.linked,
    GeneralNominalSourceFormation.initial_fresh _ (GeneralNominalCenteredHeadAllocEncoding.initial_source source) _,
    [(6,6)],rfl,(by rw [report_exact]; exact ⟨rfl,rfl,rfl⟩),model,head_model⟩
theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨6,rfl,Or.inr ⟨loose,rfl⟩⟩
theorem parent_only (visible : d ∈ registry.declarations) (role : d.role = 0) : d = declaration := by
  rcases List.mem_cons.mp visible with same | member
  · exact same
  · cases List.mem_singleton.mp member; cases role

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root 0 children :=
  ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(6,6)],rfl,prepared,rfl⟩
theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry context root 0 children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩
theorem frame : Frame registry start.core root 0 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,rfl,prepared⟩
theorem frame_plan (framed : Frame registry start.core root key candidate) : candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := parent_only framed.visible framed.role_eq
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have inputSame : input = rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(6,6)] = bounds := Option.some.inj framed.located
  subst bounds; rfl

theorem requests_empty : requests start.core root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present; cases within
theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root plan := by
  intro output member; simp [requests_empty] at member

theorem effects (assignment) : GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan assignment := by
  constructor <;> intro output member <;> simp [requests_empty] at member


theorem model_six : (model 6).1 = nominal 5 [.inl first,.inl second] := model_small 6 (by decide)
theorem observed_first : Observes model (.nominal (.source 6) 5 0) first :=
  .nominal (.source 6) (by rw [model_six]; exact ⟨subtype_refl _,subtype_refl _⟩) rfl
theorem observed_second : Observes model (.nominal (.source 6) 5 1) second :=
  .nominal (.source 6) (by rw [model_six]; exact ⟨subtype_refl _,subtype_refl _⟩) rfl

theorem head_schema : plan.headSchema =
    { tests := [(.source 6,.nominal 5 2)], variables :=
      [⟨0,.nominal (.source 6) 5 0,.actual⟩,⟨1,.nominal (.source 6) 5 1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]

theorem binders_fit (name : Nat) (member : name = 0 ∨ name = 1) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture packet).inputs name)
      (model (plan.binder name)).1 := by
  rw [capture_exact name member]
  rcases member with rfl | rfl
  · rw [model_zero]
    change Subtype (model 2).1 first ∧ Subtype first (model 3).1
    rw [model_small 2 (by decide),model_small 3 (by decide)]
    exact fits_first
  · rw [model_one]
    change Subtype (model 2).1 second ∧ Subtype second (model 3).1
    rw [model_small 2 (by decide),model_small 3 (by decide)]
    exact fits_second

theorem heads : plan.SchemaHolds plan.headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    exact ⟨[.inl first,.inl second],rfl,model_six ▸ ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 0) (.source (plan.binder 0))
      refine ⟨⟨first,observed_first⟩,⟨_,.source _⟩,?_⟩
      intro a b observed seen; cases seen
      rw [model_zero]
      exact nominal_observation_unique model (.argument (.source 6) 5 0) a first observed observed_first
    · cases List.mem_singleton.mp member
      change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 1) (.source (plan.binder 1))
      refine ⟨⟨second,observed_second⟩,⟨_,.source _⟩,?_⟩
      intro a b observed seen; cases seen
      rw [model_one]
      exact nominal_observation_unique model (.argument (.source 6) 5 1) a second observed observed_second

theorem head_equations : HeadEquations plan model := by
  refine ⟨point_root_holds _ root (fun _ => rfl) model,?_,heads⟩
  intro name member
  apply binders_fit name
  change name ∈ [0,1] at member
  simpa using member

abbrev sourceForm : Nat → GeneralDictionaryGroundCopy218Cycles.Form
  | 0 => .atom .bottom
  | 1 => .atom .top
  | 2 => .variant .bottom
  | 3 => .variant .top
  | 4 => .variant (.scalar .int)
  | 5 => .variant (.scalar .bool)
  | 6 | 7 => .foo
  | _ => .atom .bottom

theorem source_form (identity : Nat) : sourceValue identity = (sourceForm identity).value := by
  cases identity with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => cases n with
          | zero => rfl
          | succ n => cases n with
            | zero => rfl
            | succ n => cases n with
              | zero => rfl
              | succ n => cases n <;> rfl

theorem model_forms (identity : Nat) : ∃ form : GeneralDictionaryGroundCopy218Cycles.Form, (model identity).1 = form.value := by
  unfold model
  split
  · exact ⟨.variant (.scalar .int),rfl⟩
  · split
    · exact ⟨.variant (.scalar .bool),rfl⟩
    · exact ⟨sourceForm identity,source_form identity⟩

theorem acyclic (origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic start origin :=
  GeneralDictionaryGroundCopy218Cycles.acyclic start_model model_forms origin

theorem raw_edge_decreases {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge snapshot a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 (fun _ => 0) else if a = 3 then .structural 0 (fun _ => 1) else
      .deferred .unresolved : GeneralNormalizedObservation.Head view.shapes 8) = .structural kind children at recorded
    split at recorded
    · rename_i equal; subst a
      cases recorded
      have zero : b = 0 := child.symm
      subst b
      change 0 < 1; decide
    · split at recorded
      · rename_i equal; subst a
        cases recorded
        have one : b = 1 := child.symm
        subst b
        change 0 < 1; decide
      · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snapshot a b nominal model source_model
    have observation := embed_observation model _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      have firstValue : (model a.val).1 = (sourceForm a.val).value :=
        (model_small a.val (by omega)).trans (source_form a.val)
      have lastValue : (model b.val).1 = (sourceForm b.val).value :=
        (model_small b.val (by omega)).trans (source_form b.val)
      rw [firstValue] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryGroundCopy218Cycles.nominal_child
        (sourceForm a.val) equal found
      rw [lastValue] at same
      have rankEq := GeneralDictionaryGroundCopy218Cycles.equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path snapshot a b →
      (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases edge
  have larger := paths _ _ path
  omega


theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry start root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases parent_only visible role; exact unprepared prepared
    · exact unclosed administrative_ready

theorem selected : GeneralDictionaryDefaultBoundary208.Local sourceRegistry start root (.selected 0 children) := by
  apply GeneralDictionaryDefaultBoundary208.local_iff.mpr
  apply GeneralNominalCenteredHeadAllocV7Boundary.local_iff.mpr
  apply B4TargetV7.selected_iff.mpr
  refine ⟨.selected safe unique ?_,?_⟩
  · intro conflict
    exact conflict.2 ⟨model,start_model,⟨children,unique⟩,plan,frame,ready,head_equations,effects model⟩
  · rintro ⟨⟨a,b,member,_⟩,_⟩
    cases member

def effect : Effect roles := ⟨registry,start.core,plan,frame,unique,ready⟩

theorem canonical_declaration : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
  have sorted : declaration.requirements.Pairwise (fun a b => decide (a.id ≤ b.id) = true) := by decide +kernel
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_of_pairwise sorted]

theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨2,.lower,.variable 0⟩,⟨3,.upper,.variable 0⟩,
      ⟨2,.lower,.variable 1⟩,⟨3,.upper,.variable 1⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _
    (GeneralNominalCenteredHeadMatSchemas.requests snapshot registry
      (GeneralNominalDemandMerging.pointSite root).occurrence declaration declaration_checked packet.bindings) = _
  rw [bindings_exact]
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  rfl

theorem child_schema (valid : clause.Signature roles) :
    GeneralNominalCenteredHeadMatPlans.childSchema plan clause valid =
      ⟨[⟨plan.binder 0,.actual,.variable 0⟩,⟨plan.binder 1,.actual,.variable 1⟩],false⟩ := by
  rfl

theorem child_centers : childSite.center = fun i => if i.val = 0 then plan.binder 0 else plan.binder 1 := by
  funext i
  change Fin 2 at i
  have positions : i = 0 ∨ i = 1 := by omega
  rcases positions with rfl | rfl <;> rfl

theorem child_holds : childSite.Holds model := by
  intro i
  rw [child_arguments,child_centers]
  change Fin 2 at i
  by_cases zero : i.val = 0
  · simp only [zero,ite_true]
    exact (capture_exact 0 (Or.inl rfl)) ▸ binders_fit 0 (Or.inl rfl)
  · simp only [zero,ite_false]
    exact (capture_exact 1 (Or.inr rfl)) ▸ binders_fit 1 (Or.inr rfl)

theorem packet_models : GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
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
      first
        | rw [capture_exact 0 (Or.inl rfl)]
        | rw [capture_exact 1 (Or.inr rfl)]
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

theorem installable : GeneralDictionaryDefaultKernel208.Installable registry start effect :=
  (GeneralDictionaryDefaultAvailability208.selected_installable_iff ⟨rfl,source_checked⟩ reachable selected rfl rfl).mpr
    ⟨(by intro prior member; cases member),model,start_model,packet_models,head_equations,effects model⟩

theorem children_exact : children = [childSite.occurrence] := by
  change packet.children = _
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_declaration]
  rfl

theorem emitted_exact : plan.emitted = [childSite] := rfl

theorem novel : ¬ GeneralDictionaryDefaultKernel208.Committed start plan := by
  intro committed
  exact List.not_mem_nil (committed.1.2 childSite.occurrence (by rw [show plan.packet.children = children from rfl,children_exact]; exact List.mem_singleton_self _))

abbrev installed := install start effect

theorem install_step : GeneralDictionaryDefaultBoundary208.Step sourceRegistry root start installed :=
  ⟨root,.root,.install effect installable novel⟩

theorem installed_models : Models installed model :=
  GeneralDictionaryDefaultLive208.common_successor_model ⟨rfl,source_checked⟩ reachable rfl rfl
    start_model packet_models ⟨head_equations,effects model⟩

theorem installed_reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root installed :=
  ⟨start,initial_source,.tail .refl install_step⟩

end Yulang.GeneralDictionaryGroundCopy218Install
