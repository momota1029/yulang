import Yulang.GeneralNominalCenteredMergeBridge
import Yulang.GeneralDictionaryEarlyMergeExample
import Yulang.GeneralNominalGroundExamples
import Yulang.GeneralNominalPeelingExamples

/-! A ground point root emits two equal point inputs. Centered merging uses
source names, whereas the frozen emitter retains nominal observation paths. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalCenteredPointMergeExample
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (context state displayRoot listDescriptor interpretation model state_models)
open GeneralDictionaryEarlyMergeExample (registry declaration checked packet child source enabled novel query branch)
open CommonNominalFullCarrier

abbrev origin : Origin := .nominal (.source 0) 0 0
abbrev start := GeneralNominalCenteredSteps.initial (context true) displayRoot
abbrev plan : Plan roles := ⟨packet,rootSite (state true).seed displayRoot,rfl⟩
noncomputable abbrev before := GeneralNominalCenteredSteps.install start plan []

theorem raw_report : GeneralNominalPacketSupport.report packet =
    GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query

theorem inherited : (GeneralNominalSharedCaptures.inheritedReport packet).captures = [⟨0,(1,1),some origin⟩] := by
  unfold GeneralNominalSharedCaptures.inheritedReport
  rw [query]
  simp [inspectMany,inspect,GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,
    typeArguments,Report.visit,Report.append,packet,GeneralNominalDemandMerging.pointSite,
    displayRoot,GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ,origin]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [typeArguments,Report.visit,Report.append]

theorem bindings : packet.bindings = [(0,(1,1))] := by
  change GeneralNominalRecursiveInspection.bindings _ (GeneralNominalPacketSupport.report packet) = _
  rw [raw_report]
  rfl

theorem binder_zero : plan.binder 0 = 1 := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  change (if 0 ∈ declaration.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ declaration.outputNames from by decide +kernel,ite_false]
  rw [bindings]
  rfl

theorem named_empty : GeneralNominalPacketSupport.namedSchema packet = {} := GeneralDictionaryEarlyMergeExample.schema

theorem input_empty : GeneralNominalPacketSupport.inputSchema packet = {} := by
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      declaration,List.mergeSort_pair]
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,GeneralDeclarationPatterns.normalize,
    GeneralNominalMaterialization.generated]

theorem head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,displayRoot,
    GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ,origin]

def centerSite (clause : Nat) : Site roles := ⟨child clause,fun _ => 1⟩

theorem first_child : plan.childSite GeneralDeclarationExamples.displayChild
    (checked.signature.2.2.2 _ (by simp [declaration])) = centerSite 10 := by
  unfold Plan.childSite centerSite
  congr 1
  · unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame GeneralNominalAllocation.frame
    change GeneralDictionaryEmissionPlans.occurrence _ _ = _
    rw [show plan.packet = packet from rfl,bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,child,packet,displayRoot,GeneralNominalDemandMerging.pointSite,
      GeneralDeclarationExamples.displayChild,GeneralDictionaryEarlyMergeExample.secondClause]

  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,GeneralDeclarationExamples.displayChild,List.getElem_cons_zero,
      Plan.emittedCenter,GeneralDeclarationPatterns.normalize] using binder_zero

theorem second_child : plan.childSite GeneralDictionaryEarlyMergeExample.secondClause
    (checked.signature.2.2.2 _ (by simp [declaration])) = centerSite 11 := by
  unfold Plan.childSite centerSite
  congr 1
  · unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame GeneralNominalAllocation.frame
    change GeneralDictionaryEmissionPlans.occurrence _ _ = _
    rw [show plan.packet = packet from rfl,bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,child,packet,displayRoot,GeneralNominalDemandMerging.pointSite,
      GeneralDeclarationExamples.displayChild,GeneralDictionaryEarlyMergeExample.secondClause]

  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,GeneralDictionaryEarlyMergeExample.secondClause,List.getElem_cons_zero,
      Plan.emittedCenter,GeneralDeclarationPatterns.normalize] using binder_zero

theorem emitted : plan.emitted = [centerSite 10,centerSite 11] := by
  change [plan.childSite GeneralDeclarationExamples.displayChild _,plan.childSite GeneralDictionaryEarlyMergeExample.secondClause _] = _
  rw [first_child,second_child]

private theorem fit_length {base : GeneralSourceState.State} {m : GeneralNominalCommonBridge.Assignment}
    {parameters : List (GeneralNominalState.Parameter base.slots)} {values : List CommonNominalFullCarrier.Argument}
    (fit : GeneralNominalState.FitsAll base m parameters values) : parameters.length = values.length := by
  induction fit with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

theorem equations (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) : plan.Equations m := by
  have seen := nominal_argument_bounds (state true) m valid 0 listDescriptor rfl 0 (1,1) rfl
  have actual : GeneralNominalOriginTerms.Same m origin (.source 1) := by
    refine ⟨seen.1,⟨_,.source 1⟩,?_⟩
    intro a b ha hb
    cases hb
    exact ⟨(seen.2 a ha).2,(seen.2 a ha).1⟩
  refine ⟨point_root_holds _ displayRoot (fun _ => rfl) m,?_,?_,?_,?_,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with head | ⟨clause,member,used⟩
      · simpa [packet,declaration,GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize] using head
      · simp only [packet,declaration,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;>
          simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
            GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
            GeneralDictionaryEarlyMergeExample.secondClause,GeneralDeclarationExamples.displayChild] using used
    subst name
    rw [binder_zero]
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalPacketSupport.capture packet).inputs 0) _
    unfold GeneralNominalPacketSupport.capture
    rw [bindings]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      have nominal := GeneralNominalState.nominal_models (state true) m valid 0 listDescriptor rfl
      obtain ⟨arguments,fit,equal⟩ := nominal
      exact ⟨⟨_,.source 0⟩,by intro value observed; cases observed; exact ⟨arguments,by exact (fit_length fit).symm,equal⟩⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simp only [Plan.SchemaHolds,ite_true]
      rw [binder_zero]
      exact actual
  · rw [show plan.packet = packet from rfl,input_empty]
    exact ⟨(by intro _ impossible; cases impossible),(by intro _ impossible; cases impossible)⟩
  · rw [show plan.packet = packet from rfl,named_empty]
    exact ⟨(by intro _ impossible; cases impossible),(by intro _ impossible; cases impossible)⟩
  · intro clause member signature
    change clause ∈ declaration.requirements at member
    simp only [declaration,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      constructor
      · first | rw [first_child] | rw [second_child]
        intro index
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change plan.SchemaHolds (GeneralNominalMaterialization.generated _ _
          [⟨.var 0,plan.binder 0,.actual⟩]) m
        simp only [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
          GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
          GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
          List.append_nil,Plan.SchemaHolds]
        refine ⟨(by intro _ impossible; cases impossible),?_⟩
        intro entry member
        cases List.mem_singleton.mp member
        exact GeneralNominalOriginTerms.source_self m _

theorem initial_acyclic (observed : Origin) : ¬ Cyclic start observed :=
  GeneralNominalCenteredSteps.initial_acyclic _ _ (GeneralNominalActualInspectionExamples.acyclic false) observed

theorem inspection_shape (other : Plan roles)
    (sameInput : other.input = plan.input)
    (sameContext : other.packet.context = context true)
    (sameDecl : other.packet.declaration = declaration)
    (located : GeneralNominalRecursiveCandidates.arguments other.packet.context other.input.occurrence = some other.packet.bounds) :
    (inspection other).inspected.length = (inspection other).tests.length := by
  cases other with
  | mk p input exactInput =>
    cases p with
    | mk reg ctx site decl check bounds =>
      dsimp only at sameInput sameContext sameDecl located
      subst input ctx decl
      have equal : bounds = [(0,0)] := Option.some.inj located.symm
      subst bounds
      unfold inspection
      rw [query]
      simp [inspectMany,inspect,Report.visit,Report.append,Site.observed,plan,rootSite,
        displayRoot,GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,
        List.ofFn_succ,GeneralNominalExamples.state,GeneralNominalExamples.listDescriptor,typeArguments]
      repeat first
        | rw [inspectMany.eq_def]
        | rw [inspect.eq_def]
        | simp [typeArguments,Report.visit,Report.append]

theorem guard : PacketGuard start plan [] := by
  refine ⟨List.mem_singleton_self _,
    GeneralNominalValueSupport.source_packet _ _ GeneralDictionaryEarlyMergeExample.packet_guard,
    GeneralNominalCenteredSupport.legacy_decision (GeneralNominalSharedPositive.initial_decision _ _ _ _ []
      (GeneralDictionaryEarlyMergeExample.all_source_decisions displayRoot (fun _ => rfl))),
    ⟨inspection_shape plan rfl rfl rfl rfl,fun entry _ => initial_acyclic entry.1⟩,?_,?_,?_⟩
  · intro other sameInput sameRegistry sameContext visible role ready located
    have sameDecl : other.packet.declaration = declaration := List.mem_singleton.mp visible
    refine ⟨inspection_shape other sameInput sameContext sameDecl ?_,fun entry _ => initial_acyclic entry.1⟩
    simpa only [sameInput] using located
  · constructor
    · rintro ⟨site,_,_,index,cycle⟩
      exact initial_acyclic _ cycle
    · rintro ⟨other,_,_,_,_,_,_,_,_,entry,_,cycle⟩
      exact initial_acyclic _ cycle
  · exact ⟨model,(point_initial_models _ _ (fun _ => rfl) model).mpr (state_models true),
      branch model (state_models true),equations model (state_models true)⟩

theorem first_step : Step registry displayRoot start before :=
  ⟨displayRoot,.root,.install plan [] enabled novel guard⟩

theorem initial_source : InitialSource registry displayRoot start := GeneralNominalCenteredSteps.initial_source source

theorem reachable_before : B4TargetV5.Reachable (GeneralNominalCenteredBoundary.boundary roles) registry displayRoot before :=
  ⟨start,initial_source,.tail .refl first_step⟩

theorem before_models (m : GeneralNominalCommonBridge.Assignment) :
    Models before m ↔ GeneralNominalSaturationState.Models before.erased.current m := by
  rw [GeneralNominalCenteredSteps.install_models (plan := plan) (state := start) (support := []) rfl]
  change Models start m ∧ plan.Holds m ↔ GeneralNominalSaturationState.Models (GeneralNominalSharedSteps.install start.erased packet []).current m
  rw [GeneralNominalSharedSteps.install_models (packet := packet) (state := start.erased) (support := []) rfl]
  constructor
  · rintro ⟨previous,branch,eqs⟩
    exact ⟨previous.1,branch⟩
  · rintro ⟨previous,branch⟩
    exact ⟨(point_initial_models _ _ (fun _ => rfl) m).mpr previous.1,branch,equations m previous.1⟩

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context true) displayRoot [.app 0 [.app 2 []]] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp only [zero]
  refine ⟨GeneralNominalGroundExamples.listTerm,⟨?_,rfl,⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩,?_⟩
  · simp [GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      GeneralNominalCompoundReadback.quote,GeneralNominalGroundExamples.listTerm,
      GeneralNominalGroundExamples.intTerm,List.ofFn_succ,GeneralNominalOriginTerms.arity,
      GeneralNormalizedObservation.Shape.arity]
  intro m valid
  exact GeneralNominalPeelingExamples.ground m valid

theorem point_source : GeneralNominalActualBudget.PointSource (context true) displayRoot :=
  GeneralNominalPeelingExamples.point_source

theorem usable : GeneralNominalSharedCaptures.Usable packet 0 origin :=
  GeneralNominalSharedPositive.single_capture_usable packet 0 (1,1) origin
    (by rw [raw_report]; rfl) inherited
    (by rw [raw_report]; simp [GeneralNominalUnaryCaptureFacts.captured,origin])

theorem origin_unique (demand : Occurrence roles) (position : Nat) (observed : Origin)
    (found : GeneralNominalSharedEmission.OriginAt packet demand position observed) : observed = origin := by
  obtain ⟨_,_,_,_,_,_,_,known,_⟩ := found
  obtain ⟨captured,member,_,same⟩ := known.1.1
  rw [inherited] at member
  cases List.mem_singleton.mp member
  exact (Option.some.inj same).symm

noncomputable abbrev rawSite (n : Nat) := GeneralNominalSharedEmission.childSite packet (child n)

theorem raw_inputs (n : Nat) (which : n = 10 ∨ n = 11) : (rawSite n).inputs = [some origin] := by
  classical
  have available : ∃ observed, GeneralNominalSharedEmission.OriginAt packet (child n) 0 observed := by
    refine ⟨origin,?_⟩
    rcases which with rfl | rfl
    · exact ⟨GeneralDeclarationExamples.displayChild,by simp [declaration],_,(0 : Fin 1),
        (congrArg Site.occurrence first_child).symm,rfl,0,usable,rfl⟩
    · exact ⟨GeneralDictionaryEarlyMergeExample.secondClause,by simp [declaration],_,(0 : Fin 1),
        (congrArg Site.occurrence second_child).symm,rfl,0,usable,rfl⟩
  change List.ofFn (GeneralNominalSharedEmission.childOrigin packet (child n)) = _
  change [GeneralNominalSharedEmission.childOrigin packet (child n) (0 : Fin 1)] = _
  apply congrArg (fun x => [x])
  unfold GeneralNominalSharedEmission.childOrigin
  change (if h : ∃ observed, GeneralNominalSharedEmission.OriginAt packet (child n) 0 observed then
    some (Classical.choose h) else _) = some origin
  rw [dite_eq_left available]
  exact congrArg some (origin_unique _ _ _ (Classical.choose_spec available))

theorem raw_sites : before.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite displayRoot,rawSite 10,rawSite 11] := by
  change [GeneralNominalDemandMerging.pointSite displayRoot] ++ packet.children.map _ = _
  change [GeneralNominalDemandMerging.pointSite displayRoot] ++ GeneralDictionaryEarlyMergeExample.children.map _ = _
  rw [GeneralDictionaryEarlyMergeExample.children_exact]
  rfl

theorem center_sites : before.sites = [plan.input,centerSite 10,centerSite 11] := by
  change [plan.input] ++ plan.emitted = _
  rw [emitted]
  rfl

theorem center_inputs (n : Nat) : (centerSite n).observed.inputs = [some (.source 1)] := rfl

theorem recovered_center (n : Nat) :
    (GeneralNominalFeedbackSites.recover before.erased.current (centerSite n).observed).inputs = [some (.source 1)] := rfl

theorem center_same : SameInputs (Models before) (centerSite 10) (centerSite 11) :=
  ⟨rfl,.cons ⟨.source 1,.source 1,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩

theorem center_recovery_supported (n : Nat) : GeneralNominalSupportChoices.RecoverySupported
    before.erased (centerSite n).observed [] := by
  intro index absent
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  rw [center_inputs,zero] at absent
  cases absent

theorem center_merge_guard : GeneralNominalSupportChoices.MergeGuard before.erased
    (centerSite 10).observed (centerSite 11).observed [] :=
  ⟨⟨rfl,.cons ⟨.source 1,.source 1,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩,
    center_recovery_supported 10,center_recovery_supported 11⟩

theorem child_generated : GeneralNominalSaturationState.Generated before.erased.current displayRoot (child 10) := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (displayRoot,child 10) ∈ [] ++ packet.children.map (fun c => (displayRoot,c))
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨child 10,?_,rfl⟩
  change child 10 ∈ GeneralDictionaryEarlyMergeExample.children
  rw [GeneralDictionaryEarlyMergeExample.children_exact]
  simp

theorem child_not_aliased : ¬ GeneralNominalSaturationState.Alias before.erased.current
    (child 10).identity (child 11).identity := by
  have equal : ∀ a b, GeneralNominalSaturationState.Alias before.erased.current a b → a = b := by
    intro a b related
    induction related with
    | refl => rfl
    | edge member => cases member
    | symm _ ih => exact ih.symm
    | trans _ _ left right => exact left.trans right
  intro related
  have same := (GeneralNominalIdentities.source_identity (state true).seed _ _).mp (equal _ _ related)
  have impossible := congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same
  contradiction

noncomputable abbrev finish := GeneralNominalCenteredSteps.merge before (centerSite 10) (centerSite 11) []

theorem second_step : Step registry displayRoot before finish := by
  refine ⟨child 10,child_generated,.merge (centerSite 10) (centerSite 11) [] ?_ ?_
    center_same child_not_aliased center_merge_guard⟩
  · rw [center_sites]; simp
  · rw [center_sites]; simp

theorem reachable_finish : B4TargetV5.Reachable (GeneralNominalCenteredBoundary.boundary roles) registry displayRoot finish :=
  ⟨start,initial_source,.tail (.tail .refl first_step) second_step⟩

theorem center_unregistered : (centerSite 10).observed ∉ before.erased.current.sites := by
  rw [raw_sites]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rintro (root | first | last)
  · have identity := congrArg (fun s : GeneralNominalDemandMerging.Site roles => s.occurrence.identity) root
    have above := GeneralNominalIdentities.source_above_invocation (state true).seed (100,1,6,10,0)
    change GeneralNominalIdentities.source (state true).seed (100,1,6,10,0) = 100 at identity
    omega
  · have inputs := congrArg GeneralNominalDemandMerging.Site.inputs first
    rw [center_inputs,raw_inputs 10 (Or.inl rfl)] at inputs
    cases inputs
  · have inputs := congrArg GeneralNominalDemandMerging.Site.inputs last
    rw [center_inputs,raw_inputs 11 (Or.inr rfl)] at inputs
    cases inputs

theorem no_previous_merge (support : List (Occurrence roles)) :
    GeneralNominalSupport.Fact.merge (centerSite 10).observed (centerSite 11).observed support ∉ before.erased.facts := by
  intro member
  rcases List.mem_append.mp member with added | old
  · exact GeneralNominalCenteredMergeBridge.no_merge_in_install start.erased packet _ _ support added
  · cases old

theorem no_exact_erasure : ¬ GeneralNominalActualInspectionSteps.Step registry displayRoot before.erased finish.erased :=
  GeneralNominalCenteredMergeBridge.centered_merge_not_exact before (centerSite 10) (centerSite 11) []
    center_merge_guard center_unregistered no_previous_merge

theorem recovered_raw (n : Nat) (which : n = 10 ∨ n = 11) :
    (GeneralNominalFeedbackSites.recover before.erased.current (rawSite n)).inputs = [some origin] := by
  change [GeneralNominalFeedbackSites.recoverOrigin before.erased.current (rawSite n) (0 : Fin 1)] = _
  unfold GeneralNominalFeedbackSites.recoverOrigin
  simp only [raw_inputs n which]
  rfl

theorem origin_same (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m) :
    (∃ value, Observes m origin value) ∧ (∃ value, Observes m origin value) ∧
    ∀ a b, Observes m origin a → Observes m origin b → Equivalent a b := by
  have bounds := nominal_argument_bounds (state true) m valid 0 listDescriptor rfl 0 (1,1) rfl
  refine ⟨bounds.1,bounds.1,?_⟩
  intro a b ha hb
  exact ⟨subtype_trans (bounds.2 a ha).2 (bounds.2 b hb).1,
    subtype_trans (bounds.2 b hb).2 (bounds.2 a ha).1⟩

theorem raw_same : GeneralNominalFeedbackSites.SameInputs before.erased.current (rawSite 10) (rawSite 11) := by
  refine ⟨rfl,?_⟩
  change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related _) _ _
  rw [recovered_raw 10 (Or.inl rfl),recovered_raw 11 (Or.inr rfl)]
  refine .cons ⟨origin,origin,rfl,rfl,?_⟩ .nil
  intro m valid
  have previous := ((GeneralNominalSharedSteps.install_models (packet := packet)
    (state := start.erased) (support := []) rfl m).mp valid).1
  exact origin_same m previous.1

theorem raw_recovery_supported (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalSupportChoices.RecoverySupported before.erased (rawSite n) [] := by
  intro index absent
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  rw [raw_inputs n which,zero] at absent
  cases absent

theorem raw_merge_guard : GeneralNominalSupportChoices.MergeGuard before.erased (rawSite 10) (rawSite 11) [] := by
  refine ⟨⟨rfl,?_⟩,raw_recovery_supported 10 (Or.inl rfl),raw_recovery_supported 11 (Or.inr rfl)⟩
  change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related _) _ _
  rw [recovered_raw 10 (Or.inl rfl),recovered_raw 11 (Or.inr rfl)]
  exact .cons ⟨origin,origin,rfl,rfl,fun m valid => origin_same m valid.1⟩ .nil

noncomputable abbrev rawFinish := GeneralNominalSharedSteps.merge before.erased (rawSite 10) (rawSite 11) []

theorem raw_second_step : GeneralNominalActualInspectionSteps.Step registry displayRoot before.erased rawFinish := by
  refine ⟨child 10,child_generated,.merge (rawSite 10) (rawSite 11) [] ?_ ?_
    raw_same child_not_aliased raw_merge_guard⟩
  · rw [raw_sites]; simp
  · rw [raw_sites]; simp

theorem finish_current_equal : finish.erased.current = rawFinish.current :=
  GeneralNominalCenteredMergeBridge.merge_current_same_occurrences before.erased _ _ _ _ [] [] rfl rfl

theorem finish_slices_equal (support : List (Occurrence roles)) (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalSupport.Slice finish.erased support m ↔ GeneralNominalSupport.Slice rawFinish support m :=
  (GeneralNominalCenteredMergeBridge.merge_empty_outputs_slices before.erased
    (centerSite 10).observed (centerSite 11).observed [] support rfl m).trans
  (GeneralNominalCenteredMergeBridge.merge_empty_outputs_slices before.erased
    (rawSite 10) (rawSite 11) [] support rfl m).symm

theorem ground_point_counterexample :
    GeneralDeclarations.Checked registry ∧ InitialSource registry displayRoot start ∧
    GeneralNominalActualBudget.PointSource (context true) displayRoot ∧
    GeneralNominalGroundAccessibility.GroundRoots (context true) displayRoot [.app 0 [.app 2 []]] ∧
    B4Target.Steps (Step registry displayRoot) start before ∧ Step registry displayRoot before finish ∧
    ¬ GeneralNominalActualInspectionSteps.Step registry displayRoot before.erased finish.erased :=
  ⟨GeneralDictionaryEarlyMergeExample.registry_checked,initial_source,point_source,ground,
    .tail .refl first_step,second_step,no_exact_erasure⟩

theorem matching_raw_merge :
    GeneralNominalActualInspectionSteps.Step registry displayRoot before.erased rawFinish ∧
    finish.erased.current = rawFinish.current ∧
    ∀ support m, GeneralNominalSupport.Slice finish.erased support m ↔ GeneralNominalSupport.Slice rawFinish support m :=
  ⟨raw_second_step,finish_current_equal,finish_slices_equal⟩

theorem raw_generation : GeneralNominalSharedCaptures.GenerationGuard start.erased packet := by
  rintro name ⟨clause,member,used⟩
  have zero : name = 0 := by
    change clause ∈ declaration.requirements at member
    simp only [declaration,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDictionaryEarlyMergeExample.secondClause,GeneralDeclarationExamples.displayChild] using used
  subst name
  exact ⟨origin,usable⟩

theorem raw_inspection :
    (GeneralNominalActualInspectionSteps.inspection start.erased.current packet).inspected = [(0,0)] ∧
    (GeneralNominalActualInspectionSteps.inspection start.erased.current packet).tests.map Prod.fst = [.source 0] := by
  cbv
  exact ⟨rfl,trivial⟩

theorem raw_safe : GeneralNominalActualInspectionSteps.Safe start.erased.current packet := by
  constructor
  · rw [raw_inspection.1]
    simpa only [List.length_map,List.length_cons,List.length_nil] using (congrArg List.length raw_inspection.2).symm
  · intro entry present
    have member : entry.1 ∈ (GeneralNominalActualInspectionSteps.inspection start.erased.current packet).tests.map Prod.fst :=
      List.mem_map.mpr ⟨entry,present,rfl⟩
    rw [raw_inspection.2] at member
    rw [List.mem_singleton.mp member]
    constructor
    · refine ⟨0,?_,GeneralNominalDemandMerging.source_same _ 0⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))
    · exact fun cycle => initial_acyclic _ (Or.inl cycle)

theorem raw_guard : GeneralNominalActualInspectionSteps.PacketGuard start.erased packet [] := by
  refine ⟨⟨GeneralNominalValueSupport.source_packet _ _ GeneralDictionaryEarlyMergeExample.packet_guard,
    GeneralNominalSharedPositive.initial_decision _ _ _ _ []
      (GeneralDictionaryEarlyMergeExample.all_source_decisions displayRoot (fun _ => rfl)),
    raw_generation,GeneralNominalSharedCaptures.empty_input_coherent (congrArg (·.variables) input_empty)⟩,
    raw_safe,?_⟩
  intro other visible check role ready bounds located
  cases List.mem_singleton.mp visible
  have same : bounds = [((0 : Fin 2),(0 : Fin 2))] := Option.some.inj located.symm
  subst bounds
  exact raw_safe

theorem raw_first_step : GeneralNominalActualInspectionSteps.Step registry displayRoot start.erased before.erased :=
  ⟨displayRoot,.root,.install packet [] enabled novel raw_guard⟩

theorem matching_raw_path :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry displayRoot) start.erased rawFinish ∧
    finish.erased.current = rawFinish.current ∧
    ∀ support m, GeneralNominalSupport.Slice finish.erased support m ↔ GeneralNominalSupport.Slice rawFinish support m :=
  ⟨.tail (.tail .refl raw_first_step) raw_second_step,finish_current_equal,finish_slices_equal⟩

theorem before_inhabited : Models before model :=
  (GeneralNominalCenteredSteps.install_models (plan := plan) (state := start) (support := []) rfl model).mpr
    ⟨(point_initial_models _ _ (fun _ => rfl) model).mpr (state_models true),
      branch model (state_models true),equations model (state_models true)⟩

theorem finish_inhabited : Models finish model :=
  ⟨(GeneralNominalSaturationState.merge_models before.erased.current (centerSite 10).observed
    (centerSite 11).observed model).mpr ⟨before_inhabited.1,by intro atom member; cases member⟩,
    before_inhabited.2⟩

theorem initial_selected : GeneralNominalCenteredBoundary.Local registry start displayRoot
    (.selected declaration.id packet.children) :=
  GeneralNominalCenteredBoundary.installable_selected ⟨enabled,[],guard⟩

end Yulang.GeneralNominalCenteredPointMergeExample
