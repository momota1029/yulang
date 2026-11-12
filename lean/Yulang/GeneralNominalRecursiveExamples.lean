import Yulang.GeneralNominalMixedExamples
import Yulang.GeneralNominalIntervalExamples

/-! Positive source regressions use the recursive candidate relation, the
actual nominal carrier, and the original deterministic emission identities. -/
namespace Yulang.GeneralNominalRecursiveExamples

open GeneralDeclarations
open GeneralDeclarationExamples (roles constructors display wrap display_checked wrap_checked)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates
open GeneralNominalUnaryCaptureFacts

private theorem primitive_metadata (registry : Registry) (context : Context)
    (same : registry.constructors = constructors) (stateSame : context.state.constructors = constructors)
    (interpretation : context.interpretation = GeneralNominalExamples.interpretation) : Metadata registry context := by
  refine ⟨same.trans stateSame.symm,?_⟩
  rw [same,interpretation]
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have equal : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

private theorem point_linked (state : GeneralNominalState.State) (root : GeneralSourceDictionaries.Occurrence roles)
    (slot : Fin state.base.slots)
    (arguments : ∀ index, root.demand.arguments index = (state.base.source slot,state.base.source slot))
    (outputs : root.demand.outputs = []) : GeneralNominalState.Linked state root.demand := by
  constructor
  · intro index
    rw [arguments index]
    have member : state.base.source slot ∈ GeneralNominalState.sources state := by
      unfold GeneralNominalState.sources
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
    exact ⟨member,member⟩
  · intro output member; rw [outputs] at member; cases member

private theorem point_ready (state : GeneralNominalState.State) (root : GeneralSourceDictionaries.Occurrence roles)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (arguments : ∀ index, root.demand.arguments index = (state.base.source slot,state.base.source slot)) :
    ¬ GeneralNominalState.RootPending state root.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  exact ⟨slot,by rw [arguments index],Or.inr ⟨descriptor,recorded⟩⟩

private theorem display_query (context : Context)
    (catalogue : context.state.constructors = constructors)
    (interpretation : context.interpretation = GeneralNominalExamples.interpretation) :
    GeneralNominalInspection.queries context.state context.interpretation display = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,catalogue,interpretation,
    GeneralNominalExamples.interpretation]

theorem display_schema (registry : Registry) (context : Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (outputs : root.demand.outputs = [])
    (checked : DeclarationChecked registry.constructors roles display)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    generated registry context root display checked bounds = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.rootRequests,outputs,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,
    GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated ]

private theorem unary_survivor (registry : Registry) (context : Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations) (checked : DeclarationChecked registry.constructors roles declaration)
    (role : declaration.role = root.demand.role)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor)
    (binder : Nat) (names : declaration.inputNames = [binder])
    (bounds : GeneralNominalInspection.Bounds context.state) (parameters : descriptor.arguments = [.type bounds])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder]]])
    (located : arguments context root = some [(slot,slot)])
    (metadata : Metadata registry context) (linked : GeneralNominalState.Linked context.state root.demand)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (fresh : GeneralNominalAllocation.Fresh context.state registry root.identity)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model)
    (requestReady : RequestReady registry context root declaration checked [(slot,slot)])
    (materialized : GeneralNominalMaterialization.Models context.state declaration
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration [(slot,slot)])))
      (report context declaration [(slot,slot)]) (generated registry context root declaration checked [(slot,slot)]) model) :
    Survivor registry context root declaration.id
      (GeneralNominalAllocation.children context.state registry root declaration checked
        [(binder,(context.state.base.source bounds.1,context.state.base.source bounds.2))]) := by
  have calculated := report_exact context declaration slot descriptor recorded binder bounds parameters query
  have branch := private_models context registry root declaration slot descriptor recorded binder names bounds parameters query model models
  refine ⟨ready,declaration,visible,checked,rfl,role,[(slot,slot)],located,?_,?_⟩
  · refine ⟨metadata,linked,fresh,[(slot,slot)],located,?_,requestReady,model,branch.1,branch.2,materialized⟩
    rw [calculated]
    exact ⟨rfl,rfl,rfl⟩
  · rw [calculated]; rfl

theorem display_survivor : Survivor GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.displayRoot 1 [GeneralNominalExamples.displayChild] := by
  have schema := display_schema GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.displayRoot rfl display_checked [(0,0)]
  have survivor := unary_survivor GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.displayRoot display (by simp) display_checked rfl
    0 GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl
    (display_query _ rfl rfl) (by decide +kernel)
    (primitive_metadata _ _ rfl rfl rfl)
    (point_linked _ _ 0 (fun _ => rfl) rfl)
    (point_ready _ _ 0 GeneralNominalExamples.listDescriptor rfl (fun _ => rfl))
    (initial_fresh _ _ _ (by decide +kernel)) GeneralNominalExamples.model (GeneralNominalExamples.state_models true)
    ⟨(by intro _ member; cases member),(by rw [schema])⟩
    (by rw [schema]; exact GeneralNominalMaterialization.empty_models ..)
  change Survivor _ _ _ 1 (GeneralNominalAllocation.children (GeneralNominalExamples.state true) _ _ display display_checked GeneralNominalExamples.captured) at survivor
  rw [GeneralNominalExamples.display_children] at survivor
  exact survivor

abbrev nonpointContext : Context := ⟨GeneralNominalIntervalExamples.source,GeneralNominalExamples.interpretation⟩
abbrev nonpointRoot : GeneralSourceDictionaries.Occurrence roles := GeneralNominalExamples.displayRoot
abbrev nonpointChildren := GeneralNominalAllocation.children GeneralNominalIntervalExamples.source
  GeneralNominalExamples.registry nonpointRoot display display_checked [(0,(2,3))]

theorem nonpoint_survivor (first last : Inference.Base) : Survivor GeneralNominalExamples.registry nonpointContext
    nonpointRoot 1 nonpointChildren := by
  have schema := display_schema GeneralNominalExamples.registry nonpointContext nonpointRoot rfl display_checked [(0,0)]
  exact unary_survivor GeneralNominalExamples.registry nonpointContext nonpointRoot display
    (by simp) display_checked rfl
    0 GeneralNominalIntervalExamples.descriptor rfl 0 rfl (2,3) rfl
    (display_query _ rfl rfl) (by decide +kernel)
    (primitive_metadata _ _ rfl rfl rfl)
    (point_linked _ _ 0 (fun _ => rfl) rfl)
    (point_ready _ _ 0 GeneralNominalIntervalExamples.descriptor rfl (fun _ => rfl))
    (initial_fresh _ _ _ (by decide +kernel)) (GeneralNominalIntervalExamples.model first last)
    (GeneralNominalIntervalExamples.source_models first last)
    ⟨(by intro _ member; cases member),(by rw [schema])⟩
    (by rw [schema]; exact GeneralNominalMaterialization.empty_models ..)

abbrev mixedChild : GeneralSourceDictionaries.Occurrence roles :=
  ⟨GeneralNominalAllocation.source GeneralNominalMixedExamples.state GeneralNominalExamples.registry 100
      (GeneralNominalAllocation.origin 100 1 6 10 0),GeneralNominalMixedExamples.childDemand⟩

theorem mixed_children : GeneralNominalAllocation.children GeneralNominalMixedExamples.state
    GeneralNominalExamples.registry GeneralNominalMixedExamples.showRoot display display_checked [(0,(0,0))] = [mixedChild] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,GeneralDeclarationPatterns.normalize,mixedChild]

theorem show_list_survivor : Survivor GeneralNominalExamples.registry GeneralNominalMixedExamples.context
    GeneralNominalMixedExamples.showRoot 1 [mixedChild] := by
  have schema := display_schema GeneralNominalExamples.registry GeneralNominalMixedExamples.context
    GeneralNominalMixedExamples.showRoot rfl display_checked [(1,1)]
  have survivor := unary_survivor GeneralNominalExamples.registry GeneralNominalMixedExamples.context
    GeneralNominalMixedExamples.showRoot display (by simp) display_checked rfl
    1 GeneralNominalMixedExamples.descriptor rfl 0 rfl (0,0) rfl
    (display_query _ rfl rfl) (by decide +kernel)
    (primitive_metadata _ _ rfl rfl rfl)
    (point_linked _ _ 1 (fun _ => rfl) rfl)
    (point_ready _ _ 1 GeneralNominalMixedExamples.descriptor rfl (fun _ => rfl))
    (initial_fresh _ _ _ (by decide +kernel)) GeneralNominalMixedExamples.model GeneralNominalMixedExamples.state_models
    ⟨(by intro _ member; cases member),(by rw [schema])⟩
    (by rw [schema]; exact GeneralNominalMaterialization.empty_models ..)
  change Survivor _ _ _ 1 (GeneralNominalAllocation.children GeneralNominalMixedExamples.state _ _ display display_checked [(0,(0,0))]) at survivor
  rw [mixed_children] at survivor
  exact survivor

theorem show_child_K2 : GeneralNominalMixedRecurrence.RootK2 GeneralNominalMixedExamples.state mixedChild.demand :=
  GeneralNominalMixedExamples.child_K2

theorem wrap_schema : generated GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.wrapRoot wrap wrap_checked [(0,0)] =
      { variables := [⟨1,.source GeneralNominalExamples.itemTarget,.actual⟩] } := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,
    GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalExamples.itemTarget,GeneralNominalInspection.translate]

theorem wrap_survivor : Survivor GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.wrapRoot 2 [GeneralNominalExamples.wrapChild] := by
  have query : GeneralNominalInspection.queries (GeneralNominalExamples.state true) GeneralNominalExamples.interpretation wrap =
      [.nominal 0 [.variables [0]]] := display_query (GeneralNominalExamples.context true) rfl rfl
  have calculated := report_exact (GeneralNominalExamples.context true) wrap 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl query
  have materialized : GeneralNominalMaterialization.Models (GeneralNominalExamples.state true) wrap
      (GeneralNominalAllocation.capture (GeneralNominalExamples.state true) GeneralNominalExamples.registry 101 2
        (bindings (GeneralNominalExamples.state true) (report (GeneralNominalExamples.context true) wrap [(0,0)])))
      (report (GeneralNominalExamples.context true) wrap [(0,0)])
      (generated GeneralNominalExamples.registry (GeneralNominalExamples.context true) GeneralNominalExamples.wrapRoot wrap wrap_checked [(0,0)])
      GeneralNominalExamples.model := by
    rw [wrap_schema,calculated]
    refine ⟨?_,?_,?_,?_⟩
    · intro test member; cases member
    · intro entry member
      have same := List.mem_singleton.mp member; subst entry
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      change CommonNominalFullCarrier.Equivalent _ _
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · intro first one last two _ _ _ a b ha hb
      have ae := List.mem_singleton.mp one; have be := List.mem_singleton.mp two
      subst first; subst last; cases ha; cases hb
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · intro entry member cap present same
      have ae := List.mem_singleton.mp member; have be := List.mem_singleton.mp present
      subst entry; subst cap
      cases same
  have survivor := unary_survivor GeneralNominalExamples.registry (GeneralNominalExamples.context true)
    GeneralNominalExamples.wrapRoot wrap (by simp) wrap_checked rfl
    0 GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl query (by decide +kernel)
    (primitive_metadata _ _ rfl rfl rfl)
    (point_linked _ _ 0 (fun _ => rfl) rfl)
    (point_ready _ _ 0 GeneralNominalExamples.listDescriptor rfl (fun _ => rfl))
    (initial_fresh _ _ _ (by decide +kernel)) GeneralNominalExamples.model (GeneralNominalExamples.state_models true)
    ⟨(by intro _ member; cases member),(by rw [wrap_schema])⟩ materialized
  change Survivor _ _ _ 2 (GeneralNominalAllocation.children (GeneralNominalExamples.state true) _ _ wrap wrap_checked GeneralNominalExamples.captured) at survivor
  rw [GeneralNominalExamples.wrap_children] at survivor
  exact survivor

abbrev len : Declaration := ⟨30,3,[.app 0 [.var 0]],[],[],[]⟩
abbrev lenRegistry : Registry := ⟨constructors,roles,[len]⟩
abbrev lenRoot : GeneralSourceDictionaries.Occurrence roles :=
  ⟨200,⟨3,fun _ => (1,1),[],by intro _ member; cases member⟩⟩

theorem len_checked : DeclarationChecked constructors roles len := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,GeneralDeclarationPatterns.WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

theorem len_schema : generated lenRegistry GeneralNominalMixedExamples.context lenRoot len len_checked [(1,1)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    len,List.mergeSort_nil]
  rfl

theorem len_list_survivor : Survivor lenRegistry GeneralNominalMixedExamples.context lenRoot 30 [] := by
  have query : GeneralNominalInspection.queries GeneralNominalMixedExamples.state GeneralNominalExamples.interpretation len =
      [.nominal 0 [.variables [0]]] := display_query GeneralNominalMixedExamples.context rfl rfl
  have survivor := unary_survivor lenRegistry GeneralNominalMixedExamples.context lenRoot len (by simp) len_checked rfl
    1 GeneralNominalMixedExamples.descriptor rfl 0 rfl (0,0) rfl query (by decide +kernel)
    (primitive_metadata _ _ rfl rfl rfl)
    (point_linked _ _ 1 (fun _ => rfl) rfl)
    (point_ready _ _ 1 GeneralNominalMixedExamples.descriptor rfl (fun _ => rfl))
    (initial_fresh _ _ _ (by decide +kernel)) GeneralNominalMixedExamples.model GeneralNominalMixedExamples.state_models
    ⟨(by intro _ member; cases member),(by rw [len_schema])⟩
    (by rw [len_schema]; exact GeneralNominalMaterialization.empty_models ..)
  have children (captures : GeneralNominalAllocation.Bindings) :
      GeneralNominalAllocation.children GeneralNominalMixedExamples.state lenRegistry lenRoot len len_checked captures = [] := by
    unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      List.mergeSort_nil]
    rfl
  rw [children] at survivor
  exact survivor

end Yulang.GeneralNominalRecursiveExamples
