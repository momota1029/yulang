import Yulang.GeneralDictionaryHistoricalValueRequests

/-! Variable-free tests from recorded requests survive actual value traces, including
fresh output targets absent from the initial source carrier. No source
observation premise occurs. This is not full current head or Instance replay. -/
namespace Yulang.GeneralDictionaryRecordedRequestModels
open GeneralNominalSaturationState GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalMaterialization

private theorem generated_tests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request) :
    (generated state interpretation batch).tests = batch.flatMap (fun request =>
      (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode).tests) := by
  induction batch with
  | nil => rfl
  | cons first rest ih =>
    simp only [generated,List.map_cons,List.foldr_cons,Schema.append,List.flatMap_cons]
    exact congrArg (fun tail => _ ++ tail) ih

theorem subset_tests (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (small large : List Request)
    (included : ∀ request ∈ small, request ∈ large) :
    ∀ test ∈ (generated state interpretation small).tests,
      test ∈ (generated state interpretation large).tests := by
  intro test member
  rw [generated_tests] at member ⊢
  obtain ⟨request,present,member⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨request,included request present,member⟩

/-- This condition is derived from actual reachability below; it is not a
model-validity assumption. -/
def SchemaCoherent (state : State roles) : Prop :=
  ∀ packet ∈ state.packets, ∀ batch,
    generated state.context.state state.context.interpretation batch =
      generated packet.context.state packet.context.interpretation batch

theorem coherent_at (registry : Registry) (before after : State roles)
    (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (coherent : SchemaCoherent before) : SchemaCoherent after := by
  intro packet member batch
  have same := GeneralDictionaryHistoricalValueRequests.at_generated registry before after focus step batch
  rw [same]
  cases step with
  | reobserve => exact coherent packet member batch
  | ordinary action =>
    cases action with
    | enqueue => exact coherent packet member batch
    | install installed enabled novel =>
      change packet ∈ installed :: before.packets at member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.1.2.1]
      · exact coherent packet member batch
    | merge => exact coherent packet member batch
    | refresh => exact coherent packet member batch
    | equate => exact coherent packet member batch

theorem coherent_trace (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (coherent : SchemaCoherent before) : SchemaCoherent after := by
  induction path with
  | refl => exact coherent
  | tail _ step ih => exact coherent_at registry _ _ _ step.choose_spec.2 ih

theorem reachable_coherent (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    SchemaCoherent state.current := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  apply coherent_trace registry root (GeneralNominalSaturationState.initial context root) state.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry root _ _ path)
  intro packet member
  cases member

/-- A variable-free sub-batch of actual recorded materialization requests is valid
for arbitrary current report/capture data. Targets may be freshly allocated;
no initial-source observation or target-slot witness is needed. The unknown
flag is not constrained: this theorem supplies Models, not RequestReady. -/
theorem recorded_variableFree_models (state : State roles) (coherent : SchemaCoherent state)
    (packet : Packet roles) (member : packet ∈ state.packets) (batch : List Request)
    (included : ∀ request ∈ batch, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings)
    (closed : (generated packet.context.state packet.context.interpretation batch).variables = [])
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralNominalMaterialization.Models state.context.state declaration capture report
      (generated state.context.state state.context.interpretation batch) model := by
  rw [coherent packet member batch]
  have recorded := (GeneralNominalPacketSupport.packet_exact packet model).mp (valid.2.1 packet member) |>.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro test present
    exact recorded.1 test (subset_tests _ _ _ _ included test present)
  · intro entry present; rw [closed] at present; cases present
  · intro entry present; rw [closed] at present; cases present
  · intro entry present; rw [closed] at present; cases present

theorem reachable_root_requests (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (closed : (generated packet.context.state packet.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = [])
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation
        (rootRequests packet.declaration packet.site.occurrence)) model :=
  recorded_variableFree_models state.current (reachable_coherent registry root state reachable) packet member _
    (fun _ present => List.mem_append_left _ present) closed declaration capture report model valid



private theorem generated_known_iff (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request) :
    (generated state interpretation batch).unknown = false ↔
      ∀ request ∈ batch, (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode).unknown = false := by
  induction batch with
  | nil => simp [generated]
  | cons first rest ih =>
    change (_ || (generated state interpretation rest).unknown) = false ↔ _
    simp only [Bool.or_eq_false_iff,ih,List.mem_cons,forall_eq_or_imp]

theorem subset_known (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (small large : List Request)
    (included : ∀ request ∈ small, request ∈ large)
    (known : (generated state interpretation large).unknown = false) :
    (generated state interpretation small).unknown = false :=
  (generated_known_iff state interpretation small).mpr
    (fun request member => (generated_known_iff state interpretation large).mp known request (included request member))

/-- Recorded readiness is historical syntactic provenance, independent of
whether the journal has any model. -/
def RequestsKnown (state : State roles) : Prop :=
  ∀ packet ∈ state.packets, (GeneralNominalPacketSupport.namedSchema packet).unknown = false

theorem requestsKnown_at (registry : Registry) (before after : State roles)
    (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (known : RequestsKnown before) : RequestsKnown after := by
  intro packet member
  cases step with
  | reobserve => exact known packet member
  | ordinary action =>
    cases action with
    | enqueue => exact known packet member
    | merge => exact known packet member
    | refresh => exact known packet member
    | equate => exact known packet member
    | install installed enabled novel =>
      change packet ∈ installed :: before.packets at member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨_,_,_,_,_,located,prepared,_⟩ := enabled.1
        obtain ⟨_,_,_,bounds,found,_,ready,_⟩ := prepared
        have same := Option.some.inj (found.symm.trans located)
        subst bounds
        exact ready.2
      · exact known packet member

theorem requestsKnown_trace (registry : Registry) (root : Occurrence roles)
    (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (known : RequestsKnown before) : RequestsKnown after := by
  induction path with
  | refl => exact known
  | tail _ step ih => exact requestsKnown_at registry _ _ _ step.choose_spec.2 ih

theorem reachable_requestsKnown (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    RequestsKnown state.current := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  apply requestsKnown_trace registry root (GeneralNominalSaturationState.initial context root) state.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry root _ _ path)
  intro packet member
  cases member

/-- Every request sub-batch from an actually recorded packet is syntactically
known even after arbitrary Value transitions. No unknown=false premise is used. -/
theorem reachable_subset_known (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (batch : List Request)
    (included : ∀ request ∈ batch, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings) :
    (generated state.current.context.state state.current.context.interpretation batch).unknown = false := by
  rw [reachable_coherent registry root state reachable packet member batch]
  exact subset_known _ _ _ _ included (reachable_requestsKnown registry root state reachable packet member)

/-- Root outputs of a recorded packet have no deferred schema, and when their
variable list is empty they are fully closed in the current context. -/
theorem reachable_root_closed (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (closed : (generated packet.context.state packet.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = []) :
    (generated state.current.context.state state.current.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = [] ∧
    (generated state.current.context.state state.current.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).unknown = false := by
  constructor
  · rw [reachable_coherent registry root state reachable packet member _]
    exact closed
  · exact reachable_subset_known registry root state reachable packet member _
      (fun _ present => List.mem_append_left _ present)

end Yulang.GeneralDictionaryRecordedRequestModels
