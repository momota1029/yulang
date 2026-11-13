import Yulang.GeneralDictionaryRecordedRequestModels

/-! Materialization replay with variable-bearing schemas. Unlike variable-free
request replay, this theorem explicitly checks the finite capture footprint:
source identities agree and every current nominal-origin capture was present
historically. Neither Models nor variable meaning is hidden in this certificate. -/
namespace Yulang.GeneralDictionaryCapturedSchemaTransport
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization
open GeneralNominalRecursiveInspection GeneralNominalSaturationState
variable {roles : Roles.RoleDecls}

structure Footprint (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State}
    (oldReport : Report oldState) (currentReport : Report currentState) (schema : Schema) : Prop where
  outputs : ∀ entry ∈ schema.variables, entry.name ∈ declaration.outputNames →
    currentCapture.outputs entry.name = oldCapture.outputs entry.name
  inputs : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames →
    currentCapture.inputs entry.name = oldCapture.inputs entry.name
  origins : ∀ entry ∈ schema.variables, ∀ captured ∈ currentReport.captures,
    entry.name = captured.name → entry.mode = .actual → ∀ origin, captured.origin = some origin →
    ∃ old ∈ oldReport.captures, old.name = captured.name ∧ old.origin = some origin

theorem variable_meaning (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (schema : Schema)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport schema)
    (entry : Use) (member : entry ∈ schema.variables)
    (model : GeneralNominalCommonBridge.Assignment) (actual : CommonNominalFullCarrier.Ty) :
    VariableHolds declaration currentCapture model entry.name entry.mode actual ↔
      VariableHolds declaration oldCapture model entry.name entry.mode actual := by
  unfold VariableHolds
  by_cases output : entry.name ∈ declaration.outputNames
  · simp only [output,ite_true,footprint.outputs entry member output]
  · simp only [output,ite_false]
    rw [footprint.inputs entry member output]

theorem replay (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (small large : Schema)
    (variables : ∀ entry ∈ small.variables, entry ∈ large.variables)
    (tests : ∀ test ∈ small.tests, test ∈ large.tests)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport small)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalMaterialization.Models oldState declaration oldCapture oldReport large model) :
    GeneralNominalMaterialization.Models currentState declaration currentCapture currentReport small model := by
  refine ⟨fun test member => valid.1 test (tests test member),?_,?_,?_⟩
  · intro entry member
    refine ⟨(valid.2.1 entry (variables entry member)).1,?_⟩
    intro actual seen
    exact (variable_meaning declaration oldCapture currentCapture oldReport currentReport small
      footprint entry member model actual).mpr ((valid.2.1 entry (variables entry member)).2 actual seen)
  · intro first one last two same firstActual lastActual a b oneSeen twoSeen
    exact valid.2.2.1 first (variables first one) last (variables last two) same firstActual lastActual a b oneSeen twoSeen
  · intro entry member captured present same actual origin known a b seen observed
    obtain ⟨old,oldMember,names,oldOrigin⟩ := footprint.origins entry member captured present same actual origin known
    exact valid.2.2.2 entry (variables entry member) old oldMember (same.trans names.symm) actual
      origin oldOrigin a b seen observed

/-- The same report and capture trivially satisfy the finite syntactic footprint. -/
theorem footprint_refl (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (schema : Schema) : Footprint declaration capture capture report report schema := by
  refine ⟨by intros; rfl,by intros; rfl,?_⟩
  intro entry member captured present same actual origin known
  exact ⟨captured,present,rfl,known⟩

/-- Replay a complete historically recorded packet schema after actual Value
steps. Variables are permitted; the capture/origin footprint is explicit. -/
theorem recorded_replay (registry : Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (capture : GeneralDeclarationDemands.Capture)
    (report : Report state.current.context.state)
    (footprint : Footprint packet.declaration (GeneralNominalPacketSupport.capture packet) capture
      (GeneralNominalPacketSupport.report packet) report (GeneralNominalPacketSupport.namedSchema packet))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state packet.declaration capture report
      (generated state.current.context.state state.current.context.interpretation
        (requests packet.context.state packet.registry packet.site.occurrence
          packet.declaration packet.checked packet.bindings)) model := by
  rw [GeneralDictionaryRecordedRequestModels.reachable_coherent registry root state reachable packet recorded]
  exact replay packet.declaration _ capture _ report _ _ (fun _ member => member)
    (fun _ member => member) footprint model (valid.2.1 packet recorded).2.2
end Yulang.GeneralDictionaryCapturedSchemaTransport
