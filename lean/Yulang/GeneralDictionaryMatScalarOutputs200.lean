import Yulang.GeneralDictionaryMatVariableNode199

set_option backward.isDefEq.respectTransparency false

/-! Named scalar output compatibility for the actual total materializer.
The source restriction concerns compiler results, not assumed old semantics. -/
namespace Yulang.GeneralDictionaryMatScalarOutputs200
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVariableRequirements (VariableClauses)
open CommonRoleOutermostResolver (All₂ Dictionary)
open CommonNominalFullCarrier

/-- Every request has a scalar inspection and the same total scalar expression. -/
def ScalarRequests (registry : Registry) (context : Context)
    (requests : List GeneralNominalMaterialization.Request) : Prop :=
  ∀ request ∈ requests, ∃ base,
    GeneralNominalInspection.translate context.state.constructors context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = .scalar base ∧
    GeneralNominalCenteredHeadMatExpressions.translate registry.constructors context.interpretation
      request.pattern = some (.primitive (.scalar base) [])

theorem scalar_schema (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (model : Assignment)
    (requests : List GeneralNominalMaterialization.Request)
    (valid : ∀ request ∈ requests, ∃ base,
      GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern) = .scalar base ∧
      Equivalent (model request.target).1 (.base base)) :
    (GeneralNominalMaterialization.generated state interpretation requests).unknown = false ∧
    GeneralNominalMaterialization.Models state declaration capture report
      (GeneralNominalMaterialization.generated state interpretation requests) model := by
  have shape : ∃ tests, GeneralNominalMaterialization.generated state interpretation requests =
      ⟨[],tests,false⟩ ∧ ∀ test ∈ tests,
        (∃ actual, Observes model test.1 actual) ∧
        ∀ actual, Observes model test.1 actual → test.2.Holds actual := by
    induction requests with
    | nil => exact ⟨[],rfl,by simp⟩
    | cons first rest ih =>
      obtain ⟨base,translated,equation⟩ := valid first (by simp)
      obtain ⟨tests,equal,holds⟩ := ih (fun request member => valid request (by simp [member]))
      refine ⟨(.source first.target,Test.scalar base) :: tests, ?_, ?_⟩
      · simp only [GeneralNominalMaterialization.generated, List.map_cons, List.foldr_cons]
        change (GeneralNominalMaterialization.schema _ _ _).append
          (GeneralNominalMaterialization.generated state interpretation rest) = _
        rw [translated,equal]
        simp [GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]
      · intro test member
        rcases List.mem_cons.mp member with rfl | member
        · refine ⟨⟨_,.source first.target⟩,?_⟩
          intro actual seen
          cases seen
          exact equation
        · exact holds test member
  obtain ⟨tests,equal,holds⟩ := shape
  rw [equal]
  exact ⟨rfl,holds,by simp,by simp,by simp⟩

variable {roles : Roles.RoleDecls} (plan : Plan roles)

theorem requests_root (variables : VariableClauses plan.packet.declaration) :
    GeneralNominalMaterialization.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings =
    GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence := by
  unfold GeneralNominalMaterialization.requests
  suffices (GeneralCanonicalChildOrder.canonicalEmit plan.packet.site.occurrence.identity
    plan.packet.declaration plan.packet.checked
    (GeneralNominalAllocation.capture plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.bindings)
    (GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence.identity plan.packet.declaration.id)).flatMap
      GeneralNominalMaterialization.emissionRequests = [] by rw [this,List.append_nil]
  apply List.flatMap_eq_nil_iff.mpr
  intro emission member
  unfold GeneralCanonicalChildOrder.canonicalEmit GeneralDeclarationDemands.emitAll at member
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have present : clause.val ∈ plan.packet.declaration.requirements :=
    (GeneralCanonicalChildOrder.canonicalRequirements_perm plan.packet.declaration.requirements).mem_iff.mpr clause.property
  exact GeneralDictionaryVariableRequirements.emission_empty _ _ _ _ _ _
    (variables clause.val present).1 (variables clause.val present).2

theorem materialization_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (scalars : ScalarRequests plan.packet.registry plan.packet.context
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence)) :
    (generated plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false ∧
    GeneralNominalMaterialization.Models plan.packet.context.state plan.packet.declaration
      (GeneralNominalAllocation.capture plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.bindings)
      (report plan.packet.context plan.packet.declaration plan.packet.bounds)
      (generated plan.packet.registry plan.packet.context plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bounds) assignment := by
  unfold generated
  change (GeneralNominalMaterialization.generated _ _
    (GeneralNominalMaterialization.requests _ _ _ _ _ plan.packet.bindings)).unknown = false ∧
    GeneralNominalMaterialization.Models _ _ _ _
      (GeneralNominalMaterialization.generated _ _
        (GeneralNominalMaterialization.requests _ _ _ _ _ plan.packet.bindings)) assignment
  rw [requests_root plan variables]
  apply scalar_schema
  intro request member
  obtain ⟨base,old,total⟩ := scalars request member
  refine ⟨base,old,?_⟩
  have equation := GeneralNominalCenteredHeadMatStepPackets.output_equation holds.2.2
    (List.mem_append_left _ member) total
  exact equation

theorem branch_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (scalars : ScalarRequests plan.packet.registry plan.packet.context
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence)) :
    BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bounds assignment :=
  ⟨GeneralNominalCenteredHeadMatStepPackets.private_models holds,holds.2.1.2.1,
    (materialization_of_total plan assignment holds variables scalars).2⟩

theorem instance_of_total (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined plan.packet.declaration plan.packet.site.occurrence)
    (scalars : ScalarRequests plan.packet.registry plan.packet.context
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence))
    (visible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (role : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role)
    (located : arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (finished : Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds))
    (metadata : Metadata plan.packet.registry plan.packet.context) :
    GeneralDictionaryRecursiveEvidence.Instance plan.packet.registry plan.packet.context assignment
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
  refine ⟨plan.packet.declaration,visible,plan.packet.checked,rfl,role,plan.packet.bounds,
    located,finished,⟨defined,(materialization_of_total plan assignment holds variables scalars).1⟩,rfl,metadata,branch_of_total plan assignment holds variables scalars⟩

theorem evidence_of_frame_total (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (framed : GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (assignment : Assignment)
    (holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment)
    (variables : VariableClauses plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined plan.packet.declaration plan.packet.site.occurrence)
    (scalars : ScalarRequests plan.packet.registry plan.packet.context
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence))
    (dictionaries : List Dictionary)
    (children : All₂ (fun child dictionary =>
      (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
        child dictionary) plan.packet.children dictionaries) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id dictionaries) := by
  have prepared : GeneralNominalCenteredHeadCandidates.Prepared plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration := by
    rw [framed.context_eq]
    exact framed.prepared
  obtain ⟨metadata,_,_,bounds,found,finished,_⟩ := prepared
  have equal := Option.some.inj (found.symm.trans framed.located)
  subst bounds
  change GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry
    state.core.erased.current.context assignment plan.packet.site.occurrence _
  change All₂ (GeneralDictionaryRecursiveEvidence.Evidence plan.packet.registry
    state.core.erased.current.context assignment) plan.packet.children dictionaries at children
  rw [← framed.context_eq] at children ⊢
  exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
    (instance_of_total plan assignment holds variables defined scalars framed.visible framed.role_eq
      framed.located finished metadata) children

/-- Recording and current journal Models supply actual total Holds in the very
same assignment used for the children. No existential candidate model is swapped in. -/
theorem evidence_of_recorded (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (framed : GeneralNominalCenteredHeadOutputs.Frame plan.packet.registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (recorded : plan ∈ state.core.plans)
    (assignment : Assignment) (models : GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
    (variables : VariableClauses plan.packet.declaration)
    (defined : GeneralNominalMaterialization.RootDefined plan.packet.declaration plan.packet.site.occurrence)
    (scalars : ScalarRequests plan.packet.registry plan.packet.context
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence))
    (dictionaries : List Dictionary)
    (children : All₂ (fun child dictionary =>
      (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
        child dictionary) plan.packet.children dictionaries) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence plan.packet.registry state assignment
      plan.packet.site.occurrence (.node plan.packet.declaration.id dictionaries) :=
  evidence_of_frame_total plan state framed assignment (models.2.2.2.2.1 plan recorded)
    variables defined scalars dictionaries children


end Yulang.GeneralDictionaryMatScalarOutputs200
