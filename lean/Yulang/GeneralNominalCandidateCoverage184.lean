import Yulang.GeneralNominalGroundCandidateReadback184
import Yulang.GeneralNominalRegisteredCoverage183

/-! Every declared candidate input receives a historical actual head witness
under same registered occurrence/declaration. Witness selection precedes models;
existence of a matching historical plan remains explicit. -/
namespace Yulang.GeneralNominalCandidateCoverage184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (Same)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_head_use
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ plan.headSchema.variables := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 (GeneralNominalQueryProvenance183.registered_finished path plan registered) name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨origin,by simpa only [equal, Plan.headSchema] using used⟩

theorem candidate_input_readback (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (name : Nat) (named : name ∈ candidate.packet.declaration.inputNames) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables ∧
      ∀ model, Models state model → Same model origin (.source (historical.binder name)) := by
  have historicalName : name ∈ historical.packet.declaration.inputNames := declaration ▸ named
  have witnessed : ∃ origin : Origin,
      (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ historical.headSchema.variables := by
    obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
    exact registered_head_use path historical member name historicalName
  obtain ⟨origin,used⟩ := witnessed
  have input := GeneralNominalGroundCandidateReadback184.ground_input_equal checked reachable
    historical candidate member registered same
  have schema := GeneralNominalHeadTransport184.ground_head_schema_eq reachable historical candidate
    member current declaration (congrArg (fun site : Site roles => List.ofFn site.center) input)
  have candidateUse : (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables := by
    rw [schema]
    exact used
  exact ⟨origin,candidateUse,fun model valid =>
    GeneralNominalGroundCandidateReadback184.candidate_actual checked reachable historical candidate
      member registered same current declaration _ candidateUse rfl model valid⟩

theorem candidate_nonpoint_readback (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (name : Nat) (named : name ∈ candidate.packet.declaration.inputNames)
    (input : name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs name).2) :
    ∃ origin : Origin, (⟨name,origin,.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables ∧
      ∀ model, Models state model → Same model origin (.source (candidate.binder name)) := by
  obtain ⟨origin,used,_⟩ := candidate_input_readback checked reachable historical candidate member
    registered same current declaration name named
  exact ⟨origin,used,fun model valid =>
    GeneralNominalGroundCandidateReadback184.candidate_nonpoint_overlap checked reachable historical candidate
      member registered same current declaration _ used rfl input candidateNonpoint historicalNonpoint model valid⟩

end Yulang.GeneralNominalCandidateCoverage184
