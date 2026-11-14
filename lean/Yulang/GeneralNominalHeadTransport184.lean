import Yulang.GeneralNominalRegisteredReadback182
import Yulang.GeneralNominalCenteredGroundBoundary

/-! Historical configurations and structural head-schema transport.
Input center lists are explicitly equal; reachability alone is not claimed to
supply that equality. No semantic origin agreement is assumed by transport. -/
namespace Yulang.GeneralNominalHeadTransport184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- All three configuration components at installation are retained. -/
theorem registered_initial_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans,
      plan.packet.context.state.seed = context.state.seed ∧
      plan.packet.context.state.constructors = context.state.constructors ∧
      plan.packet.context.interpretation = context.interpretation := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus next action => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro previous member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.1.2.1]
        exact GeneralNominalCenteredTrace.configuration_trace path
      · exact ih previous member

theorem registered_current_configuration
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.erased.current.context.interpretation := by
  have prior := registered_initial_configuration path plan member
  have current := GeneralNominalCenteredTrace.configuration_trace path
  exact ⟨prior.1.trans current.1.symm,prior.2.1.trans current.2.1.symm,prior.2.2.trans current.2.2.symm⟩

theorem ground_registered_configuration
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.erased.current.context.interpretation := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registered_current_configuration path plan member

theorem head_schema_eq (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : List.ofFn first.input.center = List.ofFn last.input.center) :
    first.headSchema = last.headSchema := by
  simp only [Plan.headSchema,GeneralNominalInspection.queries,declaration,constructors,interpretation,centers]

theorem registered_head_schema_eq
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema := by
  have configuration := registered_current_configuration path historical member
  exact head_schema_eq candidate historical declaration
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.state.constructors) current).trans
      configuration.2.1.symm)
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.interpretation) current).trans
      configuration.2.2.symm) centers

theorem ground_head_schema_eq
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center) :
    candidate.headSchema = historical.headSchema := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registered_head_schema_eq path historical candidate member current declaration centers

/-- The candidate need not be registered: its origin is read through the
historical schema. The target here is the historical binder, not a new binder. -/
theorem ground_candidate_actual
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name)) := by
  have schemas := ground_head_schema_eq reachable historical candidate member current declaration centers
  rw [schemas] at present
  exact GeneralNominalRegisteredReadback182.registered_actual historical member valid .head entry present actual

theorem ground_candidate_readback
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) (value) (seen : Observes model entry.origin value) :
    CommonNominalFullCarrier.Equivalent value (model (historical.binder entry.name)).1 :=
  (ground_candidate_actual reachable historical candidate member current declaration centers entry present actual model valid).2.2
    value (model (historical.binder entry.name)).1 seen (.source _)

/-- Syntactic binder identity, unlike semantic agreement, is sufficient to
reuse the historical equation for a candidate binder. -/
theorem ground_candidate_overlap
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (binder : candidate.binder entry.name = historical.binder entry.name)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  rw [binder]
  exact ground_candidate_actual reachable historical candidate member current declaration centers entry present actual model valid

theorem nonpoint_binder_eq (first last : Plan roles) (name : Nat)
    (declaration : first.packet.declaration = last.packet.declaration)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (input : name ∉ first.packet.declaration.outputNames)
    (firstNonpoint : ((GeneralNominalPacketSupport.capture first.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture first.packet).inputs name).2)
    (lastNonpoint : ((GeneralNominalPacketSupport.capture last.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture last.packet).inputs name).2) :
    first.binder name = last.binder name := by
  have lastInput : name ∉ last.packet.declaration.outputNames := declaration ▸ input
  simp only [Plan.binder,lastInput,ite_false,firstNonpoint,lastNonpoint,seed,invocation,declaration]

theorem ground_nonpoint_binder_eq
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (invocation : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (name : Nat) (input : name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs name).2) :
    candidate.binder name = historical.binder name := by
  have seed := (ground_registered_configuration reachable historical member).1
  apply nonpoint_binder_eq candidate historical name declaration _ invocation input candidateNonpoint historicalNonpoint
  exact (congrArg (fun context : GeneralNominalCandidates.Context => context.state.seed) current).trans seed.symm

theorem ground_candidate_nonpoint_overlap
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (invocation : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (centers : List.ofFn candidate.input.center = List.ofFn historical.input.center)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) :=
  ground_candidate_overlap reachable historical candidate member current declaration centers entry present actual
    (ground_nonpoint_binder_eq reachable historical candidate member current declaration invocation entry.name
      input candidateNonpoint historicalNonpoint) model valid

end Yulang.GeneralNominalHeadTransport184
