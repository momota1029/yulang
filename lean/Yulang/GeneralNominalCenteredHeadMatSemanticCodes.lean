import Yulang.GeneralNominalCenteredHeadMatPlanData
import Yulang.GeneralNominalCenteredHeadMatStepFiniteProgress

/-! Finite persistent codes for total packet equations. A representative is
used only to interpret a code; the delta is independent of that representative. -/
namespace Yulang.GeneralNominalCenteredHeadMatSemanticCodes
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalReportErasure
open GeneralNominalCenteredHeadMatStepFiniteProgress (Represents)
open GeneralNominalCenteredHeadMatStepPackets (Inputs Outputs)
variable {roles : Roles.RoleDecls} {plan : Plan roles}

structure Code (roles : Roles.RoleDecls) where
  registry : Registry
  declaration : Declaration
  input : Site roles
  report : Data

def encode (plan : Plan roles) : Code roles :=
  ⟨plan.packet.registry,plan.packet.declaration,plan.input,
    erase plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)⟩

def Config (context : GeneralNominalCandidates.Context) (plan : Plan roles) : Prop :=
  plan.packet.context.state.seed = context.state.seed ∧
    plan.packet.context.state.constructors = context.state.constructors ∧
      plan.packet.context.interpretation = context.interpretation

theorem same (first last : Plan roles) (one : Config context first) (two : Config context last)
    (equal : encode first = encode last) : GeneralNominalCenteredHeadMatPlanData.Same first last :=
  ⟨congrArg Code.registry equal,congrArg Code.declaration equal,congrArg Code.input equal,
    one.1.trans two.1.symm,one.2.1.trans two.2.1.symm,one.2.2.trans two.2.2.symm,
    congrArg Code.report equal⟩

noncomputable def signature (context : GeneralNominalCandidates.Context) (code : Code roles) :
    GeneralNominalSharedBudget.Signature roles := by
  classical
  exact if available : ∃ plan, Config context plan ∧ encode plan = code then
    let plan := Classical.choose available
    ⟨plan.input.occurrence,plan.packet.children,fun model => Inputs plan model ∧ Outputs plan model⟩
  else ⟨code.input.occurrence,[],fun _ => False⟩

theorem encode_represents (configured : Config context plan) : Represents (signature context (encode plan)) plan := by
  classical
  have available : ∃ other, Config context other ∧ encode other = encode plan := ⟨plan,configured,rfl⟩
  unfold signature
  rw [dite_eq_left available]
  let other := Classical.choose available
  have spec : Config context other ∧ encode other = encode plan := Classical.choose_spec available
  have related := same other plan spec.1 configured spec.2
  exact ⟨(congrArg Site.occurrence related.input).trans plan.input_exact,
    GeneralNominalCenteredHeadMatPlanData.children related,GeneralNominalCenteredHeadMatPlanData.delta related⟩

def codes (context : GeneralNominalCandidates.Context) (registry : Registry)
    (sites : List (Site roles)) (sources : List Nat) : List (Code roles) :=
  sites.flatMap fun site => registry.declarations.flatMap fun declaration =>
    (GeneralNominalReportEnumeration.reports sources
      (GeneralNominalInspection.queries context.state context.interpretation declaration)
      (roles site.occurrence.demand.role).arity).map fun report => ⟨registry,declaration,site,report⟩

theorem encode_mem (configured : Config context plan) (registry_eq : plan.packet.registry = registry)
    (recorded : plan.input ∈ sites) (visible : plan.packet.declaration ∈ registry.declarations)
    (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (supported : ∀ slot, plan.packet.context.state.base.source slot ∈ sources) :
    encode plan ∈ codes context registry sites sources := by
  have report := GeneralNominalReportEnumeration.report_enumerated plan.packet.context plan.packet.declaration plan.packet.bounds supported
  have length : plan.packet.bounds.length = (roles plan.input.occurrence.demand.role).arity := by
    have length := GeneralNominalPacketCodes.locate_length plan.packet.context.state.base
      (List.ofFn plan.packet.site.occurrence.demand.arguments) plan.packet.bounds located
    simpa only [List.length_ofFn,plan.input_exact] using length
  have queries : GeneralNominalInspection.queries context.state context.interpretation plan.packet.declaration =
      GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration := by
    simp only [GeneralNominalInspection.queries,configured.2.1,configured.2.2]
  rw [length,← queries] at report
  refine List.mem_flatMap.mpr ⟨plan.input,recorded,List.mem_flatMap.mpr
    ⟨plan.packet.declaration,visible,List.mem_map.mpr ⟨_,report,?_⟩⟩⟩
  simp only [encode,registry_eq]

end Yulang.GeneralNominalCenteredHeadMatSemanticCodes
