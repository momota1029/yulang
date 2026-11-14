import Yulang.GeneralNominalHeadCandidateSemantic186
import Yulang.GeneralNominalHeadRootOverlap185

/-! Full-support overlap readback for arbitrary registered candidate sites.
Numeric allocation identity suffices; the demand need not be the initial root. -/
namespace Yulang.GeneralNominalHeadCandidateOverlap186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem candidate_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralNominalHeadLedgerFrame182.fullSources state)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  have allocated := GeneralNominalBinderIdentity181.binder_fresh candidate entry.name input nonpoint
  rw [current] at allocated
  rw [allocated] at overlap
  obtain ⟨historical,member,name,equal⟩ :=
    GeneralNominalHeadFullProducer185.wf_full_producer reachable overlap
  obtain ⟨nameEq,_,identity,decl,_,oldNonpoint⟩ :=
    GeneralNominalHeadBinderIdentity185.registered_binder_identity reachable historical member name equal
  subst name
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    candidate.packet.declaration historical.packet.declaration visible
    (GeneralNominalHeadRootOverlap185.wf_plan_visible reachable historical member) decl.symm
  exact GeneralNominalHeadCandidateSemantic186.candidate_nonpoint_overlap checked reachable
    historical candidate member registered identity.symm current declaration
    entry present actual input nonpoint oldNonpoint model valid


end Yulang.GeneralNominalHeadCandidateOverlap186
