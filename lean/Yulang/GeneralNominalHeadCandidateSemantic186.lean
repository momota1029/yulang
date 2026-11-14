import Yulang.GeneralNominalHeadIdentityCenters186

/-! Current candidate readback through a historical plan at the same numeric
invocation identity. Full occurrence equality and root-only restrictions are
not required. Candidate head equations are not assumed. -/
namespace Yulang.GeneralNominalHeadCandidateSemantic186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Registered semantic centers and recursive schema correspondence recover
historical binder readback for a candidate that has not been installed. -/
theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name)) := by
  have centers := GeneralNominalHeadIdentityCenters186.registered_identity_centers_same
    checked reachable candidate.input historical.input registered
    (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable historical member)
    ((congrArg Occurrence.identity candidate.input_exact).trans
      (identity.trans (congrArg Occurrence.identity historical.input_exact).symm)) model valid
  have config := GeneralNominalHeadReadback185.wf_registered_configuration reachable historical member
  obtain ⟨other,found,nameEq,modeEq,related⟩ :=
    GeneralNominalHeadSchemaSemantic186.head_correspondence candidate historical declaration
      ((congrArg (fun context : GeneralNominalCandidates.Context => context.state.constructors) current).trans config.2.1.symm)
      ((congrArg (fun context : GeneralNominalCandidates.Context => context.interpretation) current).trans config.2.2.symm)
      centers entry present
  have historicalActual : other.mode = .actual := modeEq.symm.trans actual
  have readback := GeneralNominalRegisteredReadback182.registered_actual historical member valid.1
    .head other found historicalActual
  have transported : Same model entry.origin (.source (historical.binder other.name)) :=
    GeneralNominalHeadSchemaSemantic186.related_holds
      (term := .leaf (.source (historical.binder other.name)))
      (GeneralNominalHeadSchemaSemantic186.related_symm related) readback
  simpa only [nameEq] using transported

/-- For nonoutput names with two nonpoint captures, numeric invocation identity
also identifies the allocated binder. No root occurrence premise is used. -/
theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  rw [GeneralNominalHeadReadback185.wf_nonpoint_binder_eq reachable historical candidate member
    current declaration identity entry.name input candidateNonpoint historicalNonpoint]
  exact candidate_actual checked reachable historical candidate member registered identity current declaration
    entry present actual model valid

end Yulang.GeneralNominalHeadCandidateSemantic186
