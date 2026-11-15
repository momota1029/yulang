import Yulang.GeneralDictionaryDefaultIdentityCenters214
import Yulang.GeneralDictionaryDefaultFreshActual214

/-! Current head actual-origin readback through arbitrary historical center
changes in corrected traces. Only numeric invocation/declaration identity is
needed; current candidate head equations are not assumed. -/
namespace Yulang.GeneralDictionaryDefaultCandidateActual214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalOriginTerms
open GeneralNominalMaterialization (Use)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem candidate_actual (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (valid : Models state model) : Same model entry.origin (.source (historical.binder entry.name)) := by
  have centers := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same
    checked path candidate.input historical.input frame.center_recorded
    (GeneralDictionaryDefault214ActualSupport.registered_input path historical member)
    ((congrArg Occurrence.identity candidate.input_exact).trans
      (identity.trans (congrArg Occurrence.identity historical.input_exact).symm)) valid
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have config := GeneralDictionaryDefaultConfiguration209.stored built member
  have constructors := (GeneralDictionaryDefaultConfiguration209.frame_constructors frame).trans config.2.2.2.symm
  have interpretation := ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
    (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans config.2.2.1.symm
  obtain ⟨other,found,nameEq,modeEq,related⟩ := GeneralNominalHeadSchemaSemantic186.head_correspondence
    candidate historical declaration constructors interpretation centers entry present
  have historicalActual : other.mode = .actual := modeEq.symm.trans actual
  have readback := GeneralDictionaryDefault214ActualReadback.actual_same valid
    (show GeneralDictionaryDefault214ActualReadback.Actual state (historical.binder other.name) other.origin from
      ⟨historical,member,other,found,historicalActual,rfl,rfl⟩)
  have transported : Same model entry.origin (.source (historical.binder other.name)) :=
    GeneralNominalHeadSchemaSemantic186.related_holds
      (term := .leaf (.source (historical.binder other.name)))
      (GeneralNominalHeadSchemaSemantic186.related_symm related) readback
  simpa only [nameEq] using transported

/-- Once both captures use the purpose-eight namespace, identical numeric
origins also identify the binder. Reports and point/nonpoint values otherwise
need not coincide. -/
theorem candidate_nonpoint (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (notOutput : entry.name ∉ candidate.packet.declaration.outputNames)
    (currentNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (oldNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (valid : Models state model) : Same model entry.origin (.source (candidate.binder entry.name)) := by
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have seed := ((congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
    (GeneralDictionaryDefaultConfiguration209.seed built)).trans
      (GeneralDictionaryDefault214ActualSites.plan_seed path historical member).symm
  have binder := (GeneralNominalBinderIdentity181.binder_collision_iff candidate historical entry.name entry.name
    seed notOutput (declaration ▸ notOutput) currentNonpoint oldNonpoint).mpr
      ⟨identity,congrArg Declaration.id declaration,rfl⟩
  rw [binder]
  exact candidate_actual checked path historical candidate member frame identity declaration entry present actual valid
end Yulang.GeneralDictionaryDefaultCandidateActual214
