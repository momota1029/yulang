import Yulang.GeneralDictionaryDefaultRevisit214

/-! Reinspection readback before current Prepared is known. This omits Frame
rather than using readiness circularly; trace metadata supplies configuration.
Numeric invocation equality is retained, not generalized silently to aliases. -/
namespace Yulang.GeneralDictionaryDefaultPreFrame215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalOriginTerms
open GeneralNominalMaterialization (Use)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem candidate_actual (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (valid : Models state model) : Same model entry.origin (.source (historical.binder entry.name)) := by
  have centers := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same
    checked path candidate.input historical.input inputRegistered
    (GeneralDictionaryDefault214ActualSupport.registered_input path historical member)
    ((congrArg Occurrence.identity candidate.input_exact).trans
      (identity.trans (congrArg Occurrence.identity historical.input_exact).symm)) valid
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have config := GeneralDictionaryDefaultConfiguration209.stored built member
  have constructors := ((congrArg (fun c : GeneralNominalCandidates.Context => c.state.constructors) current).trans
    ((GeneralDictionaryDefaultDepth208.configuration_trace path).2.1.trans source.metadata.1.symm)).trans config.2.2.2.symm
  have interpretation := ((congrArg GeneralNominalCandidates.Context.interpretation current).trans
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

theorem candidate_tests (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (test : Origin × Test) (present : test ∈ candidate.headSchema.tests) : Head model test.1 test.2 := by
  have centers := GeneralDictionaryDefaultIdentityCenters214.registered_identity_centers_same
    checked path candidate.input historical.input inputRegistered
    (GeneralDictionaryDefault214ActualSupport.registered_input path historical member)
    ((congrArg Occurrence.identity candidate.input_exact).trans
      (identity.trans (congrArg Occurrence.identity historical.input_exact).symm)) valid
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have config := GeneralDictionaryDefaultConfiguration209.stored built member
  have constructors := ((congrArg (fun c : GeneralNominalCandidates.Context => c.state.constructors) current).trans
    ((GeneralDictionaryDefaultDepth208.configuration_trace path).2.1.trans source.metadata.1.symm)).trans config.2.2.2.symm
  have interpretation := ((congrArg GeneralNominalCandidates.Context.interpretation current).trans
    (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans config.2.2.1.symm
  obtain ⟨other,found,testEq,related⟩ := GeneralNominalHeadTestSemantic186.head_tests candidate historical declaration
    constructors interpretation centers test present
  rw [testEq]
  exact GeneralNominalHeadTestSemantic186.related_head (GeneralNominalHeadSchemaSemantic186.related_symm related)
    ((GeneralNominalCenteredHeadMatStepPackets.head_equations (valid.2.2.2.2.1 historical member)).2.2.1 other found)


end Yulang.GeneralDictionaryDefaultPreFrame215
