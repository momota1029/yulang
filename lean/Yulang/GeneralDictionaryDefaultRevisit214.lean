import Yulang.GeneralNominalHeadTestSemantic186
import Yulang.GeneralDictionaryDefaultBinderCollisions214
import Yulang.GeneralDictionaryDefaultHeadEquationExtension214

/-! Corrected replay recovers tests, actual inhabitation and collision coherence.
Only current capture bounds remain; these are not asserted from selection. -/
namespace Yulang.GeneralDictionaryDefaultRevisit214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralNominalRecursiveInspection (Observes Origin Test)
open GeneralNominalOriginTerms (Head)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses uses_mem Compatible)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem candidate_tests (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (test : Origin × Test) (present : test ∈ candidate.headSchema.tests) : Head model test.1 test.2 := by
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
  obtain ⟨other,found,testEq,related⟩ := GeneralNominalHeadTestSemantic186.head_tests candidate historical declaration
    constructors interpretation centers test present
  rw [testEq]
  exact GeneralNominalHeadTestSemantic186.related_head (GeneralNominalHeadSchemaSemantic186.related_symm related)
    ((GeneralNominalCenteredHeadMatStepPackets.head_equations (valid.2.2.2.2.1 historical member)).2.2.1 other found)


def BoundsFit (candidate : Plan roles) (model : Assignment) : Prop :=
  ∀ index value, Observes model (uses candidate index).origin value →
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate index).name) value

theorem compatible_iff_bounds (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    Compatible candidate model ↔ BoundsFit candidate model := by
  constructor
  · exact fun compatible => compatible.2.2.1
  · intro bounds
    refine ⟨?_,?_,bounds,?_⟩
    · exact candidate_tests checked path historical candidate
        member frame identity declaration model valid
    · intro index
      exact (GeneralDictionaryDefaultCandidateActual214.candidate_actual checked path historical candidate
        member frame identity declaration (uses candidate index) (uses_mem candidate index)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate index)) valid).1
    · intro i j first last same one two
      exact GeneralDictionaryDefaultBinderCollisions214.historical_coherence checked source bound path historical candidate
        member frame identity declaration (uses candidate i) (uses candidate j)
        (uses_mem candidate i) (uses_mem candidate j)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate j))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate j))
        model valid first last one two (bounds i first one) (bounds j last two) same

theorem frame_finished {state : State roles} {candidate : Plan roles} (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate) :
    GeneralNominalRecursiveInspection.Finished (GeneralNominalQueryProvenance183.headInspection candidate) := by
  have prepared := frame.prepared
  rw [← frame.context_eq] at prepared
  obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
  have equal : bounds = candidate.packet.bounds := Option.some.inj (found.symm.trans frame.located)
  subst bounds
  exact GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _ candidate.packet.bounds _ _ 0 0 finished

theorem revisit_extension_iff_bounds (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ GeneralDictionaryDefaultConservative214.support state candidate (uses candidate), extended name = model name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended) ↔ BoundsFit candidate model := by
  rw [GeneralDictionaryDefaultHeadEquationExtension214.head_equations_extension_iff checked source bound path
    candidate frame (frame_finished frame) model valid]
  exact compatible_iff_bounds checked source bound path historical candidate member frame identity declaration model valid

end Yulang.GeneralDictionaryDefaultRevisit214
