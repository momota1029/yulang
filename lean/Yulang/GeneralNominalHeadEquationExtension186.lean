import Yulang.GeneralNominalHeadConservativeExtension186
import Yulang.GeneralNominalHeadSchemaNames186

/-! Exact conservative extension for the entire actual head equation bundle.
This stops before output equations, child materialization and dictionaries. -/
namespace Yulang.GeneralNominalHeadEquationExtension186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalRecursiveInspection (Observes Finished)
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Head Same)
open GeneralNominalCenteredModelExtension (originSource)
open CommonNominalFullCarrier
open GeneralNominalRootExtension184 (argument)
open GeneralNominalHeadConservativeExtension186 (support)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def uses (candidate : Plan roles) : Fin candidate.headSchema.variables.length → Use :=
  fun index => candidate.headSchema.variables[index]

theorem uses_mem (candidate : Plan roles) (index : Fin candidate.headSchema.variables.length) :
    uses candidate index ∈ candidate.headSchema.variables := List.getElem_mem ..

theorem uses_cover (candidate : Plan roles) (entry : Use)
    (member : entry ∈ candidate.headSchema.variables) : ∃ index, uses candidate index = entry := by
  obtain ⟨index,bounded,equal⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨index,bounded⟩,equal⟩

def Compatible (candidate : Plan roles) (model : Assignment) : Prop :=
  (∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2) ∧
  (∀ i, ∃ value, Observes model (uses candidate i).origin value) ∧
  (∀ i value, Observes model (uses candidate i).origin value →
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate i).name) value) ∧
  (∀ i j first last, candidate.binder (uses candidate i).name = candidate.binder (uses candidate j).name →
    Observes model (uses candidate i).origin first → Observes model (uses candidate j).origin last →
    Equivalent first last)

theorem tests_frame (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (previous extended : Assignment)
    (kept : ∀ name ∈ support state candidate (uses candidate), extended name = previous name)
    (test) (member : test ∈ candidate.headSchema.tests) :
    Head previous test.1 test.2 ↔ Head extended test.1 test.2 := by
  apply GeneralNominalCenteredFrame179.head_iff
  symm
  exact kept _ (List.mem_append_left _ (GeneralNominalHeadCandidateSupport186.registered_center
    state candidate.input registered ((GeneralNominalHeadCandidateSupport186.head_roots candidate aligned).1 test member)))

theorem head_equations_extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (aligned : candidate.packet.declaration.role = candidate.input.occurrence.demand.role)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection candidate))
    (previous : Assignment) (valid : Models state previous) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = previous name) ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate extended) ↔ Compatible candidate previous := by
  have actual := fun i => GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate i)
  have notOutput := fun i => GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i)
  have extension := GeneralNominalHeadConservativeExtension186.conservative_extension_iff
    checked reachable candidate registered aligned current visible (uses candidate)
    (uses_mem candidate) actual notOutput previous valid
  constructor
  · rintro ⟨extended,models,kept,input,captures,schema⟩
    have arguments : ∀ i, (argument candidate (uses candidate i)).Holds extended := by
      intro i
      refine ⟨captures _ (GeneralNominalHeadSchemaNames186.head_input candidate _ (uses_mem candidate i)),?_⟩
      simpa only [argument,actual i,ite_true] using schema.2 _ (uses_mem candidate i)
    exact ⟨fun test member => (tests_frame candidate registered aligned previous extended kept test member).mpr
      (schema.1 test member),extension.mp ⟨extended,models,kept,arguments⟩⟩
  · rintro ⟨tests,compatible⟩
    obtain ⟨extended,models,kept,arguments⟩ := extension.mpr compatible
    refine ⟨extended,models,kept,models.1.2.1 candidate.input registered,?_,?_,?_⟩
    · intro name named
      obtain ⟨origin,present⟩ := GeneralNominalHeadSchemaSemantic186.input_use candidate finished name named
      obtain ⟨index,equal⟩ := uses_cover candidate ⟨name,origin,.actual⟩ present
      have fits := (arguments index).1
      simpa only [argument,equal,Argument.Holds] using fits
    · intro test member
      exact (tests_frame candidate registered aligned previous extended kept test member).mp (tests test member)
    · intro entry present
      obtain ⟨index,equal⟩ := uses_cover candidate entry present
      have readback := (arguments index).2
      simpa only [argument,equal,GeneralNominalHeadSchemaNames186.head_actual candidate entry present,ite_true] using readback

end Yulang.GeneralNominalHeadEquationExtension186
