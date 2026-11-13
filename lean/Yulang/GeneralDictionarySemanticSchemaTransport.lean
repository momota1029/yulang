import Yulang.GeneralDictionaryCaptureMultiplicity
import Yulang.GeneralDictionaryCapturedSchemaTransport

/-! Semantic replacement for the source-ID footprint in schema replay.
The finite footprint uses endpoint equivalence and retained capture origins;
no literal binding equality or descriptor-preserving refinement is required.
Current schema tests/variables must still be among the historical ones. -/
namespace Yulang.GeneralDictionarySemanticSchemaTransport
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

structure Footprint (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State}
    (oldReport : Report oldState) (currentReport : Report currentState) (schema : Schema)
    (model : GeneralNominalCommonBridge.Assignment) : Prop where
  outputs : ∀ entry ∈ schema.variables, entry.name ∈ declaration.outputNames →
    Equivalent (model (currentCapture.outputs entry.name)).1 (model (oldCapture.outputs entry.name)).1
  inputs : ∀ entry ∈ schema.variables, entry.name ∉ declaration.outputNames →
    Equivalent (model (currentCapture.inputs entry.name).1).1 (model (oldCapture.inputs entry.name).1).1 ∧
    Equivalent (model (currentCapture.inputs entry.name).2).1 (model (oldCapture.inputs entry.name).2).1
  origins : ∀ entry ∈ schema.variables, ∀ captured ∈ currentReport.captures,
    entry.name = captured.name → entry.mode = .actual → ∀ origin, captured.origin = some origin →
    ∃ old ∈ oldReport.captures, old.name = captured.name ∧ old.origin = some origin

theorem equivalent_right (a b c : Ty) (same : Equivalent b c) :
    Equivalent a b ↔ Equivalent a c := by
  constructor
  · intro h; exact ⟨subtype_trans h.1 same.1,subtype_trans same.2 h.2⟩
  · intro h; exact ⟨subtype_trans h.1 same.2,subtype_trans same.1 h.2⟩

theorem fits_endpoints (model : GeneralNominalCommonBridge.Assignment)
    (a b : GeneralSourceState.Interval) (actual : Ty)
    (lo : Equivalent (model a.1).1 (model b.1).1)
    (hi : Equivalent (model a.2).1 (model b.2).1) :
    GeneralNominalCaptureMerges.Fits model a actual ↔ GeneralNominalCaptureMerges.Fits model b actual := by
  constructor
  · intro h; exact ⟨subtype_trans lo.2 h.1,subtype_trans h.2 hi.1⟩
  · intro h; exact ⟨subtype_trans lo.1 h.1,subtype_trans h.2 hi.2⟩

theorem variable_meaning (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (schema : Schema)
    (model : GeneralNominalCommonBridge.Assignment)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport schema model)
    (entry : Use) (member : entry ∈ schema.variables) (actual : Ty) :
    VariableHolds declaration currentCapture model entry.name entry.mode actual ↔
      VariableHolds declaration oldCapture model entry.name entry.mode actual := by
  unfold VariableHolds
  by_cases output : entry.name ∈ declaration.outputNames
  · simp only [output,ite_true]
    exact equivalent_right _ _ _ (footprint.outputs entry member output)
  · simp only [output,ite_false]
    have ends := footprint.inputs entry member output
    cases entry.mode with
    | lower => exact equivalent_right _ _ _ ends.1
    | upper => exact equivalent_right _ _ _ ends.2
    | actual => exact fits_endpoints model _ _ _ ends.1 ends.2

/-- Conditional soundness bridge for actual schema bodies. Capture-source
identities may differ, and capture multiplicity may decrease. This does not
assert that every reobserve satisfies the finite semantic footprint. -/
theorem replay (declaration : Declaration) (oldCapture currentCapture : GeneralDeclarationDemands.Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (small large : Schema)
    (variables : ∀ entry ∈ small.variables, entry ∈ large.variables)
    (tests : ∀ test ∈ small.tests, test ∈ large.tests)
    (model : GeneralNominalCommonBridge.Assignment)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport small model)
    (valid : GeneralNominalMaterialization.Models oldState declaration oldCapture oldReport large model) :
    GeneralNominalMaterialization.Models currentState declaration currentCapture currentReport small model := by
  refine ⟨fun test member => valid.1 test (tests test member),?_,?_,?_⟩
  · intro entry member
    refine ⟨(valid.2.1 entry (variables entry member)).1,?_⟩
    intro actual seen
    exact (variable_meaning declaration oldCapture currentCapture oldReport currentReport small
      model footprint entry member actual).mpr ((valid.2.1 entry (variables entry member)).2 actual seen)
  · intro first one last two same firstActual lastActual a b oneSeen twoSeen
    exact valid.2.2.1 first (variables first one) last (variables last two) same firstActual lastActual a b oneSeen twoSeen
  · intro entry member captured present same actual origin known a b seen observed
    obtain ⟨old,oldMember,names,oldOrigin⟩ := footprint.origins entry member captured present same actual origin known
    exact valid.2.2.2 entry (variables entry member) old oldMember (same.trans names.symm) actual
      origin oldOrigin a b seen observed
end Yulang.GeneralDictionarySemanticSchemaTransport
