import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputExact323
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputs320 (OutputMeaning bodyCapture bodyPattern compile compile_exact)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeEntailment320 (Holds Entails appendFacts model_append)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact supplies_unique)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralDeclarativeWhere319 (variables)
open GeneralNominalCommonBridge (Assignment)

/-- The actual singleton produced for an existing fixed output target is
equivalent to the declaration's associated output meaning at a fixed
capture. This is independent of the state and of any child judgment. -/
theorem root_exact (checked : Checked r) (visible : decl ∈ r.declarations)
    (emitted : rootFact r interp decl d capture out = some [row]) (m : Assignment) :
    OutputMeaning r.roles r.constructors interp decl d capture m out ↔ Holds m row := by
  have unique := (checked.2 decl visible).identified.2.2.1
  cases supplied : lookup r.roles decl out.name with
  | none => simp [rootFact,supplied] at emitted
  | some body =>
    cases translated : compile r.constructors interp body with
    | none => simp [rootFact,supplied,translated] at emitted
    | some code =>
      have exactRow : (⟨out.target,logical (bodyCapture d capture body) .actual code⟩ : Equation) = row := by
        simpa [rootFact,supplied,translated] using emitted
      subst row
      have origin := (lookup_exact r.roles decl unique out.name body).mp supplied
      have same := compiled_normalized
        (variables := variables (bodyCapture d capture body) m)
        ((compile_exact _ _ body).trans translated)
      simp only [Holds,logical_value]
      constructor
      · rintro ⟨other,found,meaning⟩
        cases supplies_unique r.roles decl unique out.name other body found origin
        exact eqv_trans meaning (eqv_symm same)
      · intro got
        exact ⟨body,origin,eqv_trans got same⟩

theorem all_models_exact (checked : Checked r) (visible : decl ∈ r.declarations)
    (emitted : rootFact r interp decl d capture out = some [row]) :
    (∀ m, Models s m → OutputMeaning r.roles r.constructors interp decl d capture m out) ↔
      Entails s row :=
  ⟨fun all m valid => (root_exact checked visible emitted m).mp (all m valid),
    fun all m valid => (root_exact checked visible emitted m).mpr (all m valid)⟩

/-- Adding that ordinary row restricts the old models to exactly those
which satisfy the actual fixed-target associated equation. -/
theorem append_exact (checked : Checked r) (visible : decl ∈ r.declarations)
    (emitted : rootFact r interp decl d capture out = some [row]) (m : Assignment) :
    Models (appendFacts s [row]) m ↔
      Models s m ∧ OutputMeaning r.roles r.constructors interp decl d capture m out := by
  rw [model_append,root_exact checked visible emitted]
  simp

end Yulang.GeneralDeclarativeOutputExact323
