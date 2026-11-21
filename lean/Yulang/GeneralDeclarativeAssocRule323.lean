import Yulang.GeneralDeclarativeStableRigid323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAssocRule323
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (Entails Holds literal)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture compile compile_exact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeRigidLocal323 (RootClosed)
open GeneralDeclarativeRigidLocal323 (RigidReads)
open GeneralDeclarativeStableRigid323 (Closed Rule stable_sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translate_complete)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDeclarativeDefaultCoverage322 (supplies_covered)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalInspection (Interpretation)

/-- Ordinary source equation from spec 6.3: use the parsed associated body
and the original requested name. It contains neither the batch compiler
nor any kind of selection or evidence predicate. -/
def SourceEquation (r : Registry) (interp : Interpretation) (d : Demand)
    (impl : Declaration) (capture : Nat → Capture) (row : Equation) : Prop :=
  ∃ out ∈ d.outputs, ∃ body, Supplies r.roles impl out.name body ∧
    ∃ nf, translate r.constructors interp (normalize (bodyPattern body)) = some nf ∧
      row = ⟨out.target,logical (bodyCapture d capture body) .actual nf⟩

theorem compiler_is_ordinary {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations) (request : out ∈ d.outputs)
    (built : rootFact r interp impl d capture out = some [row])
    (applied : ∀ sourceRow, SourceEquation r interp d impl capture sourceRow → Entails s sourceRow) :
    Entails s row := by
  have unique := (checked.2 impl visible).identified.2.2.1
  cases found : lookup r.roles impl out.name with
  | none => simp [rootFact,found] at built
  | some body =>
    cases raw : compile r.constructors interp body with
    | none => simp [rootFact,found,raw] at built
    | some e =>
      have belongs : (⟨out.target,logical (bodyCapture d capture body) .actual e⟩ : Equation) = row := by
        simpa [rootFact,found,raw] using built
      subst row
      have sourceBody := (lookup_exact r.roles impl unique out.name body).mp found
      obtain ⟨normalized,translated⟩ := translate_complete
        (normalize_covered (supplies_covered (cover.1 impl visible) cover.2 sourceBody))
      intro m valid
      have rowWritten := applied _ ⟨out,request,body,sourceBody,normalized,translated,rfl⟩ m valid
      have compares := compiled_normalized (variables := variables (bodyCapture d capture body) m)
        ((compile_exact r.constructors interp body).trans raw)
      rw [← translate_value (normalize (bodyPattern body)) translated] at compares
      simp only [Holds,logical_value] at rowWritten ⊢
      exact eqv_trans rowWritten (eqv_symm compares)

/-- Stable ordinary output closure is supplied by the independently
specified associated rule, not by assuming that the compiler is correct
or retrospectively changing which declaration was selected. -/
theorem from_source_closure {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations)
    (ordinary : ∀ row, SourceEquation r interp d impl capture row → row ∈ s.equations) :
    RootClosed s r interp d impl capture := by
  intro out requested row emitted
  exact compiler_is_ordinary checked cover visible requested emitted (fun e was => literal (ordinary e was))

end Yulang.GeneralDeclarativeAssocRule323
