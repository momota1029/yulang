import Yulang.GeneralDeclarativeAssocRule323
import Yulang.GeneralDeclarativeRootClosure323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAssocModel323
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeEntailment320 (Holds Entails appendFacts)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputs320 (OutputMeaning bodyCapture bodyPattern)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputSource323 (Declared declared_rows)
open GeneralDeclarativeRootClosure323 (models_close)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDefaultCoverage322 (supplies_covered)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralDictionaryAssociatedProvenance (Supplies supplies_unique declared_covered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translate_complete)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCommonBridge (Assignment)

/-- Exact semantic content of a normalized stated source equation,
including the explicit/default choice fixed by declaration uniqueness. -/
theorem actual_output {r : GeneralDeclarations.Registry} (checked : Checked r)
    (visible : impl ∈ r.declarations) (source : Supplies r.roles impl out.name body)
    (spelling : translate r.constructors interp (normalize (bodyPattern body)) = some e)
    (m : Assignment) :
    Holds m ⟨out.target,logical (bodyCapture d capture body) .actual e⟩ ↔
      OutputMeaning r.roles r.constructors interp impl d capture m out := by
  have equal := translate_value (normalize (bodyPattern body))
    (variables := variables (bodyCapture d capture body) m) spelling
  simp only [Holds,logical_value,equal]
  constructor
  · intro has
    exact ⟨body,source,has⟩
  · rintro ⟨alternative,other,meaning⟩
    have uniq := (checked.2 impl visible).identified.2.2.1
    have same := supplies_unique r.roles impl uniq out.name alternative body other source
    cases same
    exact meaning

/-- The independent source rule and the actual emitter impose exactly
the same restriction on models, without requiring syntactic identity
of their normalized and original-spelling expressions. -/
theorem compiler_models_iff_source {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role)
    (knownRequests : Declared r d)
    (emitted : collect (rootFact r interp impl d capture) d.outputs = some rows)
    (m : Assignment) :
    Models (appendFacts s rows) m ↔ Models s m ∧
      ∀ row, SourceEquation r interp d impl capture row → Holds m row := by
  rw [models_close checked visible (declared_rows checked cover visible role knownRequests) emitted]
  apply and_congr_right
  intro _
  constructor
  · intro outputs row origin
    obtain ⟨out,asked,body,selected,nf,translated,rfl⟩ := origin
    exact (actual_output checked visible selected translated m).mpr (outputs out asked)
  · intro source out there
    have legal := role.symm ▸ knownRequests out there
    obtain ⟨body,provided⟩ := declared_covered r.roles impl (checked.2 impl visible).signature out.name legal
    obtain ⟨nf,normalized⟩ := translate_complete
      (normalize_covered (supplies_covered (cover.1 impl visible) cover.2 provided))
    exact (actual_output checked visible provided normalized m).mp
      (source _ ⟨out,there,body,provided,nf,normalized,rfl⟩)

end Yulang.GeneralDeclarativeAssocModel323
