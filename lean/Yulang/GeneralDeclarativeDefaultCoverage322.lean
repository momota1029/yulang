import Yulang.GeneralDeclarativeNormalizeCovered322
import Yulang.GeneralDeclarativeExistingReturn322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeDefaultCoverage322
open GeneralNominalCenteredHeadWFSource (TermCovered TermsCovered PatternCovered PatternsCovered DeclarationCovered DefaultsCovered)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translate_complete)
open GeneralDeclarativeOutputs320 (termPattern termPatterns bodyPattern bodyCapture)
open GeneralDeclarativeExistingReturn322 (Settled)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeHead320 (State)
open GeneralDictionaryAssociatedProvenance (Body Supplies declared_covered)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (DeclarationChecked)

theorem pattern_length (rhs : List Roles.Term) : (termPatterns rhs).length = rhs.length := by
  induction rhs with
  | nil => rfl
  | cons a b ih => simp [termPatterns,ih]

mutual
 theorem default_pattern {c interp} (term : Roles.Term) (covered : TermCovered c interp term) :
    PatternCovered c interp (termPattern term) := by
  cases term with
  | var => trivial
  | app name args =>
    refine ⟨?_,default_patterns args covered.2⟩
    simpa only [pattern_length] using covered.1
 termination_by sizeOf term
 theorem default_patterns {c interp} (terms : List Roles.Term) (covered : TermsCovered c interp terms) :
    PatternsCovered c interp (termPatterns terms) := by
  cases terms with
  | nil => trivial
  | cons head tail => exact ⟨default_pattern head covered.1,default_patterns tail covered.2⟩
 termination_by sizeOf terms
end

theorem supplies_covered {r : GeneralDeclarations.Registry} (declared : DeclarationCovered r.constructors interp impl)
    (defaults : DefaultsCovered r.constructors interp r.roles)
    (source : Supplies r.roles impl name body) :
    PatternCovered r.constructors interp (bodyPattern body) := by
  cases source with
  | explicit eq present named => exact declared.2.2 eq present
  | default rhs absent present => exact default_pattern rhs (defaults _ _ _ present)

/-- Explicit-over-default selection comes from the declared source body.
Both spellings compile; the only remaining fact is the actual fixed target
equation, not a second choice of implementation or a different target. -/
theorem return_from_body {s : State}
    (declared : DeclarationCovered r.constructors interp impl)
    (defaults : DefaultsCovered r.constructors interp r.roles)
    (source : Supplies r.roles impl out.name body)
    (ordinary : ∀ norm, translate r.constructors interp (normalize (bodyPattern body)) = some norm →
      Derives s (.variable out.target) (logical (bodyCapture d capture body) .actual norm)) :
    Settled s r interp impl d capture out := by
  have cover := supplies_covered declared defaults source
  obtain ⟨orig,first⟩ := translate_complete cover
  obtain ⟨norm,second⟩ := translate_complete (normalize_covered cover)
  exact ⟨body,orig,norm,source,first,second,ordinary norm second⟩

end Yulang.GeneralDeclarativeDefaultCoverage322
