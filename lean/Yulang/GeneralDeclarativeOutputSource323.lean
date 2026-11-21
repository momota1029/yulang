import Yulang.GeneralDeclarativeRootClosure323
import Yulang.GeneralDeclarativeDefaultCoverage322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputSource323
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeRootClosure323 (DeclaredRows collected)
open GeneralDeclarativeOutputs320 (compile bodyPattern bodyCapture compile_exact)
open GeneralDeclarativeDefaultCoverage322 (supplies_covered)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeBatch320 (collect)
open GeneralDictionaryAssociatedProvenance (declared_covered lookup_exact)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (translate_complete)

def Declared (r : GeneralDeclarations.Registry) (d : GeneralDeclarativeDemand320.Demand) : Prop :=
  ∀ out ∈ d.outputs, ∃ rhs, (r.roles d.role).assoc out.name = some rhs

/-- Request names were checked at source, while the body comes from the
selected declaration. This produces actual rows, including defaults,
without knowing whether they already hold or choosing other targets. -/
theorem declared_rows (checked : Checked r) (coverage : Coverage r interp)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (requests : Declared r d) : DeclaredRows r interp decl d capture := by
  intro out asked
  have declared := role.symm ▸ requests out asked
  have valid := checked.2 decl visible
  obtain ⟨body,supply⟩ := declared_covered r.roles decl valid.signature out.name declared
  have take := (lookup_exact r.roles decl valid.identified.2.2.1 out.name body).mpr supply
  obtain ⟨code,spelling⟩ := translate_complete (supplies_covered (coverage.1 decl visible) coverage.2 supply)
  have compiled := (compile_exact r.constructors interp body).symm.trans spelling
  exact ⟨⟨out.target,logical (bodyCapture d capture body) .actual code⟩,
    by simp [rootFact,take,compiled]⟩

theorem generated (checked : Checked r) (coverage : Coverage r interp)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (requests : Declared r d) :
    ∃ rows, collect (rootFact r interp decl d capture) d.outputs = some rows :=
  collected (declared_rows checked coverage visible role requests)

end Yulang.GeneralDeclarativeOutputSource323
