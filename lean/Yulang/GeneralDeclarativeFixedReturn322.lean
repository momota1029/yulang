import Yulang.GeneralDeclarativeDefaultCoverage322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFixedReturn322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeExistingReturn322 (Settled)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern positional_exact)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDefaultCoverage322 (return_from_body)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDictionaryAssociatedProvenance (Body Supplies declared_covered)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered DefaultsCovered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Registry Declaration DeclarationChecked)

/-- A simple associated RHS can be established by the existing type name
itself or an ordinary equality to it. No new assignment is chosen. -/
theorem read_simple_body {s : State} {r : Registry}
    (source : Supplies r.roles decl out.name body)
    (spelling : bodyPattern body = .var binder)
    (stable : Derives s (.variable out.target) (.variable ((bodyCapture d capture body) binder).center)) :
    Settled s r interp decl d capture out := by
  refine ⟨body,.variable binder,.variable binder,source,?_,?_,stable⟩
  · rw [spelling]; rfl
  · rw [spelling]; rfl

theorem supplied_center {s : State} {r : Registry}
    (source : Supplies r.roles decl out.name body)
    (spelling : bodyPattern body = .var binder)
    (identity : out.target = ((bodyCapture d capture body) binder).center) :
    Settled s r interp decl d capture out :=
  read_simple_body source spelling (identity.symm ▸ Derives.refl _)

theorem positional_default_alias {s : State} {r : Registry} {arg : Capture}
    (source : Supplies r.roles decl out.name (.default role key (.var index)))
    (there : d.arguments[index]? = some arg)
    (linked : Derives s (.variable out.target) (.variable arg.center)) :
    Settled s r interp decl d capture out := by
  apply read_simple_body source (binder := index) rfl
  change Derives s (.variable out.target) (.variable (GeneralDeclarativeOutputs320.positional d index).center)
  rw [positional_exact d there]
  exact linked

/-- The checked role supplies one actual explicit/default body. Its source
coverage discharges syntax/lookup requirements, so the only missing fact
is the normalized equation at the existing requested target. -/
theorem requested_return {s : State} {r : Registry}
    (checked : DeclarationChecked r.constructors r.roles decl)
    (metadata : DeclarationCovered r.constructors interp decl)
    (defaults : DefaultsCovered r.constructors interp r.roles)
    (declared : ∃ val, (r.roles decl.role).assoc out.name = some val)
    (ordinary : ∀ body, Supplies r.roles decl out.name body → ∀ code,
      translate r.constructors interp (normalize (bodyPattern body)) = some code →
      Derives s (.variable out.target) (logical (bodyCapture d capture body) .actual code)) :
    Settled s r interp decl d capture out := by
  obtain ⟨body,known⟩ := declared_covered r.roles decl checked.signature out.name declared
  exact return_from_body metadata defaults known (ordinary body known)

end Yulang.GeneralDeclarativeFixedReturn322
