import Yulang.GeneralDeclarativeTermCapturedHead322
import Yulang.GeneralDeclarativeSourceCoverage322
import Yulang.GeneralDeclarativeFixedReturn322
import Yulang.GeneralDeclarativeEmissionLocal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOrdinaryProducer322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermCapture322 (Shared KnownNames named)
open GeneralDeclarativeTermCapturedHead322 (ActualSyntax gives_heads)
open GeneralDeclarativeExistingClause322 (Refers)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct Agree)
open GeneralDeclarativeEmissionLocal322 (Data source_batch)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeSourceCoverage322 (ready_from_forms)
open GeneralDeclarativeFixedReturn322 (requested_return)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralNominalCenteredHeadWFSource (Coverage DeclarationCovered)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Registry Declaration Checked)

noncomputable def namesOf (s : State) (seen : List Occurrence) (pool : Nat → List Nat)
    (input : Nat → Capture) : Names :=
  let actual := named s seen pool input
  ⟨actual,fun binder => (actual binder).center⟩

/-- Pure remaining ordinary readbacks, with no compiler rows or per-model
dictionary premise. Direct where binders are not included. -/
structure Residual (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (decl : Declaration) (names : Names) (place : Placement) : Prop where
  bounds : ∀ binder ∈ decl.inputNames, Bounds s (names.input binder)
  argumentBounds : ∀ arg ∈ d.arguments, Bounds s arg
  compound : ∀ clause ∈ decl.requirements, ∀ (i : Nat) pat code,
    clause.arguments[i]? = some pat →
    translate r.constructors interp (normalize pat) = some code →
    Compound pat → Refers s names.input code (place.compound clause i)
  whereOutput : ∀ clause ∈ decl.requirements, ∀ eqn ∈ clause.outputs, ∀ code,
    translate r.constructors interp (normalize eqn.rhs) = some code → ¬Direct decl eqn →
    Derives s (.variable (useOutput decl names (place.targets clause) eqn).target)
      (logical names.input .actual code)
  outputDeclared : ∀ out ∈ d.outputs, ∃ declaration, (r.roles decl.role).assoc out.name = some declaration
  output : ∀ out ∈ d.outputs, ∀ body, Supplies r.roles decl out.name body → ∀ code,
    translate r.constructors interp (normalize (bodyPattern body)) = some code →
    Derives s (.variable out.target) (logical (bodyCapture d names.input body) .actual code)

theorem ordinary_produces {s : State} {p : Supported s completed}
    (checked : Checked r) (metadata : Coverage r interp)
    (declared : decl ∈ r.declarations) (role : decl.role = d.role)
    (observed : ActualSyntax s r interp d decl seen)
    (sameBinder : Shared s seen) (names : KnownNames s seen pool)
    (rest : Residual s r interp d decl (namesOf s seen pool endpoints) place) :
    BatchRecipe s r interp d decl.id (children decl (namesOf s seen pool endpoints) place) := by
  apply source_batch (p := p) checked declared role
  refine ⟨gives_heads observed sameBinder names endpoints,rest.bounds,rest.argumentBounds,
    fun _ _ => rfl,?_,?_⟩
  · intro clause listed
    have covered := (metadata.1 decl declared).2.1 clause listed
    exact ready_from_forms covered.1 covered.2 (rest.compound clause listed) (rest.whereOutput clause listed)
  · intro out requested
    exact requested_return (checked.2 decl declared) (metadata.1 decl declared) metadata.2
      (rest.outputDeclared out requested) (rest.output out requested)

end Yulang.GeneralDeclarativeOrdinaryProducer322
