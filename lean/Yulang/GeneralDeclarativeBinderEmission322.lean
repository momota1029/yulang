import Yulang.GeneralDeclarativeSourceCoverage322
import Yulang.GeneralDeclarativeEmissionLocal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeBinderEmission322
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)
open GeneralDeclarativeSourceCoverage322 (ready_from_forms)
open GeneralDeclarativeEmissionLocal322 (Data Generates)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOutputs322 (Direct Agree)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeExistingLocal322 (Heads)
open GeneralDeclarativeExistingReturn322 (Settled)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (normalize)

def BinderOnly (decl : Declaration) : Prop :=
  ∀ clause ∈ decl.requirements,
    (∀ pat ∈ clause.arguments, ∃ name, normalize pat = .var name) ∧
    (∀ eqn ∈ clause.outputs, Direct decl eqn)

/-- For every source declaration in the binder-only where fragment, no
lookup, naming proof or body lookup is needed in its where clauses.
The actual head and the parent's *own* fixed output equation still have
their independent proof obligations. -/
theorem from_binders {s : State} {p : Supported s completed}
    (syntaxCovered : DeclarationCovered r.constructors interp decl)
    (simple : BinderOnly decl) (agrees : Agree decl names)
    (head : Heads s p r interp d decl names.input)
    (binds : ∀ n ∈ decl.inputNames, Bounds s (names.input n))
    (ranges : ∀ arg ∈ d.arguments, Bounds s arg)
    (outputs : ∀ out ∈ d.outputs, Settled s r interp decl d names.input out) :
    Data s p r interp d decl names place := by
  refine ⟨head,binds,ranges,agrees,?_,outputs⟩
  intro clause listed
  obtain ⟨pats,results⟩ := syntaxCovered.2.1 clause listed
  apply ready_from_forms pats results
  · intro i pat code atIndex _ notBinder
    obtain ⟨name,raw⟩ := (simple clause listed).1 pat (List.mem_of_getElem? atIndex)
    exact False.elim (notBinder name raw)
  · intro eqn listedEq code _ notDirect
    exact False.elim (notDirect ((simple clause listed).2 eqn listedEq))

theorem generates_from_binders {s : State} {p : Supported s completed}
    (syntaxCovered : DeclarationCovered r.constructors interp decl)
    (simple : BinderOnly decl) (agrees : Agree decl names)
    (head : Heads s p r interp d decl names.input)
    (binds : ∀ n ∈ decl.inputNames, Bounds s (names.input n))
    (ranges : ∀ arg ∈ d.arguments, Bounds s arg)
    (outputs : ∀ out ∈ d.outputs, Settled s r interp decl d names.input out) :
    Generates s p r interp d decl (children decl names place) :=
  ⟨names,place,rfl,from_binders syntaxCovered simple agrees head binds ranges outputs⟩

end Yulang.GeneralDeclarativeBinderEmission322
