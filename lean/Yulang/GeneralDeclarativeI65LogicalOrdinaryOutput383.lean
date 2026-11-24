import Yulang.GeneralDeclarativeI65CompletionRead383
import Yulang.GeneralDeclarativeAssocRule323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeOutputs320 (bodyPattern bodyCapture)
open GeneralDeclarativeSubstitution320 (logical)

/-- SourceEquation323 at a particular literal requested occurrence.
It evaluates the same declared associated body, not a compiler batch
receipt or an inferred identity of source events from equal targets. -/
def OrdinarySourceEquationAt383 (r : Registry) (i : Interpretation) (d : Demand)
    (decl : Declaration) (capture : Nat → Capture) (ordinal : Nat) (row : Equation) : Prop :=
  ∃ out, d.outputs[ordinal]? = some out ∧
    ∃ body, Supplies r.roles decl out.name body ∧
      ∃ nf, translate r.constructors i (normalize (bodyPattern body)) = some nf ∧
        row = ⟨out.target,logical (bodyCapture d capture body) .actual nf⟩

theorem logical_ordinary_equation_iff_literal_output383
    {r : Registry} {i : Interpretation} {d : Demand} {decl : Declaration}
    {capture : Nat → Capture} {row : Equation} :
    SourceEquation r i d decl capture row ↔
      ∃ ordinal, OrdinarySourceEquationAt383 r i d decl capture ordinal row := by
  constructor
  · rintro ⟨out,seen,body,defined,nf,lowered,eq⟩
    obtain ⟨ordinal,literal⟩ := List.getElem?_of_mem seen
    exact ⟨ordinal,out,literal,body,defined,nf,lowered,eq⟩
  · rintro ⟨_,out,literal,body,defined,nf,lowered,eq⟩
    exact ⟨out,List.mem_of_getElem? literal,body,defined,nf,lowered,eq⟩

/-- The actual independently selected declaration and its logical
bindings are an explicit source judgment, not determined from a bare
dictionary key. That judgment still has to be supplied by S01/S02. -/
abbrev ChosenOrdinaryBinding383 :=
  State → Request → Dictionary → Declaration → (Nat → Capture) → Prop

def LogicalOrdinaryOutput383 (chosen : ChosenOrdinaryBinding383) : LogicalOutputEquation383 :=
  fun s q d ordinal row =>
    ∃ decl capture, chosen s q d decl capture ∧
      OrdinarySourceEquationAt383 (authoredRegistry s.current)
        (interpretation s.current.environment.source.snapshot) q.demand decl capture ordinal row

/-- A concrete ordinary producing equation, actual selected bindings,
and a finite proof for the very same request yield the declared read.
Merely mentioning its fixed target is not enough. No author stamp,
active version, solver gate, checker result, or model occurs. -/
theorem completed_ordinary_source_reaches_literal_read383
    {rules : SelectedSourceRule383} {direct : DirectEquation383} {chosen : ChosenOrdinaryBinding383}
    {s : State} {q : Request} {d : Dictionary} {decl : Declaration}
    {capture : Nat → Capture} {row : Equation}
    (proof : SelectedSourceProof383 rules s q d)
    (sourceSelected : chosen s q d decl capture)
    (eqn : SourceEquation (authoredRegistry s.current)
      (interpretation s.current.environment.source.snapshot) q.demand decl capture row)
    (retained : row ∈ s.current.ordinary.equations) :
    ∃ ordinal,
      Nonempty (LogicalOutputLink383 (LogicalOrdinaryOutput383 chosen) s q d ordinal row) ∧
      Nonempty (SourceEquationRead383 rules direct (LogicalOrdinaryOutput383 chosen) s row) := by
  obtain ⟨ordinal,exact⟩ := logical_ordinary_equation_iff_literal_output383.mp eqn
  have each := exact
  obtain ⟨out,position,_,_,_,_,rowExact⟩ := each
  have target : row.left = out.target := congrArg Equation.left rowExact
  let linked : LogicalOutputLink383 (LogicalOrdinaryOutput383 chosen) s q d ordinal row :=
    ⟨out,position,target,⟨decl,capture,sourceSelected,exact⟩⟩
  exact ⟨ordinal,⟨linked⟩,⟨.output q d ordinal proof linked retained⟩⟩

end Yulang.GeneralDeclarativeI65
