import Yulang.GeneralDeclarativeI65ExactSupportReads384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)

/-- The actual ordinary associated source equation supplies a local
premise and its matching finite proof. The output position is recovered
from the literal source equation, not from equality of retained targets. -/
theorem ordinary_source_produces_exact_need384
    {source tagged chosen s q d decl capture row}
    (selected : ExactSelected384 source (LogicalOrdinaryOutput383 chosen) tagged s q d)
    (binding : chosen s q d decl capture)
    (eqn : SourceEquation (authoredRegistry s.current)
      (interpretation s.current.environment.source.snapshot) q.demand decl capture row)
    (retained : row ∈ s.current.ordinary.equations) :
    ∃ ordinal, Nonempty
      (ExactSupport384 source (LogicalOrdinaryOutput383 chosen) tagged s (.ordinary q d ordinal row)) := by
  obtain ⟨ordinal,body⟩ := logical_ordinary_equation_iff_literal_output383.mp eqn
  have printed := body
  obtain ⟨out,atOutput,_,_,_,_,rowEq⟩ := printed
  exact ⟨ordinal,⟨⟨.ordinary
    ⟨out,atOutput,congrArg Equation.left rowEq,⟨decl,capture,binding,body⟩⟩ retained,selected⟩⟩⟩

theorem tagged_source_produces_exact_need384
    {source ordinary chosen s q d decl capture ordinal row}
    (selected : ExactSelected384 source ordinary chosen s q d)
    (binding : chosen s q d decl capture)
    (body : TaggedUnarySourceAt383 s q decl capture ordinal row)
    (retained : row ∈ s.current.visible) :
    Nonempty (ExactSupport384 source ordinary chosen s (.tagged q d ordinal row)) :=
  ⟨⟨.tagged ⟨decl,capture,binding,body⟩ retained,selected⟩⟩

theorem ordinary_exact_support_requires_original_target384
    {source ordinary tagged s q d i row out}
    (exactRead : ExactSupport384 source ordinary tagged s (.ordinary q d i row))
    (position : q.demand.outputs[i]? = some out) :
    row.left = out.target := by
  obtain ⟨_,⟨linked⟩,_⟩ := ordinary_exact_support_details384 exactRead
  have same := Option.some.inj (position.symm.trans linked.actual)
  simpa [same] using linked.target

theorem tagged_exact_support_requires_original_target384
    {source ordinary tagged s q d i row out}
    (exactRead : ExactSupport384 source ordinary tagged s (.tagged q d i row))
    (position : q.demand.outputs[i]? = some out) :
    row.place = out.target := by
  obtain ⟨_,linked,_⟩ := tagged_exact_support_details384 exactRead
  obtain ⟨_,_,_,actual,atIndex,_,_,_,_,_,_,_,_,rowEq⟩ := linked
  have same := Option.some.inj (position.symm.trans atIndex)
  have target := congrArg AuthoredNominal.place rowEq
  simpa [same] using target

end Yulang.GeneralDeclarativeI65
