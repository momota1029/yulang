import Yulang.GeneralDeclarativeI65I73RuleUnionNormal407
import Yulang.GeneralDeclarativeI65I72CompletedNativeSourceIndex406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Summarizes Tree)

/-- Merely changing the set of primitive rules cannot express the
positive completed-lower native case when the current fixed Event
carrier has no authored lower. This is quantified over *every*
SourcePrimitives family, not an accident of the R0 choice. -/
theorem no_rule_sum_can_replace_the_fixed_old_source_head407 {s q row need}
    (gate : CompletedUnaryGate406 s q row need)
    (noLower : ∀ o : Origin, o ∈ s.core.origins → ¬ OriginRoute s.core o gate.arg.lower)
    (R : SourcePrimitives) :
    ∀ d, ¬ Classifies R s q (.selected d) := by
  intro d classified
  obtain ⟨t,_,⟨trace⟩,summary⟩ := classified
  cases trace with
  | rootK2 => cases summary
  | other kind => cases kind <;> cases summary
  | selected event _ _ _ _ =>
    have position := event.frame.inScope
    rw [gate.only] at position
    have same := List.mem_singleton.mp position
    exact completed_unary_gate_is_not_an_old_source_head406 gate noLower ⟨same ▸ event.head⟩

/-- Honest C entry: the checked richer source gives an actual positive
judgment at these exact indices, while no fixed C402 primitive rule
can have the corresponding selected branch in this state. It does
not say that the language should refuse that branch. -/
theorem completed_lower_is_C_not_fixed_I73_scope407 {s q trees d}
    (event : CompletedInvocation406 s q trees)
    (done : Summarizes (.selected event.row.id trees) (.selected d))
    (noLower : ∀ o : Origin, o ∈ s.core.origins → ¬OriginRoute s.core o event.chosen.gate.arg.lower) :
    ScopedClassifies406 s q (.selected d) ∧ ¬Classifies R0 s q (.selected d) :=
  ⟨completed_invocation_gives_source_verdict406 event done,
    no_rule_sum_can_replace_the_fixed_old_source_head407 event.chosen.gate noLower R0 d⟩

end Yulang.GeneralDeclarativeI65.I72
