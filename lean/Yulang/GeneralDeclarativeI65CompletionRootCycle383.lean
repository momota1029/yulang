import Yulang.GeneralDeclarativeI65CompletionRead383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Alias321 (cycle_in_alias_graph)
open GeneralDeclarativeGraphRows321 (literal_head structural)
open GeneralDeclarativeK2Graph321 (OnCycle)

/-- An actual ordinary nominal self-row at an input lower bound gives
the specified root cycle directly. This proof does not restrict the
graph by any completion or use a release or manifest. -/
theorem ordinary_self_row_yields_root_cycle383
    {s : State} {q : Request} {a : Capture} {tag : Nat}
    (arg : a ∈ q.demand.arguments)
    (stored : (⟨a.lower,.nominal tag [.variable a.lower]⟩ : Equation) ∈
      s.current.ordinary.equations) :
    RootCycle383 s q := by
  have closes : OnCycle (structural s.current.ordinary) a.lower := by
    refine ⟨a.lower,⟨.nominal tag [a.lower],literal_head stored rfl,?_⟩,.refl _⟩
    exact List.mem_cons_self
  exact ⟨a,arg,cycle_in_alias_graph closes⟩

/-- The same literal current equation can trigger I-59 even though
its only declarative read supports would belong to a closed cycle.
This is an entry-frontier rejection, not candidate-local K2 or
the complete language classifier. -/
theorem circular_only_self_output_is_still_root_k2383
    {rules : SelectedSourceRule383} {direct : DirectEquation383}
    {generated : LogicalOutputEquation383} {s : State} {q : Request} {a : Capture} {tag : Nat}
    (arg : a ∈ q.demand.arguments)
    (stored : (⟨a.lower,.nominal tag [.variable a.lower]⟩ : Equation) ∈ s.current.ordinary.equations)
    (closed : Request → Prop)
    (closedBy : ∀ q deps key kids, rules s q deps key kids → closed q →
      (∃ p ∈ deps,closed p) ∨ (∃ k ∈ kids,closed k))
    (notWritten : ¬direct s ⟨a.lower,.nominal tag [.variable a.lower]⟩)
    (noExternal : ∀ producer d ordinal,
      LogicalOutputLink383 generated s producer d ordinal ⟨a.lower,.nominal tag [.variable a.lower]⟩ →
        closed producer) :
    let ready := Nonempty (SourceEquationRead383 rules direct generated s
      ⟨a.lower,.nominal tag [.variable a.lower]⟩)
    ¬ready ∧ RootEntry383 s q ready .rootK2 := by
  exact ⟨circular_only_equation_is_not_a_read383 closed closedBy notWritten noExternal,
    .root (ordinary_self_row_yields_root_cycle383 arg stored)⟩

end Yulang.GeneralDeclarativeI65
