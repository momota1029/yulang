import Yulang.GeneralDeclarativeI65I74ExplicitPickCoherence419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open Checker408 (Problem Result)

/-- An accepted witness supplies the location of the real declaration and
retained equation. Neither location can set the logical output ordinal. -/
theorem replay_pick_uses_literal_locator419 {p wire a}
    (found : replayPick419 p wire = some a) :
    a.declaration.ordinal = wire.declaration ∧
      p.state.core.current.ordinary.equations[wire.outputRow]? =
        some ⟨p.root.demand.outputs[exactlyOneOutput p a.single].target,.variable a.rows.intSlot⟩ := by
  simp only [replayPick419,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at found
  obtain ⟨r,_,body⟩ := found
  split at body
  next safe =>
    simp only [Option.bind_eq_some_iff] at body
    obtain ⟨d,decl,body⟩ := body
    split at body
    next one =>
      simp only [Option.bind_eq_some_iff] at body
      obtain ⟨out,picked,body⟩ := body
      repeat' (first | split at body | contradiction)
      cases Option.some.inj body
      refine ⟨read_declaration_uses_the_supplied_ordinal419 decl,?_⟩
      change p.state.core.current.ordinary.equations[wire.outputRow]? =
        some ⟨p.root.demand.outputs[exactlyOneOutput p one].target,.variable r.intSlot⟩
      rw [← (eq_expr _ _).mp ‹eqExpr out.expr (.variable r.intSlot) = true›]
      exact replay_output_uses_the_supplied_equation_ordinal419 picked
    next => contradiction
  next => contradiction

theorem check_has_original_typed_write_at_supplied_locator419 {p : Problem} {r : Result} {w : PickWire}
    (yes : check p r (.explicitPick w) = true) :
    ∃ a : PickPacket p, r = pickReport a ∧ r.writes = [a.retained.write] ∧
      a.retained.write.declarationOrdinal = w.declaration ∧ a.retained.write.outputOrdinal = 0 ∧
      p.state.core.current.ordinary.equations[w.outputRow]? =
        some ⟨a.retained.write.target.target,.variable a.rows.intSlot⟩ := by
  obtain ⟨a,found,rfl⟩ := checked_report_uses_original_pick419 yes
  obtain ⟨declaration,row⟩ := replay_pick_uses_literal_locator419 found
  exact ⟨a,rfl,rfl,declaration,rfl,row⟩

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
