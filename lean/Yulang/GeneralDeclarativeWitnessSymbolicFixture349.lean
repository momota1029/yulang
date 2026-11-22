import Yulang.GeneralDeclarativeWitnessSymbolic349
import Yulang.GeneralDeclarativeWitnessPointFixture349

namespace Yulang.GeneralDeclarativeWitnessSymbolicFixture349
open GeneralDeclarativeWitnessSymbolic349 (SymbolicReport check)
open GeneralDeclarativeWitnessPointFixture349 (problem answer kind)
open GeneralDeclarativeWitnessGround349 (row)

def exactOut : SymbolicReport := ⟨answer,[row 4 kind]⟩

theorem accepted : check problem exactOut = true := by decide +kernel

/-- The trace, dictionary, output name and fixed address are all
correct, but the independently compiled symbolic body is wrong. -/
theorem changed_rhs : check problem {exactOut with outputEquations := [row 4 (.scalar .str)]} = false := by
  decide +kernel

theorem added_duplicate : check problem {exactOut with outputEquations := [row 4 kind,row 4 kind]} = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessSymbolicFixture349
