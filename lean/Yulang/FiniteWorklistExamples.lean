import Yulang.SemilinearAutomataExamples

/-!
# Executed worklist regression on infinite semilinear sets

The source natural ray is covered jointly by the even and odd target rays.
These tests call the generic NFA comparison directly, bypassing semilinear
normalization and sufficient fast acceptance. The automata have 5 and 14 carry
states, hence 524288 possible subset pairs, but only five are reachable.

The Boolean result is proved through the all-word correctness theorem and the
independent arithmetic characterization of the rays. The separate IO regression
also executes the actual search during compilation and fails on an incorrect
positive or negative result. It adds no axiom or native proof evaluation.
-/

namespace Yulang.FiniteWorklist.Examples

open SemilinearAutomata (alphabet automaton)
open SemilinearAutomata.Examples (naturalRay evenRay oddRay parity_union_exact)

def jointCoverage : Bool :=
  FiniteAutomata.checkSubset (alphabet 1) (automaton naturalRay) (automaton (evenRay ++ oddRay))

theorem jointCoverage_accepts : jointCoverage = true := by
  rw [jointCoverage, FiniteAutomata.checkSubset_exact _ SemilinearAutomata.alphabet_complete]
  intro word accepted
  exact (SemilinearAutomata.accepts_exact _ word).mpr
    ((parity_union_exact _).mp ((SemilinearAutomata.accepts_exact _ word).mp accepted))

/-- This proof covers every finite word, independently of how large its
signed integer value or coefficient witnesses are. -/
theorem every_accepted_word_is_covered (word : List (SemilinearDigits.Letter 1))
    (accepted : FiniteAutomata.Accepts (automaton naturalRay) word) :
    FiniteAutomata.Accepts (automaton (evenRay ++ oddRay)) word :=
  (FiniteAutomata.checkSubset_exact _ SemilinearAutomata.alphabet_complete _ _).mp
    jointCoverage_accepts word accepted

def runRegression : IO Unit := do
  let reached := FiniteAutomata.reachablePairs (alphabet 1)
    (automaton naturalRay) (automaton (evenRay ++ oddRay))
  unless reached.length == 5 do
    throw (IO.userError "expected exactly five reachable subset pairs")
  unless jointCoverage do
    throw (IO.userError "the even/odd union must cover the natural ray")
  if FiniteAutomata.checkSubset (alphabet 1) (automaton naturalRay) (automaton evenRay) then
    throw (IO.userError "the even ray alone must not cover every natural number")
  unless FiniteAutomata.checkSubset (alphabet 1) (automaton naturalRay) (automaton naturalRay) do
    throw (IO.userError "the raw ray NFA must be included in itself")

#eval runRegression

end Yulang.FiniteWorklist.Examples
