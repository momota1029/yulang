import Yulang.LiteralValues

namespace Yulang.LiteralValueExamples

open LiteralValues

private def noFloat : Empty → Empty → Bool := fun impossible => Empty.elim impossible

/-- No fixed machine-word bound is imposed on the integer matcher. -/
theorem integer_successor_distinct (integer : Int) :
    matchCheck noFloat (.int integer) (.int (integer + 1)) = false := by
  simp only [matchCheck, decide_eq_false_iff_not]
  omega

theorem beyond_machine_word :
    matchCheck noFloat (.int 184467440737095516170000000000000000001)
      (.int 184467440737095516170000000000000000001) = true := by decide

theorem retains_decoded_string :
    matchCheck noFloat (.str "文字列 → 値") (.str "文字列 → 値") = true := by decide

theorem booleans_remain_distinct :
    matchCheck noFloat (.bool true) (.bool false) = false := rfl

theorem number_and_string_remain_distinct :
    matchCheck noFloat (.int 42) (.str "42") = false := rfl

theorem unit_matches : matchCheck noFloat .unit .unit = true := rfl

theorem negative_range_lower_included :
    intRangeCheck (some (-7)) (some 3) (.int (-7) : Literal Empty) = true := by decide

theorem range_upper_included :
    intRangeCheck (some (-7)) (some 3) (.int 3 : Literal Empty) = true := by decide

theorem range_above_upper_rejected :
    intRangeCheck (some (-7)) (some 3) (.int 4 : Literal Empty) = false := by decide

theorem one_sided_range (integer : Int) :
    intRangeCheck (some integer) none (.int integer : Literal Empty) = true := by
  simp [intRangeCheck]

/-- Syntax keeps the sign; no float comparison or rounding rule follows. -/
theorem signed_zero_tokens_distinct :
    (⟨true, 0, 0⟩ : DecimalToken) ≠ ⟨false, 0, 0⟩ := by decide

end Yulang.LiteralValueExamples
