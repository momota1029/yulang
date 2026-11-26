import Yulang.GeneralDeclarativeI65I74SplitEscape446

namespace Yulang.GeneralDeclarativeI65.I72.SplitEscape446.Audit
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open List410

def flat : Equation := ⟨1,.variable 2⟩
def edge : Equation := ⟨0,.nominal 9 [.variable 1]⟩
def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[(2,0),(0,1)]⟩,[flat,edge]⟩
def witness : ExactEscapeWire := ⟨[1,2,0],[1,0,1]⟩

theorem separated_grades_accept_original_counterexample446 :
    splitCheck446 raw 0 witness = true ∧ checkExactEscape raw 0 witness = false := by
  decide +kernel

theorem accepts_the_actual_original_raw_safe_case446 : ¬AliasCycle raw (observed raw) 0 :=
  checked_split_escape_excludes_exact_raw_K2446 separated_grades_accept_original_counterexample446.1

theorem actual_original_cycle_has_no_accepted_split_certificate446
    {s : GeneralDeclarativeHead320.State} {site : Nat} (c : AliasCycle s (observed s) site) :
    ∀ w : ExactEscapeWire, splitCheck446 s site w = false := by
  intro w
  cases result : splitCheck446 s site w
  · rfl
  · exact (checked_split_escape_excludes_exact_raw_K2446 result c).elim

#print axioms split_independent_certificate_excludes_exact_raw_K2446
#print axioms split_check_reflects_actual_rows446
#print axioms checked_split_escape_excludes_exact_raw_K2446
#print axioms separated_grades_accept_original_counterexample446
#print axioms accepts_the_actual_original_raw_safe_case446
#print axioms actual_original_cycle_has_no_accepted_split_certificate446
end Yulang.GeneralDeclarativeI65.I72.SplitEscape446.Audit
