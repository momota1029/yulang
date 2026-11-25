import Yulang.GeneralDeclarativeI65I73UnifiedSound408

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Tree)

def rawReport : Result := ⟨.rejected,.rejected,[]⟩

def nullaryReport (d : Declaration) : Result := ⟨.selected d.id [],.selected (.node d.id []),[]⟩

theorem bool_raw_protocol_exact408 (p : Problem) (r : Result) (w : GeneralDeclarativeWitnessCycle350.Wire) :
    check p r (.rawRoot w) = true ↔
      GeneralDeclarativeWitnessCycle350.check p.state.core.current.ordinary p.root.demand w = true ∧ r = rawReport := by
  cases r
  simp [check,rawReport, matchesNoWrites_exact408, Bool.and_eq_true]

theorem bool_nullary_protocol_exact408 (p : Problem) (r : Result) :
    check p r .nullary = true ↔
      ∃ d, visible p.state.core p.root = [d] ∧ checksNullary p d = true ∧ r = nullaryReport d := by
  cases r with
  | mk t verdict writes =>
    simp only [check]
    split
    · rename_i row atRow
      simp only [Bool.and_eq_true,matchesNoWrites_exact408,nullaryReport,Result.mk.injEq]
      constructor
      · intro h
        exact ⟨row,atRow,h⟩
      · rintro ⟨d,atD,h⟩
        have eq := List.cons.inj (atRow.symm.trans atD) |>.1
        subst d
        exact h
    · rename_i bad
      simp only [Bool.false_eq_true, false_iff,not_exists]
      intro d h
      exact bad _ h.1

theorem checker_refuses_any_extra_emitted_write408 (p : Problem) (r : Result) (w : Witness)
    (extra : r.writes ≠ []) : check p r w = false := by
  cases returned : check p r w
  · rfl
  · exfalso
    cases w with
    | unsupported => simp [check] at returned
    | rawRoot wire =>
      have same := ((bool_raw_protocol_exact408 p r wire).mp returned).2
      exact extra (congrArg Result.writes same)
    | nullary =>
      obtain ⟨_,_,_,same⟩ := (bool_nullary_protocol_exact408 p r).mp returned
      exact extra (congrArg Result.writes same)

/-- Independently supplied successful witnesses cannot allow incompatible
reported answers. Raw K2 and the nullary selected branch are disjoint
on this same Problem; neither match is resolved by dispatch priority. -/
theorem exact_accepted_result_is_unique408 (p : Problem) (r a : Result) (x y : Witness)
    (first : check p r x = true) (second : check p a y = true) : r = a := by
  cases x with
  | unsupported => simp [check] at first
  | rawRoot wx =>
    obtain ⟨valid,same⟩ := (bool_raw_protocol_exact408 p r wx).mp first
    cases y with
    | unsupported => simp [check] at second
    | rawRoot wy => exact same.trans ((bool_raw_protocol_exact408 p a wy).mp second).2.symm
    | nullary =>
      have raw : RootCycle p.state p.root := GeneralDeclarativeWitnessCycle350.rooted valid
      have picked := exact_report_is_R0_classification408 (check_reflects_same_original_report408 p a .nullary second)
      obtain ⟨row,_,_,atRow⟩ := (bool_nullary_protocol_exact408 p a).mp second
      rw [atRow] at picked
      exact False.elim ((R0_raw_root_priority407 raw).2 (.node row.id []) picked)
  | nullary =>
    obtain ⟨d,dAt,dCheck,same⟩ := (bool_nullary_protocol_exact408 p r).mp first
    cases y with
    | unsupported => simp [check] at second
    | rawRoot wire =>
      have valid := ((bool_raw_protocol_exact408 p a wire).mp second).1
      have raw : RootCycle p.state p.root := GeneralDeclarativeWitnessCycle350.rooted valid
      have picked := exact_report_is_R0_classification408 (check_reflects_same_original_report408 p r .nullary first)
      rw [same] at picked
      exact False.elim ((R0_raw_root_priority407 raw).2 (.node d.id []) picked)
    | nullary =>
      obtain ⟨e,eAt,_,eq⟩ := (bool_nullary_protocol_exact408 p a).mp second
      have idEq := (List.cons.inj (dAt.symm.trans eAt)).1
      exact same.trans ((congrArg nullaryReport idEq).trans eq.symm)

end Yulang.GeneralDeclarativeI65.I72.Check408
