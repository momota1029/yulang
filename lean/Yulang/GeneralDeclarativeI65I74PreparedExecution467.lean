import Yulang.GeneralDeclarativeWitnessNativePreparation360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedExecution467
open GeneralDeclarativeWitnessNativePreparation360
open GeneralDeclarativeWitnessCompiler350 (preparation whereBatch)
open GeneralDeclarativeWitnessLiteral349 (preserves)

theorem native_preparation_replays_exact_independent_record {e f d l}
    (made : Prepared e f d l) : prepare e f d l = some made := by
  rcases made with ⟨impl,identity,authored,checked,shaped,requested,
    before,ports,execution,rows,emits,retained⟩
  unfold prepare
  split
  · rename_i absent
    rw [authored] at absent
    cases absent
  · rename_i observed got
    have sameImpl := Option.some.inj (authored.symm.trans got)
    subst observed
    simp only [dite_eq_left identity,dite_eq_left checked,dite_eq_left shaped,dite_eq_left requested]
    split
    · rename_i missing
      rw [execution] at missing
      cases missing
    · rename_i pair next
      have actual := Option.some.inj (execution.symm.trans next)
      cases actual
      split
      · rename_i missing
        rw [emits] at missing
        cases missing
      · rename_i ys reply
        have same := Option.some.inj (emits.symm.trans reply)
        subst ys
        simp [retained]

theorem independent_prepared_record_unique_if_same_actual_inputs {e f d l}
    (first second : Prepared e f d l) : first = second :=
  Option.some.inj ((native_preparation_replays_exact_independent_record first).symm.trans
    (native_preparation_replays_exact_independent_record second))

end Yulang.GeneralDeclarativeI65.I72.PreparedExecution467
