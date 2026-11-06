import Yulang.CommonFinitePresence

/-!
# Arbitrary demand parameters and Q5 separation in the finite carrier

A parameter denotes the complete observation family of its assigned type.
The assignment is used again in the negative argument of an arrow, with no
restriction to closed negative syntax or an enumerated rigid test sample.
-/

namespace Yulang.CommonFinite

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

theorem demand_parameter_refl (rank : Nat) (env : Environment Row) (name : Nat) :
    AcceptAt leRow rank env (env.types name) (.var name) :=
  fun _ valid => valid

/-- The very type chosen by the same environment is compared at the lower
negative-context rank; the assignment may itself contain masks or defaults. -/
theorem arrow_env_parameter_exact (rank : Nat) (env : Environment Row) (name : Nat)
    (input output : Ty Row) (inputRow outputRow : Row) :
    AcceptAt leRow (rank + 1) env (.arrow input inputRow output outputRow)
      (.atom (.arrowArgument name)) ↔ ProducerLeAt leRow rank (env.types name) input := by
  rw [acceptAt_atom, producerLeAt_iff_probe]
  rfl

namespace Examples

def mixedRole (Row : Type u) : Environment Row :=
  ⟨fun _ => .union (.base .int) (.base .str), fun _ => [.base .int, .base .str]⟩

theorem mixed_union_has_role (leRow : Row → Row → Prop) (rank : Nat) :
    AcceptAt leRow rank (mixedRole Row) (.union (.base .int) (.base .str)) (.role 0) := by
  rw [acceptAt_role]
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep, mixedRole]

theorem top_lacks_role (leRow : Row → Row → Prop) (rank : Nat) :
    ¬ AcceptAt leRow rank (mixedRole Row) .top (.role 0) := by
  rw [acceptAt_role]
  cases rank <;> simp [ProbeAt, ProbeStep, MaskedProbeStep]

theorem mixed_union_not_equivalent_top (leRow : Row → Row → Prop) :
    ¬ ProducerEq leRow (.union (.base .int) (.base .str)) .top := by
  intro same
  exact top_lacks_role leRow 0 (same.2 0 (mixedRole Row) (.role 0) (mixed_union_has_role leRow 0))

/-- The same distinction can be expressed by a parameter demand. It is not
lost by treating a parameter as a list of ordinary rigid head tests. -/
theorem top_lacks_mixed_parameter (leRow : Row → Row → Prop) (rank : Nat) :
    ¬ AcceptAt leRow rank (mixedRole Row) .top (.var 0) := by
  intro accepted
  have witness : Demand.tests leRow rank (mixedRole Row) (.var 0) (.role 0) := by
    change ProbeAt leRow rank (mixedRole Row) (.union (.base .int) (.base .str)) (.role 0)
    exact (acceptAt_role rank _ _ 0).mp (mixed_union_has_role leRow rank)
  have impossible := accepted (.role 0) witness
  exact top_lacks_role leRow rank ((acceptAt_role rank _ _ 0).mpr impossible)

/-- The distinction also survives a negative arrow context. -/
theorem mixed_arrow_not_equivalent_top_arrow (leRow : Row → Row → Prop) (row : Row) :
    ¬ ProducerEq leRow
      (.arrow (.union (.base .int) (.base .str)) row (.base .int) row)
      (.arrow .top row (.base .int) row) := by
  intro same
  exact mixed_union_not_equivalent_top leRow
    ⟨arrow_argument_inversion same.2, arrow_argument_inversion same.1⟩

end Examples

end Yulang.CommonFinite
