import Yulang.GeneralDictionaryAssociatedProvenance

/-! Concrete checks retain explicit equation IDs, positional defaults, and two
occurrences of one name at different source targets. No Common interpretation
or candidate resolution is asserted by these examples. -/
namespace Yulang.GeneralDictionaryAssociatedProvenanceExamples
open GeneralDeclarations GeneralDictionaryAssociatedProvenance

private def roles : Roles.RoleDecls := fun _ =>
  { arity := 1
    assoc := fun name => if name = 0 then some (some (.var 0)) else none
    defaultsScoped := by
      intro name rhs present
      split at present
      · cases present; simp [Roles.Term.bound]
      · cases present }

private def equation : Equation := ⟨17, 0, .var 91⟩
private def explicit : Declaration := ⟨23, 4, [.var 91], [], [equation], []⟩
private def fallback : Declaration := { explicit with associated := [] }

/-- A present explicit body wins even though the role also declares a default.
Its source equation ID and declaration-variable name are not erased. -/
theorem explicit_wins : lookup roles explicit 0 = some (.explicit equation) := rfl

/-- A role default retains positional variable 0, rather than relabeling it as
implementation variable 91 or choosing a captured interval endpoint. -/
theorem positional_default : lookup roles fallback 0 = some (.default 4 0 (.var 0)) := rfl

theorem undeclared_absent : lookup roles fallback 1 = none := rfl

private def demand : GeneralSourceState.Demand roles where
  role := 4
  arguments := fun _ => (10, 11)
  outputs := [⟨0, 21⟩, ⟨0, 22⟩]
  declared := by
    intro output member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨some (.var 0), rfl⟩

/-- Both constraints remain present; sharing a name does not merge targets. -/
theorem repeated_name_distinct_targets : outputs roles fallback demand =
    [(⟨0, 21⟩, some (.default 4 0 (.var 0))),
     (⟨0, 22⟩, some (.default 4 0 (.var 0)))] := rfl

end Yulang.GeneralDictionaryAssociatedProvenanceExamples
