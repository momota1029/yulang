import Yulang.GeneralSourceRoleOperationalRead292

/-! The two closed accepted source-default controls satisfy the old object's
association well-formedness, not just its post-selection executable read. -/
namespace Yulang.GeneralSourceRoleOperationalFixture292
open Yulang.Roles
open Yulang.Roles.Examples (int str)
open Yulang.Roles.AssocExamples
  (char index singletonEnv omittedImpl strImpl omitted_paterson str_paterson omitted_resolved str_resolved)
open GeneralSourceRoleResolverFixture292
open GeneralSourceMetadataRoles291 (roleTable)
open GeneralSourceRoleOperationalRead292 (resolved_declared_has_compiled_value)
open GeneralSourceRoleResolverUse292 (ShellDefault)
open GeneralSourceRoleSpelling292 (ResolvedBody Position)

theorem old_index_decl_parameter_is_positional :
    (roleTable parameterTable 2).assoc 0 = some (some (.var 1)) ∧
    Yulang.Roles.AssocExamples.parameterDefaultDecl.assoc 0 = some (some (.var 0)) :=
  ⟨rfl,rfl⟩

theorem parameter_omission_wellformed :
    AssocWellFormed (singletonEnv omittedImpl) (roleTable parameterTable) := by
  intro i membership
  have sim : i = omittedImpl := by simpa [singletonEnv] using membership
  subst i
  constructor
  · intro n b h; cases h
  · refine ⟨⟨rfl,?_⟩,?_⟩
    · intro n d h
      change (if n = 0 then some (some (.var 1 : Term)) else none) = some d at h
      split at h
      · exact Or.inr ⟨.var 1,(Option.some.inj h).symm⟩
      · cases h
    · intro n v h; cases h

theorem parameter_default_source :
    ShellDefault localEnv [shell (.binder "'key") true] 2 0 (.var 1) := by
  refine ⟨_,List.mem_singleton_self _,rfl,_,List.mem_singleton_self _,_,.binder _ _,rfl,?_⟩
  exact .binder (.rest (by decide) .first)

theorem parameter_value_old_total :
    ∃ t, assocOf (singletonEnv omittedImpl) (roleTable parameterTable)
      omitted_paterson (index str int) 0 = some t ∧
      ∀ v, 0 < t.occurrences v → 0 < argsOccurrences v [str,int] :=
  resolved_declared_has_compiled_value body_shells_export.1 _ omitted_paterson
    parameter_omission_wellformed _ _ omitted_resolved _ parameter_default_source

theorem scalar_omission_wellformed :
    AssocWellFormed (singletonEnv omittedImpl) (roleTable charTable) := by
  intro i membership
  have sim : i = omittedImpl := by simpa [singletonEnv] using membership
  subst i
  constructor
  · intro n b h; cases h
  · refine ⟨⟨rfl,?_⟩,?_⟩
    · intro n d h
      change (if n = 0 then some (some char) else none) = some d at h
      split at h
      · exact Or.inr ⟨char,(Option.some.inj h).symm⟩
      · cases h
    · intro n v h; cases h

end Yulang.GeneralSourceRoleOperationalFixture292
