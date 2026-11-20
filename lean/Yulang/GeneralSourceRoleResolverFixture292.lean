import Yulang.GeneralSourceRoleResolverUse292

/-! Execute the existing first-order resolver and its association reader on a
new finite role input; all goals and impls are the old AssocExamples. -/
namespace Yulang.GeneralSourceRoleResolverFixture292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (Shell Shape Rhs)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceMetadataRoles291 (RoleRow RoleSource roleTable)
open Yulang.Roles
open Yulang.Roles.Examples (int str)
open Yulang.Roles.AssocExamples
  (char index singletonEnv omittedImpl strImpl omitted_paterson str_paterson omitted_resolved str_resolved)

def localEnv : Environment :=
  ⟨fun n => if n = "Index" then some 2 else none,
   fun r n => if r = 2 ∧ n = "value" then some 0 else none,
   fun n => if n = "char" then some 3 else none⟩

def shell (rhs : Rhs) (eq : Bool) : Shell :=
  ⟨"Index",["'container","'key"],[⟨"value",eq,rhs,true⟩]⟩

def rolesFor (body : Option Term)
    (inScope : ∀ t, body = some t → t.bound ≤ 2) : RoleSource :=
  ⟨2,[⟨2,2,[(0,body)],by
    intro name value hit
    have proof := congrArg Prod.snd (List.mem_singleton.mp hit)
    exact inScope value proof.symm⟩]⟩

def parameterTable : RoleSource := rolesFor (some (.var 1)) (by
  intro t ht; cases Option.some.inj ht; exact Nat.le_refl _)

def charTable : RoleSource := rolesFor (some char) (by
  intro t ht; cases Option.some.inj ht; exact Nat.zero_le 2)

def requiredTable : RoleSource := rolesFor none (by
  intro t bad; cases bad)

theorem body_shells_export :
    applyShells localEnv 2 [shell (.binder "'key") true] = some parameterTable ∧
    applyShells localEnv 2 [shell (.nullary "char") true] = some charTable ∧
    applyShells localEnv 2 [shell .absent false] = some requiredTable :=
  ⟨rfl,rfl,rfl⟩

theorem role_parameter_used_by_actual_reader :
    assocOf (singletonEnv omittedImpl) (roleTable parameterTable)
      omitted_paterson (index str int) 0 = some int := by
  rw [assoc_independent_of_constraints _ _ _ _ _ omitted_resolved omittedImpl
    (by simp [singletonEnv]) (by decide)]
  rfl

theorem explicit_overrides_shell_default :
    assocOf (singletonEnv strImpl) (roleTable parameterTable)
      str_paterson (index str int) 0 = some char := by
  rw [assoc_independent_of_constraints _ _ _ _ _ str_resolved strImpl (by simp [singletonEnv]) (by decide)]
  rfl

theorem nullary_shell_default_used :
    assocOf (singletonEnv omittedImpl) (roleTable charTable)
      omitted_paterson (index str int) 0 = some char := by
  rw [assoc_independent_of_constraints _ _ _ _ _ omitted_resolved omittedImpl
    (by simp [singletonEnv]) (by decide)]
  rfl

theorem required_without_body_is_not_valid_implementation :
    assocOf (singletonEnv omittedImpl) (roleTable requiredTable)
      omitted_paterson (index str int) 0 = none ∧
    ¬ AssocWellFormed (singletonEnv omittedImpl) (roleTable requiredTable) := by
  constructor
  · rw [assoc_independent_of_constraints _ _ _ _ _ omitted_resolved omittedImpl
      (by simp [singletonEnv]) (by decide)]
    rfl
  · intro wf
    have present : (roleTable requiredTable omittedImpl.impl.role).assoc 0 = some none := rfl
    have impossible := (wf omittedImpl (by simp [singletonEnv])).2.1.2 0 none present
    simp [omittedImpl] at impossible

end Yulang.GeneralSourceRoleResolverFixture292
