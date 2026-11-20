import Yulang.GeneralSourceRoleLocalEnv292

/-! A finite check for the declared local read agreement. It does not enumerate
arbitrary environment functions or establish that a parser supplied the lists. -/
namespace Yulang.GeneralSourceRoleEnvCheck292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292 GeneralSourceRoleLocalEnv292
open GeneralSourceRoleSyntaxBoundary292 (Shell projectRole)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)

def checkBody (e f : Environment) (b : Body) : Bool :=
  match b with
  | .nullary n => decide (e.nullaryConstructor n = f.nullaryConstructor n)
  | _ => true

theorem check_body_exact (e f : Environment) (b : Body) :
    checkBody e f b = true ↔ BodyAgree e f b := by
  cases b <;> simp [checkBody,BodyAgree]

def checkOutput (e f : Environment) (r : Nat) (o : Output) : Bool :=
  decide (e.output r o.spelling = f.output r o.spelling) &&
    match e.output r o.spelling with
    | none => true
    | some _ => checkBody e f o.body

theorem check_output_exact (e f : Environment) (r : Nat) (o : Output) :
    checkOutput e f r o = true ↔ OutputAgree e f r o := by
  cases h : e.output r o.spelling <;>
    simp [checkOutput,OutputAgree,h,check_body_exact]

def checkRole (e f : Environment) (input : Role) : Bool :=
  decide (e.role input.spelling = f.role input.spelling) &&
    match e.role input.spelling with
    | none => true
    | some r => input.outputs.all (checkOutput e f r)

theorem check_role_exact (e f : Environment) (input : Role) :
    checkRole e f input = true ↔ Agree e f input := by
  cases h : e.role input.spelling <;>
    simp [checkRole,Agree,h,List.all_eq_true,check_output_exact]

def checkRoles (e f : Environment) (roles : List Role) : Bool :=
  roles.all (checkRole e f)

theorem check_roles_exact (e f : Environment) (roles : List Role) :
    checkRoles e f roles = true ↔ ∀ r ∈ roles, Agree e f r := by
  simp [checkRoles,List.all_eq_true,check_role_exact]

def checkShells (e f : Environment) (shells : List Shell) : Bool :=
  match collect projectRole shells with
  | none => true
  | some roles => checkRoles e f roles

theorem shell_check_exact (e f : Environment) (shells : List Shell) :
    checkShells e f shells = true ↔
      ∀ roles, collect projectRole shells = some roles → ∀ r ∈ roles, Agree e f r := by
  cases h : collect projectRole shells <;> simp [checkShells,h,check_roles_exact]

theorem shell_check_sound (e f : Environment) (fallback : Nat) (shells : List Shell)
    (h : checkShells e f shells = true) : applyShells e fallback shells = applyShells f fallback shells := by
  unfold applyShells
  cases hh : collect projectRole shells with
  | none => rfl
  | some roles =>
    simp only [Option.bind_some]
    exact lower_agrees fallback roles ((shell_check_exact ..).mp h roles hh)

end Yulang.GeneralSourceRoleEnvCheck292
