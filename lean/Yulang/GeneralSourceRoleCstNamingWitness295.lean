import Yulang.GeneralSourceRoleCstNamingScope295

/-! Compare only the finite lookups used by this selected declaration.
An absent or non-name-resolution branch is never invented by the check. -/
namespace Yulang.GeneralSourceRoleCstNamingWitness295
open GeneralSourceRoleSpelling292 (Body Output Environment Role)
open GeneralSourceRoleLocalEnv292 (BodyAgree OutputAgree Agree)

def bodyMatch (e f : Environment) : Body → Bool
  | .nullary c => e.nullaryConstructor c == f.nullaryConstructor c
  | _ => true

theorem body_match_exact (e f : Environment) (b : Body) :
    bodyMatch e f b = true ↔ BodyAgree e f b := by
  cases b <;> simp [bodyMatch,BodyAgree]

def outputMatch (e f : Environment) (r : Nat) (o : Output) : Bool :=
  e.output r o.spelling == f.output r o.spelling &&
    (match e.output r o.spelling with
    | none => true
    | some _ => bodyMatch e f o.body)

theorem output_match_exact (e f : Environment) (r : Nat) (o : Output) :
    outputMatch e f r o = true ↔ OutputAgree e f r o := by
  cases h : e.output r o.spelling <;> simp [outputMatch,OutputAgree,h,body_match_exact]

def roleMatch (e f : Environment) (r : Role) : Bool :=
  e.role r.spelling == f.role r.spelling &&
    (match e.role r.spelling with
    | none => true
    | some id => r.outputs.all (outputMatch e f id))

theorem role_match_exact (e f : Environment) (r : Role) :
    roleMatch e f r = true ↔ Agree e f r := by
  cases h : e.role r.spelling <;> simp [roleMatch,Agree,h,output_match_exact]

end Yulang.GeneralSourceRoleCstNamingWitness295
