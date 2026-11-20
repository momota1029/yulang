import Yulang.GeneralSourceRoleSyntaxPipeline292

/-! Independent resolution tables may vary outside the names read by the
symbolic fragment. Agreement is local and supports failed inputs as well. -/
namespace Yulang.GeneralSourceRoleLocalEnv292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292

def BodyAgree (e f : Environment) : Body → Prop
  | .nullary s => e.nullaryConstructor s = f.nullaryConstructor s
  | _ => True

def OutputAgree (e f : Environment) (r : Nat) (o : Output) : Prop :=
  e.output r o.spelling = f.output r o.spelling ∧
  (∀ id, e.output r o.spelling = some id → BodyAgree e f o.body)

def Agree (e f : Environment) (input : Role) : Prop :=
  e.role input.spelling = f.role input.spelling ∧
  ∀ r, e.role input.spelling = some r → ∀ o ∈ input.outputs, OutputAgree e f r o

theorem body_agrees {e f : Environment} (binders : List String) (rhs : Body)
    (h : BodyAgree e f rhs) : body e binders rhs = body f binders rhs := by
  cases rhs with
  | required => rfl
  | binder n => rfl
  | nullary n =>
    change e.nullaryConstructor n = f.nullaryConstructor n at h
    simp [body,h]

theorem output_agrees {e f : Environment} (r : Nat) (xs : List String) (o : Output)
    (agreement : OutputAgree e f r o) :
    resolveOutput e r xs o = resolveOutput f r xs o := by
  unfold resolveOutput
  cases h : e.output r o.spelling with
  | none =>
    have hf : f.output r o.spelling = none := agreement.1.symm.trans h
    rw [hf]; rfl
  | some id =>
    have hf : f.output r o.spelling = some id := agreement.1.symm.trans h
    rw [hf,Option.bind_some,Option.bind_some,body_agrees xs o.body (agreement.2 id h)]

theorem collect_congr {A B : Type} (f g : A → Option B) (xs : List A)
    (h : ∀ x ∈ xs, f x = g x) : collect f xs = collect g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have all : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [collect,collect,h x List.mem_cons_self,ih all]

theorem role_agrees {e f : Environment} (input : Role) (agreement : Agree e f input) :
    resolveRole e input = resolveRole f input := by
  unfold resolveRole
  cases key : e.role input.spelling with
  | none =>
    have hf : f.role input.spelling = none := agreement.1.symm.trans key
    rw [hf]; rfl
  | some r =>
    have hf : f.role input.spelling = some r := agreement.1.symm.trans key
    have projected := collect_congr (resolveOutput e r input.binders)
      (resolveOutput f r input.binders) input.outputs
      (fun o m => output_agrees r input.binders o (agreement.2 r key o m))
    rw [hf,Option.bind_some,Option.bind_some,projected]

theorem lower_agrees {e f : Environment} (fallback : Nat) (input : List Role)
    (agreement : ∀ r ∈ input, Agree e f r) : lower e fallback input = lower f fallback input := by
  unfold lower
  rw [collect_congr _ _ _ (fun r m => role_agrees r (agreement r m))]

end Yulang.GeneralSourceRoleLocalEnv292
