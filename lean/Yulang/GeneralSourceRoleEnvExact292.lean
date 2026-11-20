import Yulang.GeneralSourceRoleEnvCheck292

/-! Exact local attachment at a successful finite lowering. On failure the
agreement test is only sufficient for equal results, not necessary. -/
namespace Yulang.GeneralSourceRoleEnvExact292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292
open GeneralSourceRoleLocalEnv292 GeneralSourceRoleEnvCheck292
open GeneralSourceRoleSyntaxBoundary292 (Shell projectRole)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceMetadataExprDomain291 (bind_success)

theorem align_both {A B : Type} {p q : A → B → Prop} {xs : List A} {ys : List B}
    (left : Aligned p xs ys) (right : Aligned q xs ys) :
    Aligned (fun a b => p a b ∧ q a b) xs ys := by
  induction left with
  | nil => exact .nil
  | cons first _ ih =>
    cases right with
    | cons second tail => exact .cons ⟨first,second⟩ (ih tail)

theorem with_member {A B : Type} {p q : A → B → Prop} {xs : List A} {ys : List B}
    (left : Aligned p xs ys) (right : Aligned q xs ys) {a : A} (place : a ∈ xs) :
    ∃ b ∈ ys, p a b ∧ q a b := GeneralSourceRoleManifest292.aligned_left (align_both left right) place

theorem body_of_witnesses {e f : Environment} {xs : List String} {b : Body} {v : Option Roles.Term}
    (old : ResolvedBody e xs b v) (new : ResolvedBody f xs b v) : BodyAgree e f b := by
  cases old with
  | required => trivial
  | binder _ => trivial
  | nullary h =>
    cases new with
    | nullary hf => exact h.trans hf.symm

theorem output_of_witnesses {e f : Environment} {r : Nat} {xs : List String}
    {entry : Output} {result : Nat × Option Roles.Term}
    (old : OutputWitness e r xs entry result) (new : OutputWitness f r xs entry result) :
    OutputAgree e f r entry :=
  ⟨old.1.trans new.1.symm,fun _ _ => body_of_witnesses old.2 new.2⟩

theorem role_of_witnesses {e f : Environment} {r : Role}
    {result : GeneralSourceMetadataBareRole291.BareRow}
    (old : RowWitness e r result) (new : RowWitness f r result) : Agree e f r := by
  refine ⟨old.2.1.trans new.2.1.symm,?_⟩
  intro id read o member
  have e := Option.some.inj (read.symm.trans old.2.1)
  subst id
  obtain ⟨out,_,h₁,h₂⟩ := with_member old.2.2.2 new.2.2.2 member
  exact output_of_witnesses h₁ h₂

theorem same_result_requires_agreement (e f : Environment) (fallback : Nat) (inputs : List Role)
    (out : RoleSource) (left : lower e fallback inputs = some out)
    (right : lower f fallback inputs = some out) : checkRoles e f inputs = true := by
  apply (check_roles_exact ..).mpr
  intro r found
  obtain ⟨row,_,h₁,h₂⟩ := with_member
    ((lower_exact ..).mp left).2.1 ((lower_exact ..).mp right).2.1 found
  exact role_of_witnesses h₁ h₂

theorem at_success_exact (e f : Environment) (fallback : Nat) (inputs : List Role)
    (out : RoleSource) (left : lower e fallback inputs = some out) :
    lower f fallback inputs = some out ↔ checkRoles e f inputs = true := by
  constructor
  · exact same_result_requires_agreement e f fallback inputs out left
  · intro h
    exact (lower_agrees fallback inputs ((check_roles_exact ..).mp h)).symm.trans left

theorem shell_at_success_exact (e f : Environment) (fallback : Nat) (inputs : List Shell)
    (out : RoleSource) (left : applyShells e fallback inputs = some out) :
    applyShells f fallback inputs = some out ↔ checkShells e f inputs = true := by
  obtain ⟨symbolic,shape,old⟩ := bind_success left
  unfold applyShells at left ⊢
  rw [shape]
  change lower f fallback symbolic = some out ↔ checkShells e f inputs = true
  unfold checkShells
  rw [shape]
  exact at_success_exact e f fallback symbolic out old

end Yulang.GeneralSourceRoleEnvExact292
