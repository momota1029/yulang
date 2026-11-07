import Yulang.CorePresenceGenerationExact

/-!
# Reindexing resolved default/guard/body expressions

The environment relation compares all instances of each binding, including
captured polymorphic schemes. Local lambda/let binders lift the mapping;
reindexing preserves value restriction and both existing let alternatives.
-/

namespace Yulang.CommonPatternScopeRenaming

open Core.PresenceGeneration
open Inference (Expr)

def liftIndex (rename : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rename n + 1

def renameExpr (rename : Nat → Nat) : Expr → Expr
  | .var name => .var (rename name)
  | .lit base => .lit base
  | .lam body => .lam (renameExpr (liftIndex rename) body)
  | .app function argument => .app (renameExpr rename function) (renameExpr rename argument)
  | .letE value body => .letE (renameExpr rename value) (renameExpr (liftIndex rename) body)
  | .branch condition yes no => .branch (renameExpr rename condition) (renameExpr rename yes) (renameExpr rename no)
  | .pair first last => .pair (renameExpr rename first) (renameExpr rename last)
  | .fst pair => .fst (renameExpr rename pair)
  | .snd pair => .snd (renameExpr rename pair)
  | .emptyRecord => .emptyRecord
  | .record label head tail => .record label (renameExpr rename head) (renameExpr rename tail)
  | .recordDefault label source fallback => .recordDefault label (renameExpr rename source) (renameExpr rename fallback)
  | .field label record => .field label (renameExpr rename record)
  | .variant tag payload => .variant tag (renameExpr rename payload)

@[simp] theorem rename_isValue (rename : Nat → Nat) (expression : Expr) :
    (renameExpr rename expression).isValue = expression.isValue := by
  induction expression generalizing rename <;> simp_all [renameExpr, Expr.isValue]

def EnvInstances (m : Model) (source target : List (Binding m)) (rename : Nat → Nat) : Prop :=
  ∀ index result, BindingLookup m source index result ↔ BindingLookup m target (rename index) result

theorem EnvInstances.cons {m : Model} {source target : List (Binding m)} {rename : Nat → Nat}
    (same : EnvInstances m source target rename) (first last : Binding m)
    (head : ∀ result, BindingTyping m first result ↔ BindingTyping m last result) :
    EnvInstances m (first :: source) (last :: target) (liftIndex rename) := by
  intro index result
  cases index with
  | zero => simpa [BindingLookup, liftIndex] using head result
  | succ index => simpa [BindingLookup, liftIndex] using same index result

theorem EnvInstances.mono {m : Model} {source target : List (Binding m)} {rename : Nat → Nat}
    (same : EnvInstances m source target rename) (value : Comp m) :
    EnvInstances m (.mono value :: source) (.mono value :: target) (liftIndex rename) :=
  same.cons _ _ (fun _ => Iff.rfl)

/-- All expressions, original/target environments, reindexings and computation
results. The only premise compares the instances at every referenced index.
No injectivity, success, purity or generalization restriction is added. -/
theorem typing_rename_exact (expression : Expr) (m : Model) (rename : Nat → Nat)
    (source target : List (Binding m)) (same : EnvInstances m source target rename) (result : Comp m) :
    Typing m source expression result ↔ Typing m target (renameExpr rename expression) result := by
  induction expression generalizing rename source target result with
  | var index => simpa only [renameExpr, Typing.var_iff] using same index result
  | lit base => simp only [renameExpr, Typing.lit_iff]
  | emptyRecord => simp only [renameExpr, Typing.emptyRecord_iff]
  | lam body ih =>
      simp only [renameExpr, Typing.lam_iff]
      apply exists_congr
      intro a
      apply exists_congr
      intro b
      exact and_congr (ih (liftIndex rename) _ _ (same.mono a) b) Iff.rfl
  | app function argument ihf iha =>
      simp only [renameExpr, Typing.app_iff, ihf rename source target same, iha rename source target same]
  | branch condition yes no ihc ihy ihn =>
      simp only [renameExpr, Typing.branch_iff, ihc rename source target same,
        ihy rename source target same, ihn rename source target same]
  | pair first last ihf ihl =>
      simp only [renameExpr, Typing.pair_iff, ihf rename source target same, ihl rename source target same]
  | fst pair ih => simp only [renameExpr, Typing.fst_iff, ih rename source target same]
  | snd pair ih => simp only [renameExpr, Typing.snd_iff, ih rename source target same]
  | record label head tail ihh iht =>
      simp only [renameExpr, Typing.record_iff, ihh rename source target same, iht rename source target same]
  | recordDefault label base fallback ihb ihf =>
      simp only [renameExpr, Typing.recordDefault_iff, ihb rename source target same, ihf rename source target same]
  | field label record ih => simp only [renameExpr, Typing.field_iff, ih rename source target same]
  | variant tag payload ih => simp only [renameExpr, Typing.variant_iff, ih rename source target same]
  | letE value body ihv ihb =>
      have definition := ihv rename source target same
      have monomorphic (a : Comp m) := ihb (liftIndex rename) _ _ (same.mono (Comp.pure m a.1))
      have polymorphic := ihb (liftIndex rename) (.poly value source :: source)
        (.poly (renameExpr rename value) target :: target)
        (same.cons _ _ (fun computation => by simp only [BindingTyping.poly_iff, definition]))
      simp only [renameExpr]
      cases shape : value.isValue with
      | false =>
          rw [Typing.letComputed_iff m source value body result shape,
            Typing.letComputed_iff m target (renameExpr rename value) (renameExpr (liftIndex rename) body)
              result (by simpa only [rename_isValue] using shape)]
          simp only [definition, monomorphic]
      | true =>
          rw [Typing.letValue_iff m source value body result shape,
            Typing.letValue_iff m target (renameExpr rename value) (renameExpr (liftIndex rename) body)
              result (by simpa only [rename_isValue] using shape)]
          simp only [definition, monomorphic, polymorphic]

/-- The same reindexing preserves the actual finite expression constraints,
for arbitrary symbolic slot sets and assignments interpreting the related
source/target environments and the same requested computation. -/
theorem generation_rename_exact (expression : Expr) (m : Model) (rename : Nat → Nat)
    (source target : List (Binding m)) (same : EnvInstances m source target rename)
    (sourceSlots : α → Comp m) (targetSlots : β → Comp m)
    (sourceEnv : SchemeEnv α) (targetEnv : SchemeEnv β)
    (sourceRelated : EnvRel m sourceSlots sourceEnv source)
    (targetRelated : EnvRel m targetSlots targetEnv target)
    (sourceResult : CompTerm α) (targetResult : CompTerm β)
    (resultSame : sourceResult.eval m sourceSlots = targetResult.eval m targetSlots) :
    (generate sourceEnv expression sourceResult).Holds m sourceSlots ↔
      (generate targetEnv (renameExpr rename expression) targetResult).Holds m targetSlots := by
  rw [generate_models_iff_typing m expression sourceEnv source sourceSlots sourceResult sourceRelated,
    generate_models_iff_typing m (renameExpr rename expression) targetEnv target targetSlots targetResult targetRelated,
    resultSame]
  exact typing_rename_exact expression m rename source target same _

end Yulang.CommonPatternScopeRenaming
