import Yulang.MethodResolution
import Yulang.QualifiedInference

/-!
# Frozen dot selections in qualified inference

This connects the SCC-final selection relation to the existing generator. A
field choice emits its structural record constraint. A role choice emits an
application of the selected method declaration, including all its declared
predicates. The independent dot typing relation states those two contracts
directly; it does not invoke selection or constraint generation.

The frozen artifact stores the resolved reference and the already elaborated
receiver. Its principal scheme is the actual `QualifiedInference.principal`.
Arbitrary subsequent formula substitutions, and scheme instantiation, retain
that reference and its declared predicates. Neither operation reruns lookup
with a caller's receiver type. The input site is the final knowledge snapshot
of one SCC; computing that snapshot, full source elaboration, and the supplied
non-field typed-lookup fallback are outside this module.

The scope and method table are separate inputs. Checking that a role's method
reference denotes a declaration that actually requires that role is an
upstream declaration-elaboration obligation. The predicate-preservation
theorems explicitly require membership in the selected declaration's real
requirement list.
-/

namespace Yulang.FrozenMethods

open Inference (Model Comp CompTerm extend)
open RoleConstraints
open QualifiedInference (MethodTable SchemeEnv Binding Formula Scheme EnvRel)
open MethodResolution (Site Reference Selects freeze)

abbrev CoreExpr := QualifiedInference.Expr

def lower (reference : Reference) (receiver : CoreExpr) : CoreExpr :=
  match reference with
  | .field label => .field label receiver
  | .role _ declaration | .direct declaration => .app (.method declaration) receiver

/-- The direct contract of calling a declaration, including its dictionary
requirements, computation argument, latent result, and evaluation effect. -/
def MethodCallTyping (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (declaration : Nat) (receiver : CoreExpr) (c : Comp m) : Prop :=
  ∃ (ι : Fin (methods declaration).locals → m.Ty) (a b : Comp m) (ef : m.Row),
    Satisfies theory ((methods declaration).requirements.map
      (Goal.eval m (QualifiedInference.typeEnv m ι))) ∧
    Comp.le m (Comp.pure m ((methods declaration).value.eval m (QualifiedInference.typeEnv m ι)))
      (Comp.arrow m a b, ef) ∧
    QualifiedInference.Typing m methods theory Γ receiver a ∧
    Comp.le m (b.1, m.join ef b.2) c

def ReferenceTyping (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (reference : Reference) (receiver : CoreExpr) (c : Comp m) : Prop :=
  match reference with
  | .field label => ∃ (value : m.Ty) (effect : m.Row),
      QualifiedInference.Typing m methods theory Γ receiver
        (m.record label value m.emptyRecord, effect) ∧ Comp.le m (value, effect) c
  | .role _ declaration | .direct declaration =>
      MethodCallTyping m methods theory Γ declaration receiver c

def DotTyping (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (site : Site Row) (receiver : CoreExpr) (c : Comp m) : Prop :=
  ∃ reference, Selects site reference ∧ ReferenceTyping m methods theory Γ reference receiver c

theorem method_call_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (declaration : Nat) (receiver : CoreExpr) (c : Comp m) :
    QualifiedInference.Typing m methods theory Γ (.app (.method declaration) receiver) c ↔
      MethodCallTyping m methods theory Γ declaration receiver c := by
  constructor
  · intro typed
    obtain ⟨a, b, ef, method, argument, result⟩ := (QualifiedInference.Typing.app_iff ..).mp typed
    obtain ⟨ι, requirements, subtype⟩ := (QualifiedInference.Typing.method_iff ..).mp method
    exact ⟨ι, a, b, ef, requirements, subtype, argument, result⟩
  · rintro ⟨ι, a, b, ef, requirements, subtype, argument, result⟩
    exact .app (.method ι requirements subtype) argument result

theorem lower_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (reference : Reference) (receiver : CoreExpr) (c : Comp m) :
    QualifiedInference.Typing m methods theory Γ (lower reference receiver) c ↔
      ReferenceTyping m methods theory Γ reference receiver c := by
  cases reference with
  | field label => exact QualifiedInference.Typing.field_iff m methods theory Γ label receiver c
  | role role declaration => exact method_call_exact m methods theory Γ declaration receiver c
  | direct declaration => exact method_call_exact m methods theory Γ declaration receiver c

structure FrozenDot where
  reference : Reference
  receiver : CoreExpr
  deriving DecidableEq, Repr

def FrozenDot.body (dot : FrozenDot) : CoreExpr := lower dot.reference dot.receiver

def finalize (site : Site Row) (receiver : CoreExpr) : Option FrozenDot :=
  (freeze site).map fun reference => ⟨reference, receiver⟩

theorem finalize_exact (site : Site Row) (receiver : CoreExpr) (dot : FrozenDot) :
    finalize site receiver = some dot ↔
      Selects site dot.reference ∧ dot.receiver = receiver := by
  simp only [finalize, Option.map_eq_some_iff]
  constructor
  · rintro ⟨reference, chosen, equal⟩
    cases equal
    exact ⟨(MethodResolution.freeze_exact _ _).mp chosen, rfl⟩
  · rintro ⟨chosen, rfl⟩
    exact ⟨dot.reference, (MethodResolution.freeze_exact _ _).mpr chosen, rfl⟩

def FrozenDot.constraints (dot : FrozenDot) (methods : MethodTable)
    (Γ : SchemeEnv α) (out : CompTerm α) : Formula α :=
  QualifiedInference.generate methods Γ dot.body out

def FrozenDot.principal (dot : FrozenDot) (methods : MethodTable) (Γ : SchemeEnv α) : Scheme α :=
  QualifiedInference.principal methods Γ dot.body

def generateDot (methods : MethodTable) (Γ : SchemeEnv α) (site : Site Row)
    (receiver : CoreExpr) (out : CompTerm α) : Formula α :=
  match freeze site with
  | none => .bot
  | some reference => (FrozenDot.mk reference receiver).constraints methods Γ out

def principalDot (methods : MethodTable) (Γ : SchemeEnv α) (site : Site Row)
    (receiver : CoreExpr) : Scheme α :=
  match freeze site with
  | none => .bot
  | some reference => (FrozenDot.mk reference receiver).principal methods Γ

theorem frozen_typing_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (site : Site Row) (receiver : CoreExpr) (c : Comp m) :
    (match freeze site with
      | none => False
      | some reference => QualifiedInference.Typing m methods theory Γ (lower reference receiver) c) ↔
      DotTyping m methods theory Γ site receiver c := by
  unfold DotTyping
  simp only [← MethodResolution.freeze_exact]
  cases freeze site with
  | none => simp
  | some reference => simp [lower_exact]

/-- Selection followed by the real core generator is exact for the independent
selection-and-typing rules, for every model and predicate theory. -/
theorem generateDot_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m theory ρ sΓ Γ) (site : Site Row) (receiver : CoreExpr) (out : CompTerm α) :
    (generateDot methods sΓ site receiver out).Holds m theory ρ ↔
      DotTyping m methods theory Γ site receiver (out.eval m ρ) := by
  rw [← frozen_typing_exact]
  cases selected : freeze site with
  | none => simp [generateDot, selected, Formula.Holds]
  | some reference =>
      simp only [generateDot, selected]
      exact QualifiedInference.generate_models_iff_typing m methods theory
        (lower reference receiver) sΓ Γ ρ out henv

theorem principalDot_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m theory ρ sΓ Γ) (site : Site Row) (receiver : CoreExpr) (c : Comp m) :
    (principalDot methods sΓ site receiver).Holds m theory (extend ρ c) ↔
      DotTyping m methods theory Γ site receiver c := by
  rw [← frozen_typing_exact]
  cases selected : freeze site with
  | none => simp [principalDot, selected, Formula.Holds]
  | some reference =>
      simp only [principalDot, selected]
      exact QualifiedInference.principal_exact m methods theory
        (lower reference receiver) sΓ Γ ρ henv c

theorem FrozenDot.constraints_exact (dot : FrozenDot) (m : Model) (methods : MethodTable)
    (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m theory ρ sΓ Γ) (out : CompTerm α) :
    (dot.constraints methods sΓ out).Holds m theory ρ ↔
      ReferenceTyping m methods theory Γ dot.reference dot.receiver (out.eval m ρ) :=
  (QualifiedInference.generate_models_iff_typing m methods theory dot.body sΓ Γ ρ out henv).trans
    (lower_exact m methods theory Γ dot.reference dot.receiver (out.eval m ρ))

/-- Substitution interprets the saved formula at the new environment, while
keeping exactly the frozen field or method rule. No caller lookup appears. -/
theorem FrozenDot.substitution_exact (dot : FrozenDot) (m : Model) (methods : MethodTable)
    (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (substitution : α → CompTerm β) (ρ : β → Comp m)
    (henv : EnvRel m theory (fun x => (substitution x).eval m ρ) sΓ Γ) (out : CompTerm α) :
    ((dot.constraints methods sΓ out).subst substitution).Holds m theory ρ ↔
      ReferenceTyping m methods theory Γ dot.reference dot.receiver
        (out.eval m (fun x => (substitution x).eval m ρ)) :=
  (Formula.holds_subst m theory _ substitution ρ).trans
    (dot.constraints_exact m methods theory sΓ Γ _ henv out)

theorem FrozenDot.principal_instance_exact (dot : FrozenDot) (m : Model) (methods : MethodTable)
    (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m theory ρ sΓ Γ) (out : CompTerm α) :
    ((dot.principal methods sΓ).instantiate out).Holds m theory ρ ↔
      ReferenceTyping m methods theory Γ dot.reference dot.receiver (out.eval m ρ) :=
  (QualifiedInference.Scheme.holds_instantiate m theory ρ _ out).trans
    ((QualifiedInference.principal_exact m methods theory dot.body sΓ Γ ρ henv (out.eval m ρ)).trans
      (lower_exact m methods theory Γ dot.reference dot.receiver (out.eval m ρ)))

/-- Simultaneously substitute every captured slot and the principal result
slot. The resulting contract still contains the original reference. -/
theorem FrozenDot.principal_substitution_exact (dot : FrozenDot) (m : Model) (methods : MethodTable)
    (theory : Theory m) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (substitution : Option α → CompTerm β) (ρ : β → Comp m)
    (henv : EnvRel m theory (fun x => (substitution (some x)).eval m ρ) sΓ Γ) :
    ((dot.principal methods sΓ).subst substitution).Holds m theory ρ ↔
      ReferenceTyping m methods theory Γ dot.reference dot.receiver ((substitution none).eval m ρ) := by
  rw [Formula.holds_subst]
  have environment : (fun x => (substitution x).eval m ρ) =
      extend (fun x => (substitution (some x)).eval m ρ) ((substitution none).eval m ρ) := by
    funext x
    cases x <;> rfl
  rw [environment]
  exact (QualifiedInference.principal_exact m methods theory dot.body sΓ Γ _ henv _).trans
    (lower_exact m methods theory Γ dot.reference dot.receiver _)

/-- Every predicate from a selected declaration still needs evidence after
arbitrary substitution, including when the concrete receiver has a same-named
field. The goal is a member of the actual method declaration, not an extra gate. -/
theorem frozen_role_substitution_requires (m : Model) (methods : MethodTable) (theory : Theory m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (substitution : α → CompTerm β) (ρ : β → Comp m)
    (henv : EnvRel m theory (fun x => (substitution x).eval m ρ) sΓ Γ)
    (role declaration : Nat) (receiver : CoreExpr) (out : CompTerm α)
    (goal : Goal (Fin (methods declaration).locals))
    (required : goal ∈ (methods declaration).requirements)
    (accepted : (((FrozenDot.mk (.role role declaration) receiver).constraints methods sΓ out).subst
      substitution).Holds m theory ρ) :
    ∃ ι : Fin (methods declaration).locals → m.Ty,
      theory (goal.eval m (QualifiedInference.typeEnv m ι)) := by
  have call := ((FrozenDot.mk (.role role declaration) receiver).substitution_exact
    m methods theory sΓ Γ substitution ρ henv out).mp accepted
  obtain ⟨ι, _, _, _, requirements, _⟩ := call
  exact ⟨ι, requirements _ (List.mem_map.mpr ⟨goal, required, rfl⟩)⟩

theorem frozen_role_principal_requires (m : Model) (methods : MethodTable) (theory : Theory m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : EnvRel m theory ρ sΓ Γ) (role declaration : Nat) (receiver : CoreExpr) (out : CompTerm α)
    (goal : Goal (Fin (methods declaration).locals))
    (required : goal ∈ (methods declaration).requirements)
    (accepted : (((FrozenDot.mk (.role role declaration) receiver).principal methods sΓ).instantiate out).Holds
      m theory ρ) :
    ∃ ι : Fin (methods declaration).locals → m.Ty,
      theory (goal.eval m (QualifiedInference.typeEnv m ι)) := by
  have call := ((FrozenDot.mk (.role role declaration) receiver).principal_instance_exact
    m methods theory sΓ Γ ρ henv out).mp accepted
  obtain ⟨ι, _, _, _, requirements, _⟩ := call
  exact ⟨ι, requirements _ (List.mem_map.mpr ⟨goal, required, rfl⟩)⟩

end Yulang.FrozenMethods
