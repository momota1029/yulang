import Yulang.Structural

/-!
# Value restriction with suspended computation arguments

A syntactic variable can denote a computation argument. Failure to generalize
that variable must not reject an otherwise valid binding. These regressions
exercise the monomorphic fallback and the exact generated constraints.
-/

namespace Yulang.Polymorphism

open Inference Structural Effects

def io : Occurrence Nat := {key := 0}

def actionContext : List (Binding (model Nat)) := [.mono (.base .int, [io])]

/-- The body of `my result = action; ()`, with action at local index zero. -/
def bindAction : Expr := .letE (.var 0) (.lit .unit)

theorem bind_action_preserves_io :
    Typing (model Nat) actionContext bindAction (.base .unit, [io]) := by
  apply Typing.letComputed (m := model Nat)
    (a := (Ty.base .int, [io])) (b := (Ty.base .unit, []))
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact ⟨.refl _, row_refl _⟩

theorem action_typing_contains_io (c : Comp (model Nat))
    (typed : Typing (model Nat) actionContext (.var 0) c) : List.Mem io c.2 := by
  have bound : Comp.le (model Nat) (.base .int, [io]) c := by
    simpa [Typing.var_iff, BindingLookup, actionContext] using typed
  exact bound.2 io (by simp)

theorem bind_action_not_pure (result : Ty Nat) :
    ¬ Typing (model Nat) actionContext bindAction (result, []) := by
  intro typed
  rcases (Typing.letValue_iff (model Nat) actionContext (.var 0) (.lit .unit)
    (result, []) rfl).mp typed with generalized | monomorphic
  · rcases generalized.1 with ⟨a, ha⟩
    have impossible := action_typing_contains_io _ ha
    cases impossible
  · rcases monomorphic with ⟨a, b, ha, _, bound⟩
    have present : List.Mem io (List.append a.2 b.2) :=
      List.mem_append.mpr (Or.inl (action_typing_contains_io a ha))
    have impossible := bound.2 io present
    cases impossible

def symbolicContext : SchemeEnv Unit :=
  [Scheme.mono ⟨.base .int, .var ()⟩]

def assignment : Unit → Comp (model Nat) := fun _ => (.base .int, [io])

theorem context_related : EnvRel (model Nat) assignment symbolicContext actionContext := by
  simpa [symbolicContext, actionContext, assignment, CompTerm.eval, TyTerm.eval, RowTerm.eval,
    model, StructuralBase.model]
    using (EnvRel.nil (model Nat) assignment).mono (⟨.base .int, .var ()⟩ : CompTerm Unit)

theorem generated_effectful_alias_accepted :
    (generate symbolicContext bindAction ⟨.base .unit, .var ()⟩).Holds (model Nat) assignment := by
  apply (generate_models_iff_typing (model Nat) bindAction symbolicContext actionContext
    assignment _ context_related).mpr
  exact bind_action_preserves_io

theorem generated_effectful_alias_cannot_erase_io :
    ¬ (generate symbolicContext bindAction (CompTerm.pure (.base .unit))).Holds
      (model Nat) assignment := by
  intro checked
  have typed := (generate_models_iff_typing (model Nat) bindAction symbolicContext actionContext
    assignment _ context_related).mp checked
  exact bind_action_not_pure (.base .unit) typed

end Yulang.Polymorphism
