import Yulang.OperationalTyping

/-!
# Executable examples for the checked operational fragment

These examples run both the independent checker and the request-tree evaluator.
Each inferred bound is obtained from `closed_inferred_bound`, with no separate
assumptions about the action or handler arms.

The expressions already have resolved shapes and explicit boundary operations.
In particular, the permission granted to `handledArgument` is intentional;
these examples do not choose the source elaborator's default hygiene policy.
A boundary around a returned pair transforms its immediate request tree only.
It does not insert a latent-function wrapper into the stored callback.
-/

namespace Yulang.OperationalTypingExamples

open Directed OperationalTyping

abbrev Program (shape : Shape) := Expr 1 Nat Nat [] shape

def atomPure : CTy 1 Nat .atom := CTy.pure .atom
def atomEffect : CTy 1 Nat .atom := ⟨.atom, [raw 0]⟩
def atomTwoEffects : CTy 1 Nat .atom := ⟨.atom, [raw 0, raw 0]⟩

/-! ## Computation arguments may be unused or handled by the function -/

def unusedArgument : Program .atom :=
  .app (.lam atomEffect (.lit 7)) (.request 0 (.lit 2))

theorem unusedArgument_infer : infer Env.nil unusedArgument = some atomPure := rfl

theorem unusedArgument_eval : eval Env.nil unusedArgument = .pure (7 : Nat) := rfl

theorem unusedArgument_bound :
    Computation.BoundedBy [] (eval Env.nil unusedArgument) :=
  closed_inferred_bound unusedArgument atomPure unusedArgument_infer

/-- The function explicitly permits this occurrence at its boundary. -/
def handledArgument : Program .atom :=
  .app
    (.lam atomEffect
      (.handler 0 .atom
        (.boundary (.protect 0 allowAll) (.var .here))
        (.var .here) (.lit 8)))
    (.request 0 (.lit 2))

theorem handledArgument_infer : infer Env.nil handledArgument = some atomPure := rfl

theorem handledArgument_eval : eval Env.nil handledArgument = .pure (8 : Nat) := rfl

theorem handledArgument_bound :
    Computation.BoundedBy [] (eval Env.nil handledArgument) :=
  closed_inferred_bound handledArgument atomPure handledArgument_infer

/-! ## A shallow resumption retains the action's original row -/

def twoRequests : Expr 1 Nat Nat Γ .atom :=
  .letE (.request 0 (.lit 1)) (.request 0 (.lit 2))

def resumedAction : Program .atom :=
  .handler 0 .atom twoRequests (.var .here)
    (.app (.var (.there .here)) (.lit 3))

theorem resumedAction_infer : infer Env.nil resumedAction = some atomTwoEffects := rfl

/-- Only the first request is captured. The resumed second request is exposed. -/
theorem resumedAction_eval :
    eval Env.nil resumedAction = .request (raw 0) 2 (fun response => .pure response) := rfl

theorem resumedAction_bound :
    Computation.BoundedBy [raw 0, raw 0] (eval Env.nil resumedAction) :=
  closed_inferred_bound resumedAction atomTwoEffects resumedAction_infer

theorem resumedAction_not_pure_bound :
    ¬ Computation.BoundedBy [] (eval Env.nil resumedAction) := by
  rw [resumedAction_eval]
  exact fun bound => List.not_mem_nil bound.1

/-- Both calls use the same original continuation; neither reinstalls a handler. -/
def resumedTwice : Program (.pair .atom .atom) :=
  .handler 0 (.pair .atom .atom) twoRequests
    (.pair (.var .here) (.var .here))
    (.pair
      (.app (.var (.there .here)) (.lit 3))
      (.app (.var (.there .here)) (.lit 4)))

def resumedTwiceType : CTy 1 Nat (.pair .atom .atom) :=
  ⟨.pair .atom .atom, [raw 0, raw 0, raw 0, raw 0]⟩

theorem resumedTwice_infer : infer Env.nil resumedTwice = some resumedTwiceType := rfl

theorem resumedTwice_eval :
    eval Env.nil resumedTwice =
      .request (raw 0) 2 (fun first =>
        .request (raw 0) 2 (fun second => .pure (first, second))) := rfl

theorem resumedTwice_bound :
    Computation.BoundedBy resumedTwiceType.row (eval Env.nil resumedTwice) :=
  closed_inferred_bound resumedTwice resumedTwiceType resumedTwice_infer

/-! ## Arm effects are added after subtraction -/

def reemitFromArm : Program .atom :=
  .handler 0 .atom (.request 0 (.lit 1)) (.var .here) (.request 0 (.lit 9))

theorem reemitFromArm_infer : infer Env.nil reemitFromArm = some atomEffect := rfl

theorem reemitFromArm_eval :
    eval Env.nil reemitFromArm = .request (raw 0) 9 (fun response => .pure response) := rfl

theorem reemitFromArm_bound :
    Computation.BoundedBy [raw 0] (eval Env.nil reemitFromArm) :=
  closed_inferred_bound reemitFromArm atomEffect reemitFromArm_infer

theorem reemitFromArm_not_pure_bound :
    ¬ Computation.BoundedBy [] (eval Env.nil reemitFromArm) := by
  rw [reemitFromArm_eval]
  exact fun bound => List.not_mem_nil bound.1

/-! ## Stored callbacks retain their latent effects -/

def callbackPair : Program (.pair (.arrow .atom .atom) .atom) :=
  .pair (.lam atomPure (.request 0 (.lit 6))) (.lit 7)

def callbackPairType : CTy 1 Nat (.pair (.arrow .atom .atom) .atom) :=
  CTy.pure (.pair (CTy.arrow atomPure atomEffect) .atom)

theorem callbackPair_infer : infer Env.nil callbackPair = some callbackPairType := rfl

theorem callbackPair_bound :
    Computation.BoundedBy [] (eval Env.nil callbackPair) :=
  closed_inferred_bound callbackPair callbackPairType callbackPair_infer

theorem callbackPair_values :
    AllReturns (ValidValue callbackPairType.value) (eval Env.nil callbackPair) :=
  closed_inferred_values callbackPair callbackPairType callbackPair_infer

/-- Protecting the pair's immediate tree leaves its returned callback unchanged. -/
def useStoredCallback : Program .atom :=
  .app (.fst (.boundary (.protect 0 allowNone) callbackPair)) (.lit 0)

theorem useStoredCallback_infer : infer Env.nil useStoredCallback = some atomEffect := rfl

theorem useStoredCallback_eval :
    eval Env.nil useStoredCallback = .request (raw 0) 6 (fun response => .pure response) := rfl

theorem useStoredCallback_bound :
    Computation.BoundedBy [raw 0] (eval Env.nil useStoredCallback) :=
  closed_inferred_bound useStoredCallback atomEffect useStoredCallback_infer

/-! ## Negative release debt survives inference and a same-family handler -/

def indebted : Occurrence 1 Nat := release 0 allowNone (raw 0)
def indebtedType : CTy 1 Nat .atom := ⟨.atom, [indebted]⟩

def indebtedAction : Program .atom :=
  .handler 0 .atom
    (.boundary (.release 0 allowNone) (.request 0 (.lit 4)))
    (.var .here) (.lit 99)

theorem indebted_negative : indebted.weights 0 = -1 := rfl

theorem indebted_uncapturable : ¬ Capturable [0] indebted := by decide

theorem indebtedAction_infer : infer Env.nil indebtedAction = some indebtedType := rfl

theorem indebtedAction_eval :
    eval Env.nil indebtedAction = .request indebted 4 (fun response => .pure response) := rfl

theorem indebtedAction_bound :
    Computation.BoundedBy [indebted] (eval Env.nil indebtedAction) :=
  closed_inferred_bound indebtedAction indebtedType indebtedAction_infer

theorem indebtedAction_not_raw_bound :
    ¬ Computation.BoundedBy [raw 0] (eval Env.nil indebtedAction) := by
  rw [indebtedAction_eval]
  intro bound
  have equal : indebted = raw 0 := List.mem_singleton.mp bound.1
  have weights := congrArg (fun occurrence : Occurrence 1 Nat => occurrence.weights 0) equal
  contradiction

end Yulang.OperationalTypingExamples
