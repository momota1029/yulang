import Yulang.OperationalTransportTyping

/-!
# Runtime distinctions exercised by higher-order boundary transport

Every producer below is an `OperationalTyping.Expr` checked by the existing
`infer` and evaluated by the existing `eval`. The boundary wrappers are explicit
calls to `OperationalTransport.tree`; these examples do not invent a new source
boundary rule or claim that source elaboration inserts the wrappers already.

The regressions distinguish immediate requests from a callback stored in a pair,
contravariant transport of both a callback and its suspended producer, and an
inner allow-all mask from removal of an existing outer boundary's debt.
The mixed-owner invoker retains negative output debt; it is not an instance of
the zero-origin noncapture theorem.
-/

namespace Yulang.OperationalTransportExamples

open Directed OperationalTyping
open OperationalTransport (tree)

abbrev Program (shape : Shape) := Expr 1 Nat Nat [] shape
abbrev CallbackShape : Shape := .arrow .atom .atom
abbrev PairShape : Shape := .pair .atom CallbackShape
abbrev InvokerShape : Shape := .arrow CallbackShape .atom

def atomPure : CTy 1 Nat .atom := CTy.pure .atom
def atomEffect : CTy 1 Nat .atom := ⟨.atom, [raw 0]⟩
def callbackType : VTy 1 Nat CallbackShape := CTy.arrow atomPure atomEffect

def callback : Program CallbackShape :=
  .lam atomPure (.request 0 (.lit 7))

theorem callback_infer : infer Env.nil callback = some (CTy.pure callbackType) := rfl

def callbackPair : Program PairShape := .pair (.lit 42) callback

theorem callbackPair_infer :
    infer Env.nil callbackPair = some (CTy.pure (.pair .atom callbackType)) := rfl

/-- Applying the stored callback forces its body, after the pair is returned. -/
def invokePair (producer : Tree 1 Nat Nat PairShape) : Tree 1 Nat Nat .atom :=
  producer.bind (fun pair => pair.2 (.pure (0 : Nat)))

def inner (computation : Tree 1 Nat Nat .atom) : Tree 1 Nat Nat .atom :=
  computation.shallowHandle [0] .pure (fun _ _ _ => .pure (99 : Nat))

def outer (computation : Tree 1 Nat Nat .atom) : Tree 1 Nat Nat .atom :=
  computation.shallowHandle [0] .pure (fun _ payload _ => .pure payload)

/-! ## A boundary around the immediate pair does not protect its callback -/

def immediateOnly : Program .atom :=
  .app (.snd (.boundary (.protect 0 allowNone) callbackPair)) (.lit 0)

theorem immediateOnly_infer : infer Env.nil immediateOnly = some atomEffect := rfl

theorem immediateOnly_eval :
    eval Env.nil immediateOnly = .request (raw 0) 7 (fun response => .pure response) := rfl

theorem immediateOnly_callback_is_captured :
    inner (eval Env.nil immediateOnly) = .pure (99 : Nat) := rfl

def protectedPair : Tree 1 Nat Nat PairShape :=
  tree 0 allowNone PairShape .guard (eval Env.nil callbackPair)

def protectedOccurrence : Occurrence 1 Nat := protect 0 allowNone (raw 0)

theorem protectedPair_callback_request :
    invokePair protectedPair =
      .request protectedOccurrence 7 (fun response => .pure response) := rfl

/-- The inner handler cannot steal the callback just because the pair itself
returned without producing a request. -/
theorem protectedPair_callback_is_not_captured :
    inner (invokePair protectedPair) =
      .request protectedOccurrence 7 (fun response => .pure response) := rfl

/-- The matching outward release restores dispatch to the caller's handler,
after the protected callback has passed through the inner handler. -/
theorem matching_release_restores_caller :
    outer (tree 0 allowNone .atom .release (inner (invokePair protectedPair))) =
      .pure (7 : Nat) := rfl

/-- Releasing the returned pair also restores the original latent callback. -/
theorem returned_pair_roundtrip_restores_callback :
    invokePair (tree 0 allowNone PairShape .release protectedPair) =
      invokePair (eval Env.nil callbackPair) := by
  exact congrArg invokePair
    (OperationalTransport.tree_opposite 0 allowNone PairShape .guard (eval Env.nil callbackPair))

/-! ## Higher-order inputs are suspended computations, including their effects -/

def localDebt : Occurrence 1 Nat := release 0 allowNone (raw 0)

/-- The invoker accepts visible requests and negative boundary debt, both while
producing its callback and while running that callback. This includes a local
raw callback after contravariant release, rather than applying a raw-only
interface outside its declared input domain. -/
def callbackArgument : CTy 1 Nat CallbackShape :=
  ⟨CTy.arrow atomPure ⟨.atom, [raw 0, localDebt]⟩, [raw 0, localDebt]⟩

/-- The inner handler removes raw requests but must retain both debt entries. -/
def invokerOutput : CTy 1 Nat .atom := ⟨.atom, [localDebt, localDebt]⟩

def invoker : Program InvokerShape :=
  .lam callbackArgument
    (.handler 0 .atom (.app (.var .here) (.lit 0))
      (.var .here) (.lit 99))

theorem invoker_infer :
    infer Env.nil invoker = some (CTy.pure (CTy.arrow callbackArgument invokerOutput)) := rfl

def directCall : Program .atom := .app invoker callback

theorem directCall_infer : infer Env.nil directCall = some invokerOutput := rfl

theorem directCall_eval : eval Env.nil directCall = .pure (99 : Nat) := rfl

def applyTrees (function : Tree 1 Nat Nat (.arrow a b)) (argument : Tree 1 Nat Nat a) :
    Tree 1 Nat Nat b := function.bind (fun f => f argument)

def protectedInvoker : Tree 1 Nat Nat InvokerShape :=
  tree 0 allowNone InvokerShape .guard (eval Env.nil invoker)

/-- The unshifted local callback is compatible with the transported interface:
the negative input alternative becomes raw after protection. -/
theorem callback_fits_protected_invoker :
    checkC (CTy.pure callbackType)
      (OperationalTransportTyping.ctype 0 allowNone .guard callbackArgument) = true := rfl

/-- Cancellation restores visible effects in the output interface too; the
guarded invoker's inferred result is not incorrectly declared pure. -/
theorem protected_invoker_output_keeps_raw :
    OperationalTransportTyping.ctype 0 allowNone .guard invokerOutput =
      (⟨.atom, [raw 0, raw 0]⟩ : CTy 1 Nat .atom) := by
  change (⟨.atom, [protect 0 allowNone localDebt, protect 0 allowNone localDebt]⟩ :
    CTy 1 Nat .atom) = _
  simp only [localDebt, protect_release]

/-- The input wrapper creates negative debt around the local callback before
the inner handler runs; the output wrapper cancels it at the caller boundary. -/
theorem contravariant_callback_reaches_caller :
    outer (applyTrees protectedInvoker (eval Env.nil callback)) = .pure (7 : Nat) := rfl

def delayedCallback : Program CallbackShape :=
  .letE (.request 0 (.lit 13)) (.lam atomPure (.request 0 (.lit 7)))

def delayedCallbackType : CTy 1 Nat CallbackShape := ⟨callbackType, [raw 0]⟩

theorem delayedCallback_infer : infer Env.nil delayedCallback = some delayedCallbackType := rfl

theorem delayedCallback_fits_protected_invoker :
    checkC delayedCallbackType
      (OperationalTransportTyping.ctype 0 allowNone .guard callbackArgument) = true := rfl

theorem directDelayedCall_eval :
    eval Env.nil (.app invoker delayedCallback) = .pure (99 : Nat) := rfl

/-- A wrapper of the callback value alone would miss this first request: it
occurs while the suspended argument is producing the callback. -/
theorem contravariant_argument_request_reaches_caller :
    outer (applyTrees protectedInvoker (eval Env.nil delayedCallback)) = .pure (13 : Nat) := rfl

/-! ## Allow-all applies at the selected boundary only -/

def outerDebt : Occurrence 2 Nat := release 0 allowNone (raw 0)

def indebted : Expr 2 Nat Nat [] .atom :=
  .boundary (.release 0 allowNone) (.request 0 (.lit 19))

theorem indebted_infer : infer Env.nil indebted = some (⟨.atom, [outerDebt]⟩ : CTy 2 Nat .atom) :=
  rfl

theorem indebted_eval :
    eval Env.nil indebted = .request outerDebt 19 (fun response => .pure response) := rfl

theorem outer_debt_is_negative : outerDebt.weights 0 = -1 := rfl

theorem outer_debt_is_not_inner_debt : outerDebt.weights 1 = 0 := rfl

theorem allowAll_keeps_outer_debt :
    tree 1 allowAll .atom .guard (eval Env.nil indebted) = eval Env.nil indebted := by
  rw [indebted_eval]
  simp only [OperationalTransport.tree_request]
  congr 1
  exact glob_has_no_transport 1 1 outerDebt

/-- Permitting every family at the inner boundary neither cancels an outer
debt nor allows a same-family handler to capture it. -/
theorem allowAll_cannot_capture_outer_debt :
    Computation.shallowHandle [0] Computation.pure (fun _ _ _ => .pure (99 : Nat))
      (tree 1 allowAll .atom .guard (eval Env.nil indebted)) =
        .request outerDebt 19 (fun response => .pure response) := by
  rw [allowAll_keeps_outer_debt, indebted_eval]
  rfl

end Yulang.OperationalTransportExamples
