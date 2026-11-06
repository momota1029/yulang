import Yulang.MultiOperationHandlers
import Yulang.MultiOperationPayloadHandlers
import Yulang.StrictApplication

/-!
# A resolved expression kernel with multi-operation shallow handlers

Total handlers have a finite table of distinct operation identities. Partial
handlers have an ordered table of resolved payload tests, may repeat a key,
and subtract only keys with an unguarded irrefutable arm (Q1). Both have a
body for each table entry and exactly one value arm. Operation bodies receive the
payload and original continuation through the same de Bruijn environment as
`OperationalTyping`; the continuation keeps the entire input row. The typing
judgement is defined independently of both evaluation and semantic bounds.

Ordinary application is strict in written order (decision 43). Existing
resolved syntax embeds through its proved strict-application lowering.
This module proves safety from syntax typing, without assuming semantic
bounds for action or arm bodies. It does not claim a source elaborator,
unresolved-shape inference, operation-local polymorphism, or recursion
termination. The atom carrier is the existing uniform payload/response model.
-/

namespace Yulang.MultiOperationHandlerTyping

open Directed OperationalTyping MultiOperationHandlers

variable {n count : Nat} {Key Atom : Type}

def collectRows (rows : Fin count → Row n Key) : Row n Key :=
  (List.ofFn rows).flatten

@[simp] theorem mem_collectRows (rows : Fin count → Row n Key) (occurrence : Occurrence n Key) :
    occurrence ∈ collectRows rows ↔ ∃ index, occurrence ∈ rows index := by
  simp only [collectRows, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨row, ⟨index, rfl⟩, member⟩
    exact ⟨index, member⟩
  · rintro ⟨index, member⟩
    exact ⟨rows index, ⟨index, rfl⟩, member⟩

/-- The semantic composition lemma is subsequently discharged from the
independent syntax typing of every actual arm. -/
theorem handle_valid [DecidableEq Key] (operations : Operations Key count)
    (input : CTy n Key a) (output : VTy n Key b)
    (returnRow : Row n Key) (operationRows : Fin count → Row n Key)
    (onReturn : Value n Key Atom a → Tree n Key Atom b)
    (onOperation : Fin count → Atom → (Atom → Tree n Key Atom a) → Tree n Key Atom b)
    (returnValid : ∀ value, ValidValue input.value value →
      Valid (⟨output, returnRow⟩ : CTy n Key b) (onReturn value))
    (operationValid : ∀ index payload resume,
      (∀ response, Valid input (resume response)) →
      Valid (⟨output, operationRows index⟩ : CTy n Key b) (onOperation index payload resume))
    (action : Tree n Key Atom a) (inputValid : Valid input action) :
    Valid (⟨output, residual operations.keys input.row ++
        (returnRow ++ collectRows operationRows)⟩ : CTy n Key b)
      (handle operations onReturn onOperation action) := by
  induction action with
  | pure value =>
      exact valid_mono_values (left := ⟨output, returnRow⟩)
        (right := ⟨output, residual operations.keys input.row ++
          (returnRow ++ collectRows operationRows)⟩) (fun _ good => good)
        (fun _ member => List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
        (returnValid value inputValid.2)
  | request occurrence payload resume ih =>
      have resumeValid (response : Atom) : Valid input (resume response) :=
        ⟨inputValid.1.2 response, inputValid.2 response⟩
      by_cases captured : Capturable operations.keys occurrence
      · simp only [handle, captured, ↓reduceDIte]
        let index := operations.select occurrence.key captured.1
        exact valid_mono_values (left := ⟨output, operationRows index⟩)
          (right := ⟨output, residual operations.keys input.row ++
            (returnRow ++ collectRows operationRows)⟩) (fun _ good => good)
          (fun occurrence member => List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inr ((mem_collectRows operationRows occurrence).mpr ⟨index, member⟩)))))
          (operationValid index payload resume resumeValid)
      · simp only [handle, captured, ↓reduceDIte]
        refine ⟨⟨?_, fun response => (ih response (resumeValid response)).1⟩,
          fun response => (ih response (resumeValid response)).2⟩
        apply List.mem_append.mpr
        left
        simpa [residual, captured] using inputValid.1.1

/-- Partial payload dispatch removes only certified total keys. In particular,
the missed request belongs to the residual even though its key has an arm. -/
theorem partial_handle_valid [DecidableEq Key]
    (arms : Fin count → MultiOperationPayloadHandlers.Arm Key Atom)
    (input : CTy n Key a) (output : VTy n Key b)
    (returnRow : Row n Key) (operationRows : Fin count → Row n Key)
    (onReturn : Value n Key Atom a → Tree n Key Atom b)
    (onArm : Fin count → Atom → (Atom → Tree n Key Atom a) → Tree n Key Atom b)
    (returnValid : ∀ value, ValidValue input.value value →
      Valid (⟨output, returnRow⟩ : CTy n Key b) (onReturn value))
    (armValid : ∀ index payload resume,
      (∀ response, Valid input (resume response)) →
      Valid (⟨output, operationRows index⟩ : CTy n Key b) (onArm index payload resume))
    (action : Tree n Key Atom a) (inputValid : Valid input action) :
    Valid (⟨output, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
        (returnRow ++ collectRows operationRows)⟩ : CTy n Key b)
      (MultiOperationPayloadHandlers.handle arms onReturn onArm action) := by
  induction action with
  | pure value =>
      exact valid_mono_values (left := ⟨output, returnRow⟩)
        (right := ⟨output, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
          (returnRow ++ collectRows operationRows)⟩) (fun _ good => good)
        (fun _ member => List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
        (returnValid value inputValid.2)
  | request occurrence payload resume ih =>
      have resumeValid (response : Atom) : Valid input (resume response) :=
        ⟨inputValid.1.2 response, inputValid.2 response⟩
      cases selected : MultiOperationPayloadHandlers.select arms occurrence payload with
      | some index =>
          simp only [MultiOperationPayloadHandlers.handle, selected]
          exact valid_mono_values (left := ⟨output, operationRows index⟩)
            (right := ⟨output, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
              (returnRow ++ collectRows operationRows)⟩) (fun _ good => good)
            (fun occurrence member => List.mem_append.mpr (Or.inr (List.mem_append.mpr
              (Or.inr ((mem_collectRows operationRows occurrence).mpr ⟨index, member⟩)))))
            (armValid index payload resume resumeValid)
      | none =>
          simp only [MultiOperationPayloadHandlers.handle, selected]
          refine ⟨⟨?_, fun response => (ih response (resumeValid response)).1⟩,
            fun response => (ih response (resumeValid response)).2⟩
          exact List.mem_append.mpr (Or.inl
            (MultiOperationPayloadHandlers.missed_retained arms input.row occurrence payload inputValid.1.1 selected))

inductive Expr (n : Nat) (Key Atom : Type) : List Shape → Shape → Type where
  | core : OperationalTyping.Expr n Key Atom Γ s → Expr n Key Atom Γ s
  | lam : CTy n Key a → Expr n Key Atom (a :: Γ) b → Expr n Key Atom Γ (.arrow a b)
  | app : Expr n Key Atom Γ (.arrow a b) → Expr n Key Atom Γ a → Expr n Key Atom Γ b
  | pair : Expr n Key Atom Γ a → Expr n Key Atom Γ b → Expr n Key Atom Γ (.pair a b)
  | fst : Expr n Key Atom Γ (.pair a b) → Expr n Key Atom Γ a
  | snd : Expr n Key Atom Γ (.pair a b) → Expr n Key Atom Γ b
  | letE : Expr n Key Atom Γ a → Expr n Key Atom (a :: Γ) b → Expr n Key Atom Γ b
  | request : Key → Expr n Key Atom Γ .atom → Expr n Key Atom Γ .atom
  | boundary : Boundary n Key → Expr n Key Atom Γ s → Expr n Key Atom Γ s
  | handler {count : Nat} : Operations Key count → VTy n Key b → Expr n Key Atom Γ a →
      Expr n Key Atom (a :: Γ) b →
      (Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: Γ) b) → Expr n Key Atom Γ b
  | partialHandler {count : Nat} : (Fin count → MultiOperationPayloadHandlers.Arm Key Atom) →
      VTy n Key b → Expr n Key Atom Γ a → Expr n Key Atom (a :: Γ) b →
      (Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: Γ) b) → Expr n Key Atom Γ b
  | widen : CTy n Key s → Expr n Key Atom Γ s → Expr n Key Atom Γ s

def Expr.var (index : Var Γ s) : Expr n Key Atom Γ s := .core (.var index)
def Expr.lit (value : Atom) : Expr n Key Atom Γ .atom := .core (.lit value)

def eval [DecidableEq Key] (runtime : Env (Tree n Key Atom) Γ) :
    Expr n Key Atom Γ s → Tree n Key Atom s
  | .core expression => StrictApplication.eval runtime expression
  | .lam _ body => .pure (fun argument => eval (Env.cons argument runtime) body)
  | .app function argument => (eval runtime function).bind fun f =>
      (eval runtime argument).bind fun value => f (.pure value)
  | .pair left right => (eval runtime left).bind fun a =>
      (eval runtime right).bind fun b => .pure (a, b)
  | .fst pair => (eval runtime pair).bind fun value => .pure value.1
  | .snd pair => (eval runtime pair).bind fun value => .pure value.2
  | .letE value body => (eval runtime value).bind fun v => eval (Env.cons (.pure v) runtime) body
  | .request key payload => (eval runtime payload).bind fun value =>
      .request (raw key) value (fun response => .pure response)
  | .boundary boundary body => Computation.mapRequests boundary.transform (eval runtime body)
  | .handler operations _ action onReturn onOperation =>
      handle operations
        (fun value => eval (Env.cons (.pure value) runtime) onReturn)
        (fun index payload resume =>
          eval (Env.cons (s := .atom) (.pure payload)
            (Env.cons (s := .arrow .atom _) (.pure (fun argument => argument.bind resume)) runtime))
            (onOperation index))
        (eval runtime action)
  | .partialHandler arms _ action onReturn onArm =>
      MultiOperationPayloadHandlers.handle arms
        (fun value => eval (Env.cons (.pure value) runtime) onReturn)
        (fun index payload resume =>
          eval (Env.cons (s := .atom) (.pure payload)
            (Env.cons (s := .arrow .atom _) (.pure (fun argument => argument.bind resume)) runtime))
            (onArm index))
        (eval runtime action)
  | .widen _ body => eval runtime body

/-- This judgement mentions neither evaluation nor any semantic safety
predicate. Operation arms retain the complete input computation type. -/
inductive Typing [DecidableEq Key] : {Γ : List Shape} →
    Env (CTy n Key) Γ → {s : Shape} → Expr n Key Atom Γ s → CTy n Key s → Prop where
  | core : OperationalTyping.Typing types (StrictApplication.compile expression) output →
      Typing types (.core expression) output
  | lam : Typing (Env.cons input types) body output →
      Typing types (.lam input body) (CTy.pure (CTy.arrow input output))
  | app : Typing types function ⟨CTy.arrow input output, functionRow⟩ →
      Typing types argument actual → CLe (CTy.pure actual.value) input →
      Typing types (.app function argument)
        ⟨output.value, functionRow ++ (actual.row ++ output.row)⟩
  | pair : Typing types left a → Typing types right b →
      Typing types (.pair left right) ⟨.pair a.value b.value, a.row ++ b.row⟩
  | fst : Typing types pair ⟨.pair a b, row⟩ → Typing types (.fst pair) ⟨a, row⟩
  | snd : Typing types pair ⟨.pair a b, row⟩ → Typing types (.snd pair) ⟨b, row⟩
  | letE : Typing types value input → Typing (Env.cons (CTy.pure input.value) types) body output →
      Typing types (.letE value body) ⟨output.value, input.row ++ output.row⟩
  | request : Typing types payload ⟨.atom, row⟩ →
      Typing types (.request key payload) ⟨.atom, row ++ [raw key]⟩
  | boundary : Typing types body input →
      Typing types (.boundary boundary body) ⟨input.value, boundary.row input.row⟩
  | handler {count : Nat} {operations : Operations Key count}
      {onOperation : Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: Γ) b}
      {operated : Fin count → CTy n Key b} :
      Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      (∀ index, Typing (operationTypes types input) (onOperation index) (operated index)) →
      VLe returned.value target → (∀ index, VLe (operated index).value target) →
      Typing types (.handler operations target action onReturn onOperation)
        ⟨target, residual operations.keys input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩
  | partialHandler {count : Nat} {arms : Fin count → MultiOperationPayloadHandlers.Arm Key Atom}
      {onArm : Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: Γ) b}
      {operated : Fin count → CTy n Key b} :
      Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      (∀ index, Typing (operationTypes types input) (onArm index) (operated index)) →
      VLe returned.value target → (∀ index, VLe (operated index).value target) →
      Typing types (.partialHandler arms target action onReturn onArm)
        ⟨target, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩
  | widen : Typing types body input → CLe input target →
      Typing types (.widen target body) target

/-- Every action/arm bound is derived from its syntax typing. The only
semantic premise is validity of an open program's external environment. -/
theorem typing_evaluates [DecidableEq Key] {types : Env (CTy n Key) Γ}
    {expression : Expr n Key Atom Γ s} {output : CTy n Key s}
    (typed : Typing types expression output) :
    ∀ runtime : Env (Tree n Key Atom) Γ, EnvValid types runtime →
      Valid output (eval runtime expression) := by
  induction typed with
  | core typed =>
      intro runtime good
      rw [eval, ← StrictApplication.compile_correct]
      exact OperationalTyping.typing_sound typed runtime good
  | lam typed ih =>
      intro runtime good
      apply valid_pure
      intro argument bounded returned
      exact ih _ (good.cons ⟨bounded, returned⟩)
  | app functionTyped argumentTyped compatible ihf iha =>
      intro runtime good
      simp only [eval]
      refine valid_bind (output := ⟨_, _⟩) (ihf runtime good) ?_
      intro function functionValid
      apply valid_bind (iha runtime good)
      intro value valueValid
      have argumentValid := subtype_sound compatible (valid_pure _ _ valueValid)
      exact functionValid _ argumentValid.1 argumentValid.2
  | pair leftTyped rightTyped ihl ihr =>
      intro runtime good
      exact valid_pair (ihl runtime good) (ihr runtime good)
  | fst pairTyped ih => intro runtime good; exact valid_fst (ih runtime good)
  | snd pairTyped ih => intro runtime good; exact valid_snd (ih runtime good)
  | letE valueTyped bodyTyped ihv ihb =>
      intro runtime good
      apply valid_bind (ihv runtime good)
      intro value valueValid
      exact ihb _ (good.cons (valid_pure _ _ valueValid))
  | request payloadTyped ih => intro runtime good; exact valid_request _ (ih runtime good)
  | boundary bodyTyped ih => intro runtime good; exact valid_mapRequests _ (ih runtime good)
  | handler actionTyped returnTyped operationTyped returnSubtype operationSubtype iha ihr iho =>
      intro runtime good
      apply handle_valid
      · intro value valueValid
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ returnSubtype v hv)
          (SignedStructural.row_refl _) (ihr _ (good.cons (valid_pure _ _ valueValid)))
      · intro index payload resume resumeGood
        have continuation := valid_pure _ _ (valid_resumption _ resume resumeGood)
        have payloadGood := valid_pure (.atom : VTy n Key .atom) payload trivial
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ (operationSubtype index) v hv)
          (SignedStructural.row_refl _)
          (iho index _ (EnvValid.cons (EnvValid.cons good continuation) payloadGood))
      · exact iha runtime good
  | partialHandler actionTyped returnTyped operationTyped returnSubtype operationSubtype iha ihr iho =>
      intro runtime good
      apply partial_handle_valid
      · intro value valueValid
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ returnSubtype v hv)
          (SignedStructural.row_refl _) (ihr _ (good.cons (valid_pure _ _ valueValid)))
      · intro index payload resume resumeGood
        have continuation := valid_pure _ _ (valid_resumption _ resume resumeGood)
        have payloadGood := valid_pure (.atom : VTy n Key .atom) payload trivial
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ (operationSubtype index) v hv)
          (SignedStructural.row_refl _)
          (iho index _ (EnvValid.cons (EnvValid.cons good continuation) payloadGood))
      · exact iha runtime good
  | widen bodyTyped compatible ih =>
      intro runtime good
      exact subtype_sound compatible (ih runtime good)

theorem closed_typed_bound [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CTy n Key s)
    (typed : Typing Env.nil expression output) :
    Computation.BoundedBy output.row (eval Env.nil expression) :=
  (typing_evaluates typed Env.nil (fun index => nomatch index)).1

theorem closed_typed_values [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CTy n Key s)
    (typed : Typing Env.nil expression output) :
    AllReturns (ValidValue output.value) (eval Env.nil expression) :=
  (typing_evaluates typed Env.nil (fun index => nomatch index)).2

/-- A closed, typed expression with no residual operations evaluates to a
returned value. This concerns the finite resolved syntax, not source recursion. -/
theorem closed_empty_row_returns [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (valueType : VTy n Key s)
    (typed : Typing Env.nil expression ⟨valueType, []⟩) :
    ∃ value, eval Env.nil expression = .pure value ∧ ValidValue valueType value := by
  have valid := typing_evaluates typed Env.nil (fun index => nomatch index)
  cases evaluated : eval Env.nil expression with
  | pure value => exact ⟨value, rfl, by simpa [evaluated, Valid, AllReturns] using valid.2⟩
  | request occurrence payload resume =>
      rw [evaluated] at valid
      have impossible : occurrence ∈ ([] : Row n Key) := valid.1.1
      cases impossible

end Yulang.MultiOperationHandlerTyping
