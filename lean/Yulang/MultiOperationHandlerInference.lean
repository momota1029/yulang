import Yulang.MultiOperationHandlerTyping

/-!
# Executable inference for the resolved multi-operation kernel

The finite operation table is checked arm by arm. The resumption's input row
is the original action row, including operations handled by this delimiter.
`infer_exact` proves equivalence to the independently defined syntax typing;
`inferred_operationally_valid` therefore needs no arm/action safety hypotheses.
This is resolved monomorphic inference with annotated lambda inputs and
handler value targets, not whole-source principal inference.
-/

namespace Yulang.MultiOperationHandlerTyping

open Directed OperationalTyping MultiOperationHandlers

/-- Sequencing a finite family preserves its index, including the empty table. -/
def collectOptions {A : Type} : {count : Nat} → (Fin count → Option A) → Option (Fin count → A)
  | 0, _ => some (fun index => nomatch index)
  | count + 1, choices => do
      let first ← choices 0
      let rest ← collectOptions (fun index : Fin count => choices index.succ)
      return Fin.cases first rest

theorem collectOptions_complete {A : Type} {count : Nat}
    (choices : Fin count → Option A) (values : Fin count → A)
    (success : ∀ index, choices index = some (values index)) :
    collectOptions choices = some values := by
  induction count with
  | zero =>
      have equal : (fun index : Fin 0 => nomatch index) = values := by
        funext index
        exact index.elim0
      simp [collectOptions, equal]
  | succ count ih =>
      have tail := ih (fun index => choices index.succ) (fun index => values index.succ)
        (fun index => success index.succ)
      have equal : Fin.cases (values 0) (fun index => values index.succ) = values := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      simp [collectOptions, success 0, tail, equal]

theorem collectOptions_sound {A : Type} {count : Nat}
    (choices : Fin count → Option A) (values : Fin count → A)
    (success : collectOptions choices = some values) :
    ∀ index, choices index = some (values index) := by
  induction count with
  | zero => intro index; exact index.elim0
  | succ count ih =>
      cases first : choices 0 with
      | none => simp [collectOptions, first] at success
      | some head =>
          cases rest : collectOptions (fun index : Fin count => choices index.succ) with
          | none => simp [collectOptions, first, rest] at success
          | some tail =>
              have equal : Fin.cases head tail = values := by
                simpa [collectOptions, first, rest] using success
              cases equal
              intro index
              refine Fin.cases ?_ (fun index => ?_) index
              · exact first
              · exact ih _ _ rest index

def infer [DecidableEq Key] (types : Env (CTy n Key) Γ) :
    Expr n Key Atom Γ s → Option (CTy n Key s)
  | .core expression => StrictApplication.infer types expression
  | .lam input body => do
      let output ← infer (Env.cons input types) body
      return CTy.pure (CTy.arrow input output)
  | .app function argument => do
      let ⟨.arrow a ea b eb, functionRow⟩ ← infer types function
      let actual ← infer types argument
      if checkC (CTy.pure actual.value) ⟨a, ea⟩ then
        return ⟨b, functionRow ++ (actual.row ++ eb)⟩
      else none
  | .pair left right => do
      let a ← infer types left
      let b ← infer types right
      return ⟨.pair a.value b.value, a.row ++ b.row⟩
  | .fst pair => do
      let ⟨.pair a _, row⟩ ← infer types pair
      return ⟨a, row⟩
  | .snd pair => do
      let ⟨.pair _ b, row⟩ ← infer types pair
      return ⟨b, row⟩
  | .letE value body => do
      let input ← infer types value
      let output ← infer (Env.cons (CTy.pure input.value) types) body
      return ⟨output.value, input.row ++ output.row⟩
  | .request key payload => do
      let input ← infer types payload
      return ⟨.atom, input.row ++ [raw key]⟩
  | .boundary boundary body => do
      let input ← infer types body
      return ⟨input.value, boundary.row input.row⟩
  | .handler (count := count) operations target action onReturn onOperation => do
      let input ← infer types action
      let returned ← infer (Env.cons (CTy.pure input.value) types) onReturn
      let operated ← collectOptions (fun index => infer (operationTypes types input) (onOperation index))
      if checkV returned.value target &&
          (List.finRange count).all (fun index => checkV (operated index).value target) then
        return ⟨target, residual operations.keys input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩
      else none
  | .partialHandler (count := count) arms target action onReturn onArm => do
      let input ← infer types action
      let returned ← infer (Env.cons (CTy.pure input.value) types) onReturn
      let operated ← collectOptions (fun index => infer (operationTypes types input) (onArm index))
      if checkV returned.value target &&
          (List.finRange count).all (fun index => checkV (operated index).value target) then
        return ⟨target, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
          (returned.row ++ collectRows (fun index => (operated index).row))⟩
      else none
  | .widen target body => do
      let input ← infer types body
      if checkC input target then return target else none

theorem infer_complete [DecidableEq Key] {types : Env (CTy n Key) Γ}
    {expression : Expr n Key Atom Γ s} {output : CTy n Key s}
    (typed : Typing types expression output) : infer types expression = some output := by
  induction typed with
  | core typed => exact OperationalTyping.infer_complete typed
  | lam _ ih => simp [infer, ih]
  | app _ _ compatible ihf iha =>
      simp [infer, ihf, iha, CTy.arrow, (checkC_exact _ _).mpr compatible]
  | pair _ _ iha ihb => simp [infer, iha, ihb]
  | fst _ ih => simp [infer, ih]
  | snd _ ih => simp [infer, ih]
  | letE _ _ ihv ihb => simp [infer, ihv, ihb]
  | request _ ih => simp [infer, ih]
  | boundary _ ih => simp [infer, ih]
  | handler _ _ _ returned operated iha ihr iho =>
      have allArms := collectOptions_complete _ _ iho
      have checks : ∀ index, checkV _ _ = true := fun index => (checkV_exact _ _).mpr (operated index)
      simp [infer, iha, ihr, allArms, (checkV_exact _ _).mpr returned, checks]
  | partialHandler _ _ _ returned operated iha ihr iho =>
      have allArms := collectOptions_complete _ _ iho
      have checks : ∀ index, checkV _ _ = true := fun index => (checkV_exact _ _).mpr (operated index)
      simp [infer, iha, ihr, allArms, (checkV_exact _ _).mpr returned, checks]
  | widen _ compatible ih => simp [infer, ih, (checkC_exact _ _).mpr compatible]

theorem infer_sound [DecidableEq Key] (expression : Expr n Key Atom Γ s)
    (types : Env (CTy n Key) Γ) (output : CTy n Key s)
    (accepted : infer types expression = some output) : Typing types expression output := by
  induction expression with
  | core expression =>
      exact .core ((StrictApplication.infer_exact expression types output).mp accepted)
  | lam input body ih =>
      simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨result, success, equal⟩ := accepted
      cases Option.some.inj equal
      exact .lam (ih _ _ success)
  | app function argument ihf iha =>
      cases hf : infer types function with
      | none => simp [infer, hf] at accepted
      | some functionType =>
          rcases functionType with ⟨functionType, functionRow⟩
          cases functionType with
          | arrow a ea b eb =>
              cases ha : infer types argument with
              | none => simp [infer, hf, ha] at accepted
              | some actual =>
                  cases compatible : checkC (CTy.pure actual.value) ⟨a, ea⟩ with
                  | false => simp [infer, hf, ha, compatible] at accepted
                  | true =>
                      have equal : (⟨b, functionRow ++ (actual.row ++ eb)⟩ : CTy n Key _) = output := by
                        simpa [infer, hf, ha, compatible] using accepted
                      cases equal
                      exact .app (input := ⟨a, ea⟩) (output := ⟨b, eb⟩)
                        (ihf _ _ hf) (iha _ _ ha) ((checkC_exact _ _).mp compatible)
  | pair left right ihl ihr =>
      cases hl : infer types left with
      | none => simp [infer, hl] at accepted
      | some a =>
          cases hr : infer types right with
          | none => simp [infer, hl, hr] at accepted
          | some b =>
              have equal : (⟨.pair a.value b.value, a.row ++ b.row⟩ : CTy n Key _) = output := by
                simpa [infer, hl, hr] using accepted
              cases equal
              exact .pair (ihl _ _ hl) (ihr _ _ hr)
  | fst pair ih =>
      cases hp : infer types pair with
      | none => simp [infer, hp] at accepted
      | some pairType =>
          rcases pairType with ⟨pairType, row⟩
          cases pairType with
          | pair a b =>
              have equal : (⟨a, row⟩ : CTy n Key _) = output := by
                simpa [infer, hp] using accepted
              cases equal
              exact .fst (ih _ _ hp)
  | snd pair ih =>
      cases hp : infer types pair with
      | none => simp [infer, hp] at accepted
      | some pairType =>
          rcases pairType with ⟨pairType, row⟩
          cases pairType with
          | pair a b =>
              have equal : (⟨b, row⟩ : CTy n Key _) = output := by
                simpa [infer, hp] using accepted
              cases equal
              exact .snd (ih _ _ hp)
  | letE value body ihv ihb =>
      cases hv : infer types value with
      | none => simp [infer, hv] at accepted
      | some input =>
          cases hb : infer (Env.cons (CTy.pure input.value) types) body with
          | none => simp [infer, hv, hb] at accepted
          | some result =>
              have equal : (⟨result.value, input.row ++ result.row⟩ : CTy n Key _) = output := by
                simpa [infer, hv, hb] using accepted
              cases equal
              exact .letE (ihv _ _ hv) (ihb _ _ hb)
  | request key payload ih =>
      cases hp : infer types payload with
      | none => simp [infer, hp] at accepted
      | some input =>
          rcases input with ⟨input, row⟩
          cases input
          have equal : (⟨.atom, row ++ [raw key]⟩ : CTy n Key _) = output := by
            simpa [infer, hp] using accepted
          cases equal
          exact .request (ih _ _ hp)
  | boundary boundary body ih =>
      cases hb : infer types body with
      | none => simp [infer, hb] at accepted
      | some input =>
          have equal : (⟨input.value, boundary.row input.row⟩ : CTy n Key _) = output := by
            simpa [infer, hb] using accepted
          cases equal
          exact .boundary (ih _ _ hb)
  | handler operations target action onReturn onOperation iha ihr iho =>
      cases ha : infer types action with
      | none => simp [infer, ha] at accepted
      | some input =>
          cases hr : infer (Env.cons (CTy.pure input.value) types) onReturn with
          | none => simp [infer, ha, hr] at accepted
          | some returned =>
              cases ho : collectOptions (fun index => infer (operationTypes types input) (onOperation index)) with
              | none => simp [infer, ha, hr, ho] at accepted
              | some operated =>
                  cases compatible : checkV returned.value target &&
                      (List.finRange _).all (fun index => checkV (operated index).value target) with
                  | false => simp [infer, ha, hr, ho, compatible] at accepted
                  | true =>
                      have equal : (⟨target, residual operations.keys input.row ++
                          (returned.row ++ collectRows (fun index => (operated index).row))⟩ : CTy n Key _) =
                            output := by
                        simpa [infer, ha, hr, ho, compatible] using accepted
                      cases equal
                      have both : checkV returned.value target = true ∧
                          ∀ index, checkV (operated index).value target = true := by
                        simpa only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] using compatible
                      exact .handler (iha _ _ ha) (ihr _ _ hr)
                        (fun index => iho index _ _ (collectOptions_sound _ _ ho index))
                        ((checkV_exact _ _).mp both.1)
                        (fun index => (checkV_exact _ _).mp (both.2 index))
  | partialHandler arms target action onReturn onArm iha ihr iho =>
      cases ha : infer types action with
      | none => simp [infer, ha] at accepted
      | some input =>
          cases hr : infer (Env.cons (CTy.pure input.value) types) onReturn with
          | none => simp [infer, ha, hr] at accepted
          | some returned =>
              cases ho : collectOptions (fun index => infer (operationTypes types input) (onArm index)) with
              | none => simp [infer, ha, hr, ho] at accepted
              | some operated =>
                  cases compatible : checkV returned.value target &&
                      (List.finRange _).all (fun index => checkV (operated index).value target) with
                  | false => simp [infer, ha, hr, ho, compatible] at accepted
                  | true =>
                      have equal : (⟨target, residual (MultiOperationPayloadHandlers.removedKeys arms) input.row ++
                          (returned.row ++ collectRows (fun index => (operated index).row))⟩ : CTy n Key _) =
                            output := by
                        simpa [infer, ha, hr, ho, compatible] using accepted
                      cases equal
                      have both : checkV returned.value target = true ∧
                          ∀ index, checkV (operated index).value target = true := by
                        simpa only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] using compatible
                      exact .partialHandler (iha _ _ ha) (ihr _ _ hr)
                        (fun index => iho index _ _ (collectOptions_sound _ _ ho index))
                        ((checkV_exact _ _).mp both.1)
                        (fun index => (checkV_exact _ _).mp (both.2 index))
  | widen target body ih =>
      cases hb : infer types body with
      | none => simp [infer, hb] at accepted
      | some input =>
          cases compatible : checkC input target with
          | false => simp [infer, hb, compatible] at accepted
          | true =>
              have equal : target = output := by simpa [infer, hb, compatible] using accepted
              cases equal
              exact .widen (ih _ _ hb) ((checkC_exact _ _).mp compatible)

theorem infer_exact [DecidableEq Key] (expression : Expr n Key Atom Γ s)
    (types : Env (CTy n Key) Γ) (output : CTy n Key s) :
    infer types expression = some output ↔ Typing types expression output :=
  ⟨infer_sound expression types output, infer_complete⟩

theorem inferred_operationally_valid [DecidableEq Key]
    (expression : Expr n Key Atom Γ s) (types : Env (CTy n Key) Γ)
    (output : CTy n Key s) (accepted : infer types expression = some output)
    (runtime : Env (Tree n Key Atom) Γ) (environment : EnvValid types runtime) :
    Valid output (eval runtime expression) :=
  typing_evaluates (infer_sound expression types output accepted) runtime environment

end Yulang.MultiOperationHandlerTyping
