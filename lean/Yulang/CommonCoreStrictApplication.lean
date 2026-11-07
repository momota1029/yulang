import Yulang.CommonSolvedSource

/-!
# Strict application in the common inference carrier

The source macro evaluates the function and then the argument in a pair,
captures that pair once, and applies its two pure projections. No source
operand is copied, shifted or evaluated through a suspended argument.

The independent rule checks the evaluated argument value at the function's
input computation and retains the function, argument and result rows. The
equivalence below handles both existing let rules: a captured value pair may
be generalized, but selecting its two projections separately cannot add a
strict-application typing. All original lexical bindings remain shared.

This module supplies the reusable source boundary for the extended Core
judgment. It leaves the historical computation-argument application intact.
-/

namespace Yulang.CommonCoreStrictApplication

open Core.PresenceGeneration
open Inference (Expr)

abbrev Context := List (Binding Common.model)
abbrev Result := Comp Common.model

def forceApplication (function argument : Expr) : Expr :=
  .letE (.pair function argument) (.app (.fst (.var 0)) (.snd (.var 0)))

/-- Independent written-order rule. Its definition mentions neither the
source macro nor the generated formula nor any solver result. -/
inductive StrictTyping (environment : Context) (function argument : Expr) : Result → Prop where
  | app {input output actual result : Result} {functionRow : Common.Row} :
      Typing Common.model environment function (Comp.arrow Common.model input output, functionRow) →
      Typing Common.model environment argument actual →
      Comp.le Common.model (Comp.pure Common.model actual.1) input →
      Comp.le Common.model
        (output.1, Common.rowJoin functionRow (Common.rowJoin actual.2 output.2)) result →
      StrictTyping environment function argument result

private theorem comp_refl (result : Result) : Comp.le Common.model result result :=
  ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

private theorem zero_binding {environment : Context} {binding : Binding Common.model}
    {result : Result} (typed : Typing Common.model (binding :: environment) (.var 0) result) :
    BindingTyping Common.model binding result := by
  cases typed with
  | var found accepted =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact accepted

private theorem pair_left {environment : Context} {function argument : Expr} {result : Result}
    {first last : Common.Ty}
    (typed : Typing Common.model environment (.pair function argument) result)
    (below : Common.Subtype result.1 (Common.pair first last)) :
    ∃ row, Typing Common.model environment function (first, row) ∧ Common.rowLe row result.2 := by
  cases typed with
  | pair before after bounded =>
      have components := (Common.common_pair_iff _ _ _ _).mp
        (Common.subtype_trans bounded.1 below)
      exact ⟨_, CommonPresenceSourceFamily.typing_subsume before _
        ⟨components.1, Common.rowLe_refl _⟩,
        fun occurrence member => bounded.2 occurrence (Or.inl member)⟩

private theorem pair_right {environment : Context} {function argument : Expr} {result : Result}
    {first last : Common.Ty}
    (typed : Typing Common.model environment (.pair function argument) result)
    (below : Common.Subtype result.1 (Common.pair first last)) :
    ∃ row, Typing Common.model environment argument (last, row) ∧ Common.rowLe row result.2 := by
  cases typed with
  | pair before after bounded =>
      have components := (Common.common_pair_iff _ _ _ _).mp
        (Common.subtype_trans bounded.1 below)
      exact ⟨_, CommonPresenceSourceFamily.typing_subsume after _
        ⟨components.2, Common.rowLe_refl _⟩,
        fun occurrence member => bounded.2 occurrence (Or.inr member)⟩

private theorem mono_fst {environment : Context} {function argument : Expr} {captured wanted : Result}
    (source : Typing Common.model environment (.pair function argument) captured)
    (used : Typing Common.model (.mono (Comp.pure Common.model captured.1) :: environment)
      (.fst (.var 0)) wanted) :
    ∃ row, Typing Common.model environment function (wanted.1, row) ∧ Common.rowLe row captured.2 := by
  cases used with
  | fst pair bounded =>
      cases zero_binding pair with
      | mono contained =>
          obtain ⟨row, typed, rowBound⟩ := pair_left source contained.1
          exact ⟨row, CommonPresenceSourceFamily.typing_subsume typed _
            ⟨bounded.1, Common.rowLe_refl _⟩, rowBound⟩

private theorem mono_snd {environment : Context} {function argument : Expr} {captured wanted : Result}
    (source : Typing Common.model environment (.pair function argument) captured)
    (used : Typing Common.model (.mono (Comp.pure Common.model captured.1) :: environment)
      (.snd (.var 0)) wanted) :
    ∃ row, Typing Common.model environment argument (wanted.1, row) ∧ Common.rowLe row captured.2 := by
  cases used with
  | snd pair bounded =>
      cases zero_binding pair with
      | mono contained =>
          obtain ⟨row, typed, rowBound⟩ := pair_right source contained.1
          exact ⟨row, CommonPresenceSourceFamily.typing_subsume typed _
            ⟨bounded.1, Common.rowLe_refl _⟩, rowBound⟩

private theorem poly_fst {environment : Context} {function argument : Expr} {wanted : Result}
    (used : Typing Common.model (.poly (.pair function argument) environment :: environment)
      (.fst (.var 0)) wanted) :
    Typing Common.model environment function (Comp.pure Common.model wanted.1) := by
  cases used with
  | fst pair bounded =>
      cases zero_binding pair with
      | poly source _ =>
          obtain ⟨row, typed, rowBound⟩ := pair_left source (Common.subtype_refl _)
          exact CommonPresenceSourceFamily.typing_subsume typed _ ⟨bounded.1, rowBound⟩

private theorem poly_snd {environment : Context} {function argument : Expr} {wanted : Result}
    (used : Typing Common.model (.poly (.pair function argument) environment :: environment)
      (.snd (.var 0)) wanted) :
    Typing Common.model environment argument (Comp.pure Common.model wanted.1) := by
  cases used with
  | snd pair bounded =>
      cases zero_binding pair with
      | poly source _ =>
          obtain ⟨row, typed, rowBound⟩ := pair_right source (Common.subtype_refl _)
          exact CommonPresenceSourceFamily.typing_subsume typed _ ⟨bounded.1, rowBound⟩

theorem forceApplication_reflected {environment : Context} {function argument : Expr} {result : Result}
    (typed : Typing Common.model environment (forceApplication function argument) result) :
    StrictTyping environment function argument result := by
  cases typed with
  | letComputed captured body bounded =>
      cases body with
      | app functionUsed argumentUsed bodyBound =>
          obtain ⟨functionRow, functionTyped, functionBound⟩ := mono_fst captured functionUsed
          obtain ⟨argumentRow, argumentTyped, argumentBound⟩ := mono_snd captured argumentUsed
          refine .app functionTyped argumentTyped
            ⟨Common.subtype_refl _, Common.rowEmpty_le _⟩
            ⟨Common.subtype_trans bodyBound.1 bounded.1, ?_⟩
          intro occurrence member
          rcases member with before | argument | after
          · exact bounded.2 occurrence (Or.inl (functionBound occurrence before))
          · exact bounded.2 occurrence (Or.inl (argumentBound occurrence argument))
          · exact bounded.2 occurrence (Or.inr (bodyBound.2 occurrence (Or.inr after)))
  | letValue _ _ body =>
      cases body with
      | app functionUsed argumentUsed bodyBound =>
          refine .app (poly_fst functionUsed) (poly_snd argumentUsed)
            ⟨Common.subtype_refl _, Common.rowEmpty_le _⟩ ⟨bodyBound.1, ?_⟩
          intro occurrence member
          rcases member with impossible | impossible | after
          · exact False.elim impossible
          · exact False.elim impossible
          · exact bodyBound.2 occurrence (Or.inr after)

theorem forceApplication_preserved {environment : Context} {function argument : Expr} {result : Result}
    (typed : StrictTyping environment function argument result) :
    Typing Common.model environment (forceApplication function argument) result := by
  cases typed with
  | @app input output actual result functionRow functionTyped argumentTyped compatible bounded =>
      let value := Common.pair (Comp.arrow Common.model input output) actual.1
      have boundVariable : Typing Common.model (.mono (Comp.pure Common.model value) :: environment)
          (.var 0) (Comp.pure Common.model value) := .var rfl (.mono (comp_refl _))
      have functionUsed : Typing Common.model (.mono (Comp.pure Common.model value) :: environment)
          (.fst (.var 0)) (Comp.pure Common.model (Comp.arrow Common.model input output)) :=
        .fst boundVariable (comp_refl _)
      have argumentUsed : Typing Common.model (.mono (Comp.pure Common.model value) :: environment)
          (.snd (.var 0)) input := .snd boundVariable compatible
      have body : Typing Common.model (.mono (Comp.pure Common.model value) :: environment)
          (.app (.fst (.var 0)) (.snd (.var 0))) output :=
        .app functionUsed argumentUsed ⟨Common.subtype_refl _,
          fun _ member => member.elim False.elim id⟩
      refine .letComputed (.pair functionTyped argumentTyped (comp_refl _)) body ⟨bounded.1, ?_⟩
      intro occurrence member
      rcases member with (before | argument) | after
      · exact bounded.2 occurrence (Or.inl before)
      · exact bounded.2 occurrence (Or.inr (Or.inl argument))
      · exact bounded.2 occurrence (Or.inr (Or.inr after))

/-- All lexical environments (including captured schemes), both source
operands, and all common value/row results. No syntax or solve premise. -/
theorem forceApplication_typing_exact (environment : Context) (function argument : Expr) (result : Result) :
    Typing Common.model environment (forceApplication function argument) result ↔
      StrictTyping environment function argument result :=
  ⟨forceApplication_reflected, forceApplication_preserved⟩

/-- Actual finite schemes, obtained by running the existing complete solver
on the proved strict lowering. No residual conditions are added to parameters. -/
def infer (function argument : Expr) : List CommonSolvedSource.Scheme :=
  CommonSolvedSource.inferSource (forceApplication function argument)

theorem all_parameters_typed (function argument : Expr) (scheme : CommonSolvedSource.Scheme)
    (returned : scheme ∈ infer function argument) (parameters : scheme.Parameters) :
    StrictTyping [] function argument (scheme.instantiate parameters) :=
  forceApplication_reflected
    (CommonSolvedSource.source_instantiates (forceApplication function argument) scheme returned parameters)

theorem principal (function argument : Expr) (result : Result) :
    StrictTyping [] function argument result ↔
      ∃ scheme ∈ infer function argument, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result :=
  (forceApplication_typing_exact [] function argument result).symm.trans
    (CommonSolvedSource.source_principal (forceApplication function argument) result)

theorem empty_iff_untypable (function argument : Expr) :
    infer function argument = [] ↔ ¬ ∃ result, StrictTyping [] function argument result := by
  rw [infer, CommonSolvedSource.source_empty_iff]
  simp only [forceApplication_typing_exact]

end Yulang.CommonCoreStrictApplication
