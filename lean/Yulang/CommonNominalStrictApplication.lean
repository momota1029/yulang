import Yulang.CommonNominalSourceSubsumption
import Yulang.CommonNominalConstructors

/-!
# Actual strict-application lowering over the full nominal carrier

This transfers the independent original strict rule and its pair/let lowering
without restricting argument/result types to old Common images. Both original
let alternatives and all captured environments are included. No solver or
runtime theorem is inferred from this source-typing equivalence.
-/

namespace Yulang.CommonNominalStrictApplication

open Core.PresenceGeneration
open Inference (Expr)

abbrev Context := List (Binding CommonNominalCarrier.model)
abbrev Result := Comp CommonNominalCarrier.model

def forceApplication (function argument : Expr) : Expr :=
  .letE (.pair function argument) (.app (.fst (.var 0)) (.snd (.var 0)))

/-- Independent written-order rule. Its definition mentions neither the
source macro nor the generated formula nor any solver result. -/
inductive StrictTyping (environment : Context) (function argument : Expr) : Result → Prop where
  | app {input output actual result : Result} {functionRow : Common.Row} :
      Typing CommonNominalCarrier.model environment function (Comp.arrow CommonNominalCarrier.model input output, functionRow) →
      Typing CommonNominalCarrier.model environment argument actual →
      Comp.le CommonNominalCarrier.model (Comp.pure CommonNominalCarrier.model actual.1) input →
      Comp.le CommonNominalCarrier.model
        (output.1, Common.rowJoin functionRow (Common.rowJoin actual.2 output.2)) result →
      StrictTyping environment function argument result

private theorem comp_refl (result : Result) : Comp.le CommonNominalCarrier.model result result :=
  ⟨CommonNominalCarrier.subtype_refl _, Common.rowLe_refl _⟩

private theorem zero_binding {environment : Context} {binding : Binding CommonNominalCarrier.model}
    {result : Result} (typed : Typing CommonNominalCarrier.model (binding :: environment) (.var 0) result) :
    BindingTyping CommonNominalCarrier.model binding result := by
  cases typed with
  | var found accepted =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact accepted

private theorem pair_left {environment : Context} {function argument : Expr} {result : Result}
    {first last : CommonNominalCarrier.Ty}
    (typed : Typing CommonNominalCarrier.model environment (.pair function argument) result)
    (below : CommonNominalCarrier.Subtype result.1 (CommonNominalCarrier.pair first last)) :
    ∃ row, Typing CommonNominalCarrier.model environment function (first, row) ∧ Common.rowLe row result.2 := by
  cases typed with
  | pair before after bounded =>
      have components := (CommonNominalCarrier.common_pair_iff _ _ _ _).mp
        (CommonNominalCarrier.subtype_trans bounded.1 below)
      exact ⟨_, CommonNominalSourceSubsumption.typing_subsume before _
        ⟨components.1, Common.rowLe_refl _⟩,
        fun occurrence member => bounded.2 occurrence (Or.inl member)⟩

private theorem pair_right {environment : Context} {function argument : Expr} {result : Result}
    {first last : CommonNominalCarrier.Ty}
    (typed : Typing CommonNominalCarrier.model environment (.pair function argument) result)
    (below : CommonNominalCarrier.Subtype result.1 (CommonNominalCarrier.pair first last)) :
    ∃ row, Typing CommonNominalCarrier.model environment argument (last, row) ∧ Common.rowLe row result.2 := by
  cases typed with
  | pair before after bounded =>
      have components := (CommonNominalCarrier.common_pair_iff _ _ _ _).mp
        (CommonNominalCarrier.subtype_trans bounded.1 below)
      exact ⟨_, CommonNominalSourceSubsumption.typing_subsume after _
        ⟨components.2, Common.rowLe_refl _⟩,
        fun occurrence member => bounded.2 occurrence (Or.inr member)⟩

private theorem mono_fst {environment : Context} {function argument : Expr} {captured wanted : Result}
    (source : Typing CommonNominalCarrier.model environment (.pair function argument) captured)
    (used : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model captured.1) :: environment)
      (.fst (.var 0)) wanted) :
    ∃ row, Typing CommonNominalCarrier.model environment function (wanted.1, row) ∧ Common.rowLe row captured.2 := by
  cases used with
  | fst pair bounded =>
      cases zero_binding pair with
      | mono contained =>
          obtain ⟨row, typed, rowBound⟩ := pair_left source contained.1
          exact ⟨row, CommonNominalSourceSubsumption.typing_subsume typed _
            ⟨bounded.1, Common.rowLe_refl _⟩, rowBound⟩

private theorem mono_snd {environment : Context} {function argument : Expr} {captured wanted : Result}
    (source : Typing CommonNominalCarrier.model environment (.pair function argument) captured)
    (used : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model captured.1) :: environment)
      (.snd (.var 0)) wanted) :
    ∃ row, Typing CommonNominalCarrier.model environment argument (wanted.1, row) ∧ Common.rowLe row captured.2 := by
  cases used with
  | snd pair bounded =>
      cases zero_binding pair with
      | mono contained =>
          obtain ⟨row, typed, rowBound⟩ := pair_right source contained.1
          exact ⟨row, CommonNominalSourceSubsumption.typing_subsume typed _
            ⟨bounded.1, Common.rowLe_refl _⟩, rowBound⟩

private theorem poly_fst {environment : Context} {function argument : Expr} {wanted : Result}
    (used : Typing CommonNominalCarrier.model (.poly (.pair function argument) environment :: environment)
      (.fst (.var 0)) wanted) :
    Typing CommonNominalCarrier.model environment function (Comp.pure CommonNominalCarrier.model wanted.1) := by
  cases used with
  | fst pair bounded =>
      cases zero_binding pair with
      | poly source _ =>
          obtain ⟨row, typed, rowBound⟩ := pair_left source (CommonNominalCarrier.subtype_refl _)
          exact CommonNominalSourceSubsumption.typing_subsume typed _ ⟨bounded.1, rowBound⟩

private theorem poly_snd {environment : Context} {function argument : Expr} {wanted : Result}
    (used : Typing CommonNominalCarrier.model (.poly (.pair function argument) environment :: environment)
      (.snd (.var 0)) wanted) :
    Typing CommonNominalCarrier.model environment argument (Comp.pure CommonNominalCarrier.model wanted.1) := by
  cases used with
  | snd pair bounded =>
      cases zero_binding pair with
      | poly source _ =>
          obtain ⟨row, typed, rowBound⟩ := pair_right source (CommonNominalCarrier.subtype_refl _)
          exact CommonNominalSourceSubsumption.typing_subsume typed _ ⟨bounded.1, rowBound⟩

theorem forceApplication_reflected {environment : Context} {function argument : Expr} {result : Result}
    (typed : Typing CommonNominalCarrier.model environment (forceApplication function argument) result) :
    StrictTyping environment function argument result := by
  cases typed with
  | letComputed captured body bounded =>
      cases body with
      | app functionUsed argumentUsed bodyBound =>
          obtain ⟨functionRow, functionTyped, functionBound⟩ := mono_fst captured functionUsed
          obtain ⟨argumentRow, argumentTyped, argumentBound⟩ := mono_snd captured argumentUsed
          refine .app functionTyped argumentTyped
            ⟨CommonNominalCarrier.subtype_refl _, Common.rowEmpty_le _⟩
            ⟨CommonNominalCarrier.subtype_trans bodyBound.1 bounded.1, ?_⟩
          intro occurrence member
          rcases member with before | argument | after
          · exact bounded.2 occurrence (Or.inl (functionBound occurrence before))
          · exact bounded.2 occurrence (Or.inl (argumentBound occurrence argument))
          · exact bounded.2 occurrence (Or.inr (bodyBound.2 occurrence (Or.inr after)))
  | letValue _ _ body =>
      cases body with
      | app functionUsed argumentUsed bodyBound =>
          refine .app (poly_fst functionUsed) (poly_snd argumentUsed)
            ⟨CommonNominalCarrier.subtype_refl _, Common.rowEmpty_le _⟩ ⟨bodyBound.1, ?_⟩
          intro occurrence member
          rcases member with impossible | impossible | after
          · exact False.elim impossible
          · exact False.elim impossible
          · exact bodyBound.2 occurrence (Or.inr after)

theorem forceApplication_preserved {environment : Context} {function argument : Expr} {result : Result}
    (typed : StrictTyping environment function argument result) :
    Typing CommonNominalCarrier.model environment (forceApplication function argument) result := by
  cases typed with
  | @app input output actual result functionRow functionTyped argumentTyped compatible bounded =>
      let value := CommonNominalCarrier.pair (Comp.arrow CommonNominalCarrier.model input output) actual.1
      have boundVariable : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model value) :: environment)
          (.var 0) (Comp.pure CommonNominalCarrier.model value) := .var rfl (.mono (comp_refl _))
      have functionUsed : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model value) :: environment)
          (.fst (.var 0)) (Comp.pure CommonNominalCarrier.model (Comp.arrow CommonNominalCarrier.model input output)) :=
        .fst boundVariable (comp_refl _)
      have argumentUsed : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model value) :: environment)
          (.snd (.var 0)) input := .snd boundVariable compatible
      have body : Typing CommonNominalCarrier.model (.mono (Comp.pure CommonNominalCarrier.model value) :: environment)
          (.app (.fst (.var 0)) (.snd (.var 0))) output :=
        .app functionUsed argumentUsed ⟨CommonNominalCarrier.subtype_refl _,
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
    Typing CommonNominalCarrier.model environment (forceApplication function argument) result ↔
      StrictTyping environment function argument result :=
  ⟨forceApplication_reflected, forceApplication_preserved⟩

end Yulang.CommonNominalStrictApplication
