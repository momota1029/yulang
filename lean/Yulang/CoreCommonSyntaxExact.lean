import Yulang.CoreCommonSyntax

/-! Exact lowering of the independent common syntax rules, including captured
polymorphic environments and both value-restricted let alternatives. -/

namespace Yulang.Core.CommonSyntax

open PresenceGeneration (Model Comp)

def Lookup (m : Model) (environment : List (Binding m)) (index : Nat) (result : Comp m) : Prop :=
  ∃ binding, environment[index]? = some binding ∧ BindingTyping m binding result

def SourceLookup (m : Model) (environment : List (PresenceGeneration.Binding m))
    (index : Nat) (result : Comp m) : Prop :=
  ∃ binding, environment[index]? = some binding ∧ PresenceGeneration.BindingTyping m binding result

/-- The two environments give exactly the same computation instances at
each lexical index. Captured bodies need not have identical syntax. -/
def EnvRel (m : Model) (environment : List (Binding m))
    (source : List (PresenceGeneration.Binding m)) : Prop :=
  ∀ index result, Lookup m environment index result ↔ SourceLookup m source index result

theorem EnvRel.nil (m : Model) : EnvRel m [] [] := by
  intro index result
  simp [Lookup, SourceLookup]

theorem EnvRel.cons (related : EnvRel m environment source)
    (bindingRelated : ∀ result, BindingTyping m binding result ↔
      PresenceGeneration.BindingTyping m sourceBinding result) :
    EnvRel m (binding :: environment) (sourceBinding :: source) := by
  intro index result
  cases index with
  | zero => simpa [Lookup, SourceLookup] using bindingRelated result
  | succ index => simpa [Lookup, SourceLookup] using related index result

@[simp] theorem mono_iff (value result : Comp m) :
    BindingTyping m (.mono value) result ↔ Comp.le m value result := by
  constructor
  · intro typed; cases typed; assumption
  · exact .mono

@[simp] theorem source_mono_iff (value result : Comp m) :
    PresenceGeneration.BindingTyping m (.mono value) result ↔ Comp.le m value result := by
  constructor
  · intro typed; cases typed; assumption
  · exact .mono

theorem EnvRel.mono (related : EnvRel m environment source) (value : Comp m) :
    EnvRel m (.mono value :: environment) (.mono value :: source) :=
  related.cons (fun result => (mono_iff value result).trans (source_mono_iff value result).symm)

@[simp] theorem poly_iff (expression : Term) (environment : List (Binding m)) (result : Comp m) :
    BindingTyping m (.poly expression environment) result ↔
      Typing m environment expression (Comp.pure m result.1) ∧ m.subRow m.empty result.2 := by
  constructor
  · intro typed; cases typed; exact ⟨‹_›, ‹_›⟩
  · rintro ⟨typed, row⟩; exact .poly typed row

@[simp] theorem source_poly_iff (expression : Inference.Expr)
    (environment : List (PresenceGeneration.Binding m)) (result : Comp m) :
    PresenceGeneration.BindingTyping m (.poly expression environment) result ↔
      PresenceGeneration.Typing m environment expression (Comp.pure m result.1) ∧
        m.subRow m.empty result.2 := by
  constructor
  · intro typed; cases typed; exact ⟨‹_›, ‹_›⟩
  · rintro ⟨typed, row⟩; exact .poly typed row

@[simp] theorem var_iff (environment : List (Binding m)) (index : Nat) (result : Comp m) :
    Typing m environment (.var index) result ↔ Lookup m environment index result := by
  constructor
  · intro typed; cases typed; exact ⟨_, ‹_›, ‹_›⟩
  · rintro ⟨binding, found, typed⟩; exact .var found typed

@[simp] theorem source_var_iff (environment : List (PresenceGeneration.Binding m))
    (index : Nat) (result : Comp m) :
    PresenceGeneration.Typing m environment (.var index) result ↔
      SourceLookup m environment index result := by
  constructor
  · intro typed; cases typed; exact ⟨_, ‹_›, ‹_›⟩
  · rintro ⟨binding, found, typed⟩; exact .var found typed

/-- The concrete common model, all related captured environments, covered
expressions and arbitrary result computations. This internal compiler lemma uses only a
syntactic domain condition; the public closed theorem discharges it internally. -/
theorem lowering_exact (expression : Term) (within : covered expression = true)
    (related : EnvRel Common.model environment source) (result : Comp Common.model) :
    Typing Common.model environment expression result ↔
      PresenceGeneration.Typing Common.model source (lower expression) result := by
  cases expression with
  | var index => simpa only [lower, var_iff, source_var_iff] using related index result
  | lit base =>
      constructor
      · intro typed; cases typed; exact .lit ‹_›
      · intro typed; cases typed; exact .lit ‹_›
  | literal value =>
      constructor
      · intro typed; cases typed; exact .lit ‹_›
      · intro typed; cases typed; exact .literal ‹_›
  | data value =>
      constructor
      · intro typed; cases typed with
        | data valueTyped => exact CommonData.typing_lowered valueTyped source
      · intro typed; exact .data (CommonData.typing_reflected value within typed)
  | lam body =>
      constructor
      · intro typed; cases typed with
        | lam bodyTyped bounded =>
            exact .lam ((lowering_exact body within (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | lam bodyTyped bounded =>
            exact .lam ((lowering_exact body within (related.mono _) _).mpr bodyTyped) bounded
  | app first last =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | app functionTyped argumentTyped bounded =>
            exact .app ((lowering_exact first within.1 related _).mp functionTyped)
              ((lowering_exact last within.2 related _).mp argumentTyped) bounded
      · intro typed; cases typed with
        | app functionTyped argumentTyped bounded =>
            exact .app ((lowering_exact first within.1 related _).mpr functionTyped)
              ((lowering_exact last within.2 related _).mpr argumentTyped) bounded
  | strictApp first last =>
      simp only [covered, Bool.and_eq_true] at within
      rw [lower, CommonCoreStrictApplication.forceApplication_typing_exact]
      constructor
      · intro typed; cases typed with
        | strictApp functionTyped argumentTyped compatible bounded =>
            exact .app ((lowering_exact first within.1 related _).mp functionTyped)
              ((lowering_exact last within.2 related _).mp argumentTyped) compatible bounded
      · intro typed; cases typed with
        | app functionTyped argumentTyped compatible bounded =>
            exact .strictApp ((lowering_exact first within.1 related _).mpr functionTyped)
              ((lowering_exact last within.2 related _).mpr argumentTyped) compatible bounded
  | letE name value body =>
      simp only [covered, Bool.and_eq_true] at within
      have polyRelated : EnvRel Common.model (.poly value environment :: environment)
          (.poly (lower value) source :: source) :=
        related.cons (fun result => by
          simp only [poly_iff, source_poly_iff]
          exact and_congr (lowering_exact value within.1 related _) Iff.rfl)
      constructor
      · intro typed; cases typed with
        | letValue nonexpansive valueTyped bodyTyped =>
            exact .letValue (by simpa only [lower_isValue value within.1] using nonexpansive)
              ((lowering_exact value within.1 related _).mp valueTyped)
              ((lowering_exact body within.2 polyRelated _).mp bodyTyped)
        | letComputed valueTyped bodyTyped bounded =>
            exact .letComputed ((lowering_exact value within.1 related _).mp valueTyped)
              ((lowering_exact body within.2 (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | letValue nonexpansive valueTyped bodyTyped =>
            exact .letValue (by simpa only [lower_isValue value within.1] using nonexpansive)
              ((lowering_exact value within.1 related _).mpr valueTyped)
              ((lowering_exact body within.2 polyRelated _).mpr bodyTyped)
        | letComputed valueTyped bodyTyped bounded =>
            exact .letComputed ((lowering_exact value within.1 related _).mpr valueTyped)
              ((lowering_exact body within.2 (related.mono _) _).mpr bodyTyped) bounded
  | leaf body =>
      constructor
      · intro typed; cases typed with
        | leaf bodyTyped => exact (lowering_exact body within related _).mp bodyTyped
      · intro typed; exact .leaf ((lowering_exact body within related _).mpr typed)
  | caseE subject arms =>
      obtain ⟨name, body, rfl, subjectWithin, bodyWithin⟩ := (covered_case_iff subject arms).mp within
      change _ ↔ PresenceGeneration.Typing Common.model source
        (CommonCoreNamedCase.caseName (lower subject) (lower body)) result
      rw [CommonCoreNamedCase.lowering_exact]
      constructor
      · intro typed; cases typed with
        | caseName subjectTyped bodyTyped bounded =>
            exact .bind ((lowering_exact subject subjectWithin related _).mp subjectTyped)
              ((lowering_exact body bodyWithin (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | bind subjectTyped bodyTyped bounded =>
            exact .caseName ((lowering_exact subject subjectWithin related _).mpr subjectTyped)
              ((lowering_exact body bodyWithin (related.mono _) _).mpr bodyTyped) bounded
  | branch condition yes no =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | branch conditionTyped yesTyped noTyped bounded =>
            exact .branch ((lowering_exact condition within.1.1 related _).mp conditionTyped)
              ((lowering_exact yes within.1.2 related _).mp yesTyped)
              ((lowering_exact no within.2 related _).mp noTyped) bounded
      · intro typed; cases typed with
        | branch conditionTyped yesTyped noTyped bounded =>
            exact .branch ((lowering_exact condition within.1.1 related _).mpr conditionTyped)
              ((lowering_exact yes within.1.2 related _).mpr yesTyped)
              ((lowering_exact no within.2 related _).mpr noTyped) bounded
  | pair first last =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | pair firstTyped lastTyped bounded =>
            exact .pair ((lowering_exact first within.1 related _).mp firstTyped)
              ((lowering_exact last within.2 related _).mp lastTyped) bounded
      · intro typed; cases typed with
        | pair firstTyped lastTyped bounded =>
            exact .pair ((lowering_exact first within.1 related _).mpr firstTyped)
              ((lowering_exact last within.2 related _).mpr lastTyped) bounded
  | fst body =>
      constructor
      · intro typed; cases typed with
        | fst bodyTyped bounded => exact .fst ((lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | fst bodyTyped bounded => exact .fst ((lowering_exact body within related _).mpr bodyTyped) bounded
  | snd body =>
      constructor
      · intro typed; cases typed with
        | snd bodyTyped bounded => exact .snd ((lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | snd bodyTyped bounded => exact .snd ((lowering_exact body within related _).mpr bodyTyped) bounded
  | emptyRecord =>
      constructor
      · intro typed; cases typed; exact .emptyRecord ‹_›
      · intro typed; cases typed; exact .emptyRecord ‹_›
  | record label head tail =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | record headTyped tailTyped width bounded =>
            exact .record ((lowering_exact head within.1 related _).mp headTyped)
              ((lowering_exact tail within.2 related _).mp tailTyped) width bounded
      · intro typed; cases typed with
        | record headTyped tailTyped width bounded =>
            exact .record ((lowering_exact head within.1 related _).mpr headTyped)
              ((lowering_exact tail within.2 related _).mpr tailTyped) width bounded
  | recordDefault label initial fallback =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | recordDefault sourceTyped fallbackTyped width bounded =>
            exact .recordDefault ((lowering_exact initial within.1 related _).mp sourceTyped)
              ((lowering_exact fallback within.2 related _).mp fallbackTyped) width bounded
      · intro typed; cases typed with
        | recordDefault sourceTyped fallbackTyped width bounded =>
            exact .recordDefault ((lowering_exact initial within.1 related _).mpr sourceTyped)
              ((lowering_exact fallback within.2 related _).mpr fallbackTyped) width bounded
  | field label body =>
      constructor
      · intro typed; cases typed with
        | field bodyTyped bounded => exact .field ((lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | field bodyTyped bounded => exact .field ((lowering_exact body within related _).mpr bodyTyped) bounded
  | variant label body =>
      constructor
      · intro typed; cases typed with
        | variant bodyTyped bounded => exact .variant ((lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | variant bodyTyped bounded => exact .variant ((lowering_exact body within related _).mpr bodyTyped) bounded
  | _ => simp [covered] at within
termination_by expression

end Yulang.Core.CommonSyntax
