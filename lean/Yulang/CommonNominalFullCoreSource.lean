import Yulang.CommonNominalCoreSource
import Yulang.CommonNominalFullStrictApplication
import Yulang.CommonNominalFullNamedCase

/-!
# Actual common Core source lowering over the full nominal carrier

Literal payloads and structural data remain in original Core syntax. Every
original covered common constructor, captured scheme and value-let alternative
has the same independent typing as its actual presence lowering. No old-image
restriction is imposed on environments, intermediate types or results.
This does not add nominal/list construction rules to the public Core entry.
-/

namespace Yulang.CommonNominalFullCoreSource

open Core Core.CommonSyntax

open PresenceGeneration (Model Comp)

theorem lowering_exact (expression : Term) (within : covered expression = true)
    (related : EnvRel CommonNominalFullCarrier.model environment source) (result : Comp CommonNominalFullCarrier.model) :
    Typing CommonNominalFullCarrier.model environment expression result ↔
      PresenceGeneration.Typing CommonNominalFullCarrier.model source (lower expression) result := by
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
      change _ ↔ PresenceGeneration.Typing CommonNominalFullCarrier.model source
        (CommonNominalFullStrictApplication.forceApplication (lower first) (lower last)) result
      rw [CommonNominalFullStrictApplication.forceApplication_typing_exact source (lower first) (lower last) result]
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
      have polyRelated : EnvRel CommonNominalFullCarrier.model (.poly value environment :: environment)
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
      change _ ↔ PresenceGeneration.Typing CommonNominalFullCarrier.model source
        (CommonNominalFullNamedCase.caseName (lower subject) (lower body)) result
      rw [CommonNominalFullNamedCase.lowering_exact source (lower subject) (lower body) result]
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


/-- Every actual original common Core source expression and arbitrary full
nominal environment/result, with syntax rejection discharged internally. -/
theorem generate_nominal_core_exact (symbolic : PresenceGeneration.SchemeEnv α)
    (environment : List (Binding CommonNominalFullCarrier.model))
    (source : List (PresenceGeneration.Binding CommonNominalFullCarrier.model))
    (assignment : α → Comp CommonNominalFullCarrier.model) (expression : Term)
    (output : PresenceGeneration.CompTerm α)
    (actualRelated : EnvRel CommonNominalFullCarrier.model environment source)
    (symbolicRelated : PresenceGeneration.EnvRel CommonNominalFullCarrier.model assignment symbolic source) :
    (generateNominalCore symbolic expression output).Holds CommonNominalFullCarrier.model assignment ↔
      Typing CommonNominalFullCarrier.model environment expression (output.eval CommonNominalFullCarrier.model assignment) := by
  cases within : covered expression with
  | false =>
      constructor
      · simp [generateNominalCore, within, PresenceGeneration.Formula.Holds]
      · intro typed
        have supported := typing_covered typed
        simp [within] at supported
  | true =>
      rw [generateNominalCore, ite_eq_left within]
      exact (PresenceGeneration.generate_models_iff_typing CommonNominalFullCarrier.model _ symbolic source
        assignment output symbolicRelated).trans
        (lowering_exact expression within actualRelated _).symm

end Yulang.CommonNominalFullCoreSource
