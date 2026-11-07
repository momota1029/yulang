import Yulang.CoreCommonSyntaxExact
import Yulang.CommonNominalStrictApplication
import Yulang.CommonNominalNamedCase

/-!
# Actual common Core source lowering over the full nominal carrier

Literal payloads and structural data remain in original Core syntax. Every
original covered common constructor, captured scheme and value-let alternative
has the same independent typing as its actual presence lowering. No old-image
restriction is imposed on environments, intermediate types or results.
This does not add nominal/list construction rules to the public Core entry.
-/

namespace Yulang.Core.CommonSyntax

open PresenceGeneration (Model Comp)

theorem nominal_lowering_exact (expression : Term) (within : covered expression = true)
    (related : EnvRel CommonNominalCarrier.model environment source) (result : Comp CommonNominalCarrier.model) :
    Typing CommonNominalCarrier.model environment expression result ↔
      PresenceGeneration.Typing CommonNominalCarrier.model source (lower expression) result := by
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
            exact .lam ((nominal_lowering_exact body within (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | lam bodyTyped bounded =>
            exact .lam ((nominal_lowering_exact body within (related.mono _) _).mpr bodyTyped) bounded
  | app first last =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | app functionTyped argumentTyped bounded =>
            exact .app ((nominal_lowering_exact first within.1 related _).mp functionTyped)
              ((nominal_lowering_exact last within.2 related _).mp argumentTyped) bounded
      · intro typed; cases typed with
        | app functionTyped argumentTyped bounded =>
            exact .app ((nominal_lowering_exact first within.1 related _).mpr functionTyped)
              ((nominal_lowering_exact last within.2 related _).mpr argumentTyped) bounded
  | strictApp first last =>
      simp only [covered, Bool.and_eq_true] at within
      change _ ↔ PresenceGeneration.Typing CommonNominalCarrier.model source
        (CommonNominalStrictApplication.forceApplication (lower first) (lower last)) result
      rw [CommonNominalStrictApplication.forceApplication_typing_exact source (lower first) (lower last) result]
      constructor
      · intro typed; cases typed with
        | strictApp functionTyped argumentTyped compatible bounded =>
            exact .app ((nominal_lowering_exact first within.1 related _).mp functionTyped)
              ((nominal_lowering_exact last within.2 related _).mp argumentTyped) compatible bounded
      · intro typed; cases typed with
        | app functionTyped argumentTyped compatible bounded =>
            exact .strictApp ((nominal_lowering_exact first within.1 related _).mpr functionTyped)
              ((nominal_lowering_exact last within.2 related _).mpr argumentTyped) compatible bounded
  | letE name value body =>
      simp only [covered, Bool.and_eq_true] at within
      have polyRelated : EnvRel CommonNominalCarrier.model (.poly value environment :: environment)
          (.poly (lower value) source :: source) :=
        related.cons (fun result => by
          simp only [poly_iff, source_poly_iff]
          exact and_congr (nominal_lowering_exact value within.1 related _) Iff.rfl)
      constructor
      · intro typed; cases typed with
        | letValue nonexpansive valueTyped bodyTyped =>
            exact .letValue (by simpa only [lower_isValue value within.1] using nonexpansive)
              ((nominal_lowering_exact value within.1 related _).mp valueTyped)
              ((nominal_lowering_exact body within.2 polyRelated _).mp bodyTyped)
        | letComputed valueTyped bodyTyped bounded =>
            exact .letComputed ((nominal_lowering_exact value within.1 related _).mp valueTyped)
              ((nominal_lowering_exact body within.2 (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | letValue nonexpansive valueTyped bodyTyped =>
            exact .letValue (by simpa only [lower_isValue value within.1] using nonexpansive)
              ((nominal_lowering_exact value within.1 related _).mpr valueTyped)
              ((nominal_lowering_exact body within.2 polyRelated _).mpr bodyTyped)
        | letComputed valueTyped bodyTyped bounded =>
            exact .letComputed ((nominal_lowering_exact value within.1 related _).mpr valueTyped)
              ((nominal_lowering_exact body within.2 (related.mono _) _).mpr bodyTyped) bounded
  | leaf body =>
      constructor
      · intro typed; cases typed with
        | leaf bodyTyped => exact (nominal_lowering_exact body within related _).mp bodyTyped
      · intro typed; exact .leaf ((nominal_lowering_exact body within related _).mpr typed)
  | caseE subject arms =>
      obtain ⟨name, body, rfl, subjectWithin, bodyWithin⟩ := (covered_case_iff subject arms).mp within
      change _ ↔ PresenceGeneration.Typing CommonNominalCarrier.model source
        (CommonNominalNamedCase.caseName (lower subject) (lower body)) result
      rw [CommonNominalNamedCase.lowering_exact source (lower subject) (lower body) result]
      constructor
      · intro typed; cases typed with
        | caseName subjectTyped bodyTyped bounded =>
            exact .bind ((nominal_lowering_exact subject subjectWithin related _).mp subjectTyped)
              ((nominal_lowering_exact body bodyWithin (related.mono _) _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | bind subjectTyped bodyTyped bounded =>
            exact .caseName ((nominal_lowering_exact subject subjectWithin related _).mpr subjectTyped)
              ((nominal_lowering_exact body bodyWithin (related.mono _) _).mpr bodyTyped) bounded
  | branch condition yes no =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | branch conditionTyped yesTyped noTyped bounded =>
            exact .branch ((nominal_lowering_exact condition within.1.1 related _).mp conditionTyped)
              ((nominal_lowering_exact yes within.1.2 related _).mp yesTyped)
              ((nominal_lowering_exact no within.2 related _).mp noTyped) bounded
      · intro typed; cases typed with
        | branch conditionTyped yesTyped noTyped bounded =>
            exact .branch ((nominal_lowering_exact condition within.1.1 related _).mpr conditionTyped)
              ((nominal_lowering_exact yes within.1.2 related _).mpr yesTyped)
              ((nominal_lowering_exact no within.2 related _).mpr noTyped) bounded
  | pair first last =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | pair firstTyped lastTyped bounded =>
            exact .pair ((nominal_lowering_exact first within.1 related _).mp firstTyped)
              ((nominal_lowering_exact last within.2 related _).mp lastTyped) bounded
      · intro typed; cases typed with
        | pair firstTyped lastTyped bounded =>
            exact .pair ((nominal_lowering_exact first within.1 related _).mpr firstTyped)
              ((nominal_lowering_exact last within.2 related _).mpr lastTyped) bounded
  | fst body =>
      constructor
      · intro typed; cases typed with
        | fst bodyTyped bounded => exact .fst ((nominal_lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | fst bodyTyped bounded => exact .fst ((nominal_lowering_exact body within related _).mpr bodyTyped) bounded
  | snd body =>
      constructor
      · intro typed; cases typed with
        | snd bodyTyped bounded => exact .snd ((nominal_lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | snd bodyTyped bounded => exact .snd ((nominal_lowering_exact body within related _).mpr bodyTyped) bounded
  | emptyRecord =>
      constructor
      · intro typed; cases typed; exact .emptyRecord ‹_›
      · intro typed; cases typed; exact .emptyRecord ‹_›
  | record label head tail =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | record headTyped tailTyped width bounded =>
            exact .record ((nominal_lowering_exact head within.1 related _).mp headTyped)
              ((nominal_lowering_exact tail within.2 related _).mp tailTyped) width bounded
      · intro typed; cases typed with
        | record headTyped tailTyped width bounded =>
            exact .record ((nominal_lowering_exact head within.1 related _).mpr headTyped)
              ((nominal_lowering_exact tail within.2 related _).mpr tailTyped) width bounded
  | recordDefault label initial fallback =>
      simp only [covered, Bool.and_eq_true] at within
      constructor
      · intro typed; cases typed with
        | recordDefault sourceTyped fallbackTyped width bounded =>
            exact .recordDefault ((nominal_lowering_exact initial within.1 related _).mp sourceTyped)
              ((nominal_lowering_exact fallback within.2 related _).mp fallbackTyped) width bounded
      · intro typed; cases typed with
        | recordDefault sourceTyped fallbackTyped width bounded =>
            exact .recordDefault ((nominal_lowering_exact initial within.1 related _).mpr sourceTyped)
              ((nominal_lowering_exact fallback within.2 related _).mpr fallbackTyped) width bounded
  | field label body =>
      constructor
      · intro typed; cases typed with
        | field bodyTyped bounded => exact .field ((nominal_lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | field bodyTyped bounded => exact .field ((nominal_lowering_exact body within related _).mpr bodyTyped) bounded
  | variant label body =>
      constructor
      · intro typed; cases typed with
        | variant bodyTyped bounded => exact .variant ((nominal_lowering_exact body within related _).mp bodyTyped) bounded
      · intro typed; cases typed with
        | variant bodyTyped bounded => exact .variant ((nominal_lowering_exact body within related _).mpr bodyTyped) bounded
  | _ => simp [covered] at within
termination_by expression

end Yulang.Core.CommonSyntax
