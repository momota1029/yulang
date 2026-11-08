import Yulang.CommonPatternSourceElaboration
import Yulang.CommonPatternSourceScope
import Yulang.CoreScopedPatterns
import Yulang.CommonSourcePatternAllocation

/-! The real Q4 source elaboration and independent Common default typing.
The source coverage gate is checked before a default's fallback lowering can
enter the structural pattern generator. -/

namespace Yulang.CommonSourcePatternElaboration

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp Binding)
open CommonPatternEnvironment (NamedTypes semanticPrefix)
open CommonPatternSourceScope (corePrefix core_prefix_related)
open CommonSourcePatternTyping (RawTyping)
open CasePatterns (Pattern)

open CommonPatternSourceElaboration (DefaultTyped elaborate covered names_elaborate default_exact)

theorem preserved (related : CommonSyntax.EnvRel Common.model environment outer)
    (typed : RawTyping (DefaultTyped outerNames environment) types pattern input bindings) :
    covered (types.map Prod.fst ++ outerNames) pattern = true ∧
      RawTyping (CommonPatternGeneration.DefaultTyping outer) types
        (elaborate (types.map Prod.fst ++ outerNames) pattern) input bindings := by
  induction typed
  all_goals try simp only [elaborate, Scoped.embed, Patterns.map, covered] at *
  case wildcard => exact ⟨True.intro, .wildcard⟩
  case bind => exact ⟨True.intro, .bind⟩
  case literal below => exact ⟨True.intro, .literal below⟩
  case intRange below bounded => exact ⟨True.intro, .intRange below bounded⟩
  case recordEnd => exact ⟨True.intro, .recordEnd⟩
  case pair p q ihp ihq =>
    have tail := ihq
    simp only [List.map_append, ← p.binding_names, List.append_assoc] at tail
    exact ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, tail.1⟩, .pair ihp.2 tail.2⟩
  case field below p q ihp ihq =>
    have tail := ihq
    simp only [List.map_append, ← p.binding_names, List.append_assoc] at tail
    exact ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, tail.1⟩, .field below ihp.2 tail.2⟩
  case defaultField below default p q ihp ihq =>
    have fallback := (default_exact outerNames related _ _ _).mp default
    have tail := ihq
    simp only [List.map_append, ← p.binding_names, List.append_assoc] at tail
    exact ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fallback.1, ihp.1⟩, tail.1⟩,
      .defaultField below fallback.2 ihp.2 tail.2⟩
  case variant p ih => exact ⟨ih.1, .variant ih.2⟩
  case or p q ihp ihq =>
    refine ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, ihq.1⟩, .or ihp.2 ?_⟩
    simpa only [Patterns.names_map, Scoped.names_embed (F := Empty)] using ihq.2
  case as p ih => exact ⟨ih.1, .as ih.2⟩
  case narrow below p ih => exact ⟨ih.1, .narrow below ih.2⟩

theorem reflected (related : CommonSyntax.EnvRel Common.model environment outer)
    (typed : RawTyping (CommonPatternGeneration.DefaultTyping outer) types pattern input bindings) :
    ∀ source, covered (types.map Prod.fst ++ outerNames) source = true →
      elaborate (types.map Prod.fst ++ outerNames) source = pattern →
      RawTyping (DefaultTyped outerNames environment) types source input bindings := by
  induction typed
  all_goals intro source within syntaxEq
  case narrow below typed ih => exact .narrow below (ih source within syntaxEq)
  all_goals cases source <;> simp only [elaborate, Scoped.embed, Patterns.map] at syntaxEq
  all_goals cases syntaxEq
  case pair.pair.refl =>
    rename_i types a left b right p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by
      simpa only [Patterns.names_map, Scoped.names_embed (F := Empty)] using hp.binding_names.symm
    simp only [covered, Bool.and_eq_true] at within
    exact .pair (ihp p within.1 rfl)
      (ihq q (by simpa only [List.map_append, names, List.append_assoc] using within.2)
        (by simp only [List.map_append, names, List.append_assoc, elaborate]))
  case field.field.refl =>
    rename_i input name payload types left right below p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by
      simpa only [Patterns.names_map, Scoped.names_embed (F := Empty)] using hp.binding_names.symm
    simp only [covered, Bool.and_eq_true] at within
    exact .field below (ihp p within.1 rfl)
      (ihq q (by simpa only [List.map_append, names, List.append_assoc] using within.2)
        (by simp only [List.map_append, names, List.append_assoc, elaborate]))
  case defaultField.defaultField.refl =>
    rename_i name input payload types fallbackType left right below fallback p q default hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by
      simpa only [Patterns.names_map, Scoped.names_embed (F := Empty)] using hp.binding_names.symm
    simp only [covered, Bool.and_eq_true] at within
    exact .defaultField below ((default_exact outerNames related _ _ _).mpr ⟨within.1.1, default⟩)
      (ihp p within.1.2 rfl)
      (ihq q (by simpa only [List.map_append, names, List.append_assoc] using within.2)
        (by simp only [List.map_append, names, List.append_assoc, elaborate]))
  case or.or.refl =>
    rename_i types input bindings p q hp ihp hq ihq
    simp only [covered, Bool.and_eq_true] at within
    apply RawTyping.or (ihp p within.1 rfl)
    simpa only [Patterns.names_map, Scoped.names_embed (F := Empty)] using ihq q within.2 rfl
  all_goals first
    | apply RawTyping.wildcard
    | apply RawTyping.bind
    | apply RawTyping.literal <;> assumption
    | apply RawTyping.intRange <;> assumption
    | apply RawTyping.recordEnd
    | apply RawTyping.variant
    | apply RawTyping.as
  all_goals apply_assumption <;> first | assumption | rfl

theorem raw_typing_exact (related : CommonSyntax.EnvRel Common.model environment outer)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (types : NamedTypes)
    (input : Common.Ty) (bindings : NamedTypes) :
    RawTyping (DefaultTyped outerNames environment) types pattern input bindings ↔
      covered (types.map Prod.fst ++ outerNames) pattern = true ∧
      RawTyping (CommonPatternGeneration.DefaultTyping outer) types
        (elaborate (types.map Prod.fst ++ outerNames) pattern) input bindings :=
  ⟨preserved related, fun ⟨within, typed⟩ => reflected related typed pattern within rfl⟩

open CommonPatternSourceElaboration (check_elaborate)

theorem source_typing_exact (related : CommonSyntax.EnvRel Common.model environment outer)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (types : NamedTypes)
    (input : Common.Ty) (bindings : NamedTypes) :
    CommonSourcePatternTyping.Typing (DefaultTyped outerNames environment) types pattern input bindings ↔
      covered (types.map Prod.fst ++ outerNames) pattern = true ∧
      CommonSourcePatternTyping.Typing (CommonPatternGeneration.DefaultTyping outer) types
        (elaborate (types.map Prod.fst ++ outerNames) pattern) input bindings := by
  have names : PatternBindingChecks.NamesValid (elaborate (types.map Prod.fst ++ outerNames) pattern) ↔
      PatternBindingChecks.NamesValid pattern := by
    rw [← PatternBindingChecks.check_exact, ← PatternBindingChecks.check_exact, check_elaborate]
  simp only [CommonSourcePatternTyping.Typing, names, raw_typing_exact related]
  exact and_left_comm

open PresenceGeneration (SchemeEnv TyTerm Formula)
open CommonPatternEnvironment (NamedTerms evalTypes evalTypes_names)

def generateSourcePattern (outerNames : List Nat) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (input : TyTerm α) : Formula α :=
  let scope := priorBindings.map Prod.fst ++ outerNames
  if covered scope pattern then
    CommonSourcePatternAllocation.generateCheckedPattern (elaborate scope pattern) environment priorBindings input
  else .bot

/-- Every actual named source pattern/default, arbitrary captured outer
environment, cumulative symbolic prefix, input type and slot assignment.
Both the coverage check and Q7 are part of the finite algorithm. The target
judgment remains the structural Common carrier, not the full B2 judgment. -/
theorem generateSourcePattern_exact (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (outerNames : List Nat) (assignment : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : PresenceGeneration.EnvRel Common.model assignment symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) :
    (generateSourcePattern outerNames symbolic priorBindings pattern input).Holds Common.model assignment ↔
      ∃ bindings, CommonSourcePatternTyping.Typing (DefaultTyped outerNames environment)
        (evalTypes assignment priorBindings) pattern (input.eval Common.model assignment) bindings := by
  simp only [source_typing_exact coreRelated pattern, evalTypes_names]
  cases within : covered (priorBindings.map Prod.fst ++ outerNames) pattern with
  | false => simp only [generateSourcePattern, within, Bool.false_eq_true, ↓reduceIte, Formula.Holds,
      false_and, exists_false]
  | true =>
      simp only [generateSourcePattern, within, ↓reduceIte, true_and]
      exact CommonSourcePatternAllocation.generateCheckedPattern_exact _ assignment symbolic semantic
        symbolicRelated priorBindings input

end Yulang.CommonSourcePatternElaboration
