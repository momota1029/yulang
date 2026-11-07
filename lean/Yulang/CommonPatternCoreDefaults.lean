import Yulang.CommonPatternSourceElaboration
import Yulang.CommonPatternFormulaEquivalence
import Yulang.CommonAlignedPatternGenerationProvenance

/-! Structural pattern allocation with actual independent Core defaults.
The Core terms already use the de Bruijn indices of their Q4 cumulative
environment. No data-expression embedding or runtime termination premise is
used by this static bridge. The original CommonSyntax judgment still bounds
the term language; operation syntax and the full B5 carrier remain separate. -/

namespace Yulang.CommonPatternCoreDefaults

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternSourceScope (corePrefix core_prefix_related)
open CommonAlignedPatternTyping (RawTyping)
open CasePatterns (Pattern)

def DefaultTyped (environment : List (CommonSyntax.Binding Common.model))
    (types : NamedTypes) (code : Required.Term) (type : Common.Ty) : Prop :=
  ∃ row, CommonSyntax.Typing Common.model (corePrefix types ++ environment) code (type, row)

def lower (pattern : Pattern Empty Required.Term) : Pattern Empty Inference.Expr :=
  Patterns.map CommonSyntax.lower pattern

@[simp] theorem names_lower (pattern : Pattern Empty Required.Term) :
    (lower pattern).names = pattern.names := Patterns.names_map _ _

def covered : Pattern Empty Required.Term → Bool
  | .wildcard | .bind _ | .literal _ | .intRange _ _ | .recordEnd | .nil => true
  | .pair p q | .field _ p q | .cons p q | .snoc p q | .or p q => covered p && covered q
  | .defaultField _ code p q => CommonSyntax.covered code && covered p && covered q
  | .variant _ p | .nominal _ _ p | .as p _ => covered p

theorem default_exact (related : CommonSyntax.EnvRel Common.model environment outer)
    (types : NamedTypes) (code : Required.Term) (type : Common.Ty) :
    DefaultTyped environment types code type ↔ CommonSyntax.covered code = true ∧
      CommonPatternGeneration.DefaultTyping outer types (CommonSyntax.lower code) type := by
  constructor
  · rintro ⟨row, typed⟩
    have within := CommonSyntax.typing_covered typed
    exact ⟨within, row, (CommonSyntax.lowering_exact _ within (core_prefix_related types related) _).mp typed⟩
  · rintro ⟨within, row, typed⟩
    exact ⟨row, (CommonSyntax.lowering_exact _ within (core_prefix_related types related) _).mpr typed⟩

theorem preserved (related : CommonSyntax.EnvRel Common.model environment outer)
    (typed : RawTyping (DefaultTyped environment) types pattern input bindings) :
    covered pattern = true ∧ RawTyping (CommonPatternGeneration.DefaultTyping outer)
      types (lower pattern) input bindings := by
  induction typed
  all_goals try simp only [lower, Patterns.map, covered] at *
  case wildcard => exact ⟨True.intro, .wildcard⟩
  case bind => exact ⟨True.intro, .bind⟩
  case literal below => exact ⟨True.intro, .literal below⟩
  case intRange below bounded => exact ⟨True.intro, .intRange below bounded⟩
  case recordEnd => exact ⟨True.intro, .recordEnd⟩
  case pair p q ihp ihq => exact ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, ihq.1⟩, .pair ihp.2 ihq.2⟩
  case field below p q ihp ihq => exact ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, ihq.1⟩, .field below ihp.2 ihq.2⟩
  case defaultField below default p q ihp ihq =>
    have fallback := (default_exact related _ _ _).mp default
    exact ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fallback.1, ihp.1⟩, ihq.1⟩,
      .defaultField below fallback.2 ihp.2 ihq.2⟩
  case variant p ih => exact ⟨ih.1, .variant ih.2⟩
  case or p q ihp ihq =>
    exact ⟨Bool.and_eq_true_iff.mpr ⟨ihp.1, ihq.1⟩, .or ihp.2 (by simpa only [Patterns.names_map] using ihq.2)⟩
  case as p ih => exact ⟨ih.1, .as ih.2⟩
  case narrow below p ih => exact ⟨ih.1, .narrow below ih.2⟩

theorem reflected (related : CommonSyntax.EnvRel Common.model environment outer)
    (typed : RawTyping (CommonPatternGeneration.DefaultTyping outer) types pattern input bindings) :
    ∀ source, covered source = true → lower source = pattern →
      RawTyping (DefaultTyped environment) types source input bindings := by
  induction typed
  all_goals intro source within syntaxEq
  case narrow below typed ih => exact .narrow below (ih source within syntaxEq)
  all_goals cases source <;> simp only [lower, Patterns.map] at syntaxEq
  all_goals cases syntaxEq
  case pair.pair.refl =>
    rename_i types a left b right p q hp ihp hq ihq
    simp only [covered, Bool.and_eq_true] at within
    exact .pair (ihp p within.1 rfl) (ihq q within.2 rfl)
  case field.field.refl =>
    rename_i input name payload types left right below p q hp ihp hq ihq
    simp only [covered, Bool.and_eq_true] at within
    exact .field below (ihp p within.1 rfl) (ihq q within.2 rfl)
  case defaultField.defaultField.refl =>
    rename_i name input payload types fallbackType left right below fallback p q default hp ihp hq ihq
    simp only [covered, Bool.and_eq_true] at within
    exact .defaultField below ((default_exact related _ _ _).mpr ⟨within.1.1, default⟩)
      (ihp p within.1.2 rfl) (ihq q within.2 rfl)
  case or.or.refl =>
    rename_i types input bindings p q hp ihp hq ihq
    simp only [covered, Bool.and_eq_true] at within
    apply RawTyping.or (ihp p within.1 rfl)
    simpa only [Patterns.names_map] using ihq q within.2 rfl
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
    (pattern : Pattern Empty Required.Term) (types : NamedTypes) (input : Common.Ty) (bindings : NamedTypes) :
    RawTyping (DefaultTyped environment) types pattern input bindings ↔ covered pattern = true ∧
      RawTyping (CommonPatternGeneration.DefaultTyping outer) types (lower pattern) input bindings :=
  ⟨preserved related, fun ⟨within, typed⟩ => reflected related typed pattern within rfl⟩

@[simp] theorem check_lower (pattern : Pattern Empty Required.Term) :
    PatternBindingChecks.check (lower pattern) = PatternBindingChecks.check pattern := by
  induction pattern <;> simp_all only [lower, Patterns.map, PatternBindingChecks.check, Patterns.names_map]

theorem typing_exact (related : CommonSyntax.EnvRel Common.model environment outer)
    (pattern : Pattern Empty Required.Term) (types : NamedTypes) (input : Common.Ty) (bindings : NamedTypes) :
    CommonAlignedPatternTyping.Typing (DefaultTyped environment) types pattern input bindings ↔
      covered pattern = true ∧ CommonAlignedPatternTyping.Typing
        (CommonPatternGeneration.DefaultTyping outer) types (lower pattern) input bindings := by
  have names : PatternBindingChecks.NamesValid (lower pattern) ↔ PatternBindingChecks.NamesValid pattern := by
    rw [← PatternBindingChecks.check_exact, ← PatternBindingChecks.check_exact, check_lower]
  simp only [CommonAlignedPatternTyping.Typing, names, raw_typing_exact related]
  exact and_left_comm

def generatePattern (environment : SchemeEnv α) (prior : NamedTerms α)
    (pattern : Pattern Empty Required.Term) (input : TyTerm α) : Formula α :=
  if covered pattern then CommonAlignedPatternAllocation.generateCheckedPattern (lower pattern) environment prior input
  else .bot

/-- All Core terms are quantified, with unsupported terms rejected internally.
Defaults see the actual cumulative pure monomorphic Q4 environment. -/
theorem generatePattern_exact (pattern : Pattern Empty Required.Term)
    (assignment : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model assignment symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α) :
    (generatePattern symbolic prior pattern input).Holds Common.model assignment ↔
      ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyped environment)
        (evalTypes assignment prior) pattern (input.eval Common.model assignment) bindings := by
  simp only [typing_exact coreRelated pattern]
  cases within : covered pattern with
  | false => simp only [generatePattern, within, Bool.false_eq_true, ↓reduceIte, Formula.Holds, false_and, exists_false]
  | true =>
      simp only [generatePattern, within, ↓reduceIte, true_and]
      exact CommonAlignedPatternAllocation.generateCheckedPattern_exact _ assignment symbolic semantic symbolicRelated prior input

open CommonPatternGenerationProvenance (SafeFormula SafeEnvironment GoodBindings Input)

theorem safe_generatePattern (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (prior : NamedTerms α) (priorGood : GoodBindings prior) (pattern : Pattern Empty Required.Term)
    (input : TyTerm α) (inputGood : Input input) : SafeFormula (generatePattern environment prior pattern input) := by
  unfold generatePattern
  split
  · unfold CommonAlignedPatternAllocation.generateCheckedPattern
    split
    · exact CommonAlignedPatternGenerationProvenance.safe_allocated _ environment environmentGood prior priorGood input inputGood
    · exact .bot
  · exact .bot

end Yulang.CommonPatternCoreDefaults
