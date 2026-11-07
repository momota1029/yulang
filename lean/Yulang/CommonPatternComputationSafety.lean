import Yulang.CommonPatternComputations
import Yulang.CommonAlignedPatternPartialSafety

/-! Structural partial correctness for arbitrary computations. The explicit
logic interface may speak about all finite prefixes of a nonterminating
computation. Nothing here requires a default to produce one finite result.
An adequacy instance for the general source semantics remains a B3 bridge. -/

namespace Yulang.CommonPatternComputationSafety

set_option backward.isDefEq.respectTransparency false

open CommonPatternComputations (Ops run andThen align)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (valueAt bindingTypes bindingTypes_append)
open CommonPatternLookup
open CommonAlignedPatternTyping (RawTyping)
open CommonPatternBindingAlignment (reorder)
open CaseValues (Bindings BindingsHold)
open Core.CommonData (Value)

structure Logic {M : Type → Type} (ops : Ops M) where
  Safe : {A : Type} → M A → (A → Prop) → Common.Row → Prop
  ret_safe : ∀ {A} (value : A) post cap, post value → Safe (ops.ret value) post cap
  bind_safe : ∀ {A B} {first : M A} {next : A → M B} {pre post cap},
    Safe first pre cap → (∀ value, pre value → Safe (next value) post cap) →
      Safe (ops.bind first next) post cap
  weaken : ∀ {A} {computation : M A} {pre post cap}, Safe computation pre cap →
    (∀ value, pre value → post value) → Safe computation post cap

def OptionHolds (types : NamedTypes) : Option (Bindings Empty) → Prop
  | none => True
  | some values => BindingsHold (bindingTypes types) values

def DefaultSound {M : Type → Type} {ops : Ops M} (logic : Logic ops) (cap : Common.Row)
    (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (evaluate : Bindings Empty → D → M Value) : Prop :=
  ∀ types code type, DefaultTyped types code type → ∀ actual,
    BindingsHold (bindingTypes types) actual → logic.Safe (evaluate actual code) (valueAt type) cap

theorem andThen_safe {M : Type → Type} {ops : Ops M} (logic : Logic ops)
    (first : M (Option (Bindings Empty))) (next : Bindings Empty → M (Option (Bindings Empty)))
    (headSafe : logic.Safe first (OptionHolds left) cap)
    (tailSafe : ∀ prior, BindingsHold (bindingTypes left) prior → logic.Safe (next prior) (OptionHolds right) cap) :
    logic.Safe (andThen ops first next) (OptionHolds (left ++ right)) cap := by
  apply logic.bind_safe headSafe
  intro option typed
  cases option with
  | none => exact logic.ret_safe _ _ _ True.intro
  | some prior =>
      apply logic.bind_safe (tailSafe prior typed)
      intro option moreTyped
      cases option with
      | none => exact logic.ret_safe _ _ _ True.intro
      | some more =>
          apply logic.ret_safe
          simpa only [OptionHolds, bindingTypes_append] using typed.append moreTyped

theorem option_reorder (names : List Nat) (option : Option (Bindings Empty))
    (typed : OptionHolds types option) : OptionHolds (reorder names types) (option.map (reorder names)) := by
  cases option with
  | none => trivial
  | some values =>
      change BindingsHold (bindingTypes (reorder names types)) (reorder names values)
      rw [CommonAlignedPatternPartialSafety.bindingTypes_reorder]
      exact CommonPatternBindingAlignment.reorder_bindings_hold names typed

/-- Every independent structural derivation, every typed incoming scope and
real subject, in any computation logic satisfying the stated sequencing
rules. The default contract is partial correctness, with no termination or
success condition and no named lookup-invariance requirement. -/
theorem typing_safe {M : Type → Type} {ops : Ops M} (logic : Logic ops) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool) (evaluate : Bindings Empty → D → M Value)
    (defaults : DefaultSound logic cap DefaultTyped evaluate)
    (typed : RawTyping DefaultTyped types pattern input bindings) :
    PatternBindingChecks.NamesValid pattern → ∀ environment,
      BindingsHold (bindingTypes types) environment → ∀ value, valueAt input value →
        logic.Safe (run ops floatCheck evaluate environment pattern value) (OptionHolds bindings) cap := by
  induction typed with
  | wildcard =>
      intro valid environment env value within
      exact logic.ret_safe _ _ _ .nil
  | bind =>
      intro valid environment env value within
      exact logic.ret_safe _ _ _ (.cons within .nil)
  | literal admissible =>
      intro valid environment env value within
      cases value <;> simp only [run]
      all_goals first
        | (split <;> apply logic.ret_safe <;> first | exact .nil | trivial)
        | exact logic.ret_safe _ _ _ True.intro
  | intRange admissible bounded =>
      intro valid environment env value within
      cases value <;> simp only [run]
      all_goals first
        | (split <;> apply logic.ret_safe <;> first | exact .nil | trivial)
        | exact logic.ret_safe _ _ _ True.intro
  | pair left right ihl ihr =>
      intro valid environment env value within
      cases valid with | pair vp vq apart =>
        obtain ⟨first, last, rfl, firstValid, lastValid⟩ := pair_components within _ _ (Common.subtype_refl _)
        apply andThen_safe logic _ _ (ihl vp environment env first firstValid)
        intro prior priorValid
        exact ihr vq (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append env) last lastValid
  | recordEnd =>
      intro valid environment env value within
      obtain ⟨fields, rfl⟩ := records_of_width within (Common.subtype_refl _)
      exact logic.ret_safe _ _ _ .nil
  | field below child rest ihc ihr =>
      intro valid environment env value within
      cases valid with | field vp vr apart =>
        have width := Common.subtype_trans below ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl)
        obtain ⟨fields, rfl⟩ := records_of_width within width
        obtain ⟨item, found, itemValid⟩ := required_lookup fields _ _ _ within below
        simp only [run, found]
        apply andThen_safe logic _ _ (ihc vp environment env item itemValid)
        intro prior priorValid
        exact ihr vr (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append env) (.record fields) within
  | @defaultField name input payload types fallback fallbackType p left rest right optional fallbackTyped child restTyped ihc ihr =>
      intro valid environment env value within
      cases valid with | defaultField vp vr apart =>
        have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff input).mpr
          (CommonOptionalBound.optional_payload_shape name input payload optional)
        obtain ⟨fields, rfl⟩ := records_of_width within width
        have selected : logic.Safe
            (match CaseValues.lookup name fields with
              | some item => ops.ret item
              | none => evaluate environment fallback)
            (valueAt (.union payload fallbackType)) cap := by
          cases found : CaseValues.lookup name fields with
          | some item =>
              apply logic.ret_safe
              exact typing_change_result (optional_lookup fields _ name payload item within optional found) _
                (CommonBoundCoalescing.le_union_left _ _)
          | none =>
              apply logic.weaken (defaults types fallback fallbackType fallbackTyped environment env)
              intro item itemValid
              exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_right _ _)
        simp only [run]
        cases found : CaseValues.lookup name fields <;> simp only [found] at selected ⊢
        all_goals
          apply logic.bind_safe selected
          intro item itemValid
          apply andThen_safe logic _ _ (ihc vp environment env item itemValid)
          intro prior priorValid
          exact ihr vr (prior ++ environment)
            (by simpa only [bindingTypes_append] using priorValid.append env) (.record fields) within
  | variant child ih =>
      intro valid environment env value within
      cases valid with | variant vp =>
        obtain ⟨item, rfl, itemValid⟩ := variant_payload within _ _ (Common.subtype_refl _)
        simpa only [run, ↓reduceIte] using ih vp environment env item itemValid
  | @or types p input bindings q left right ihl ihr =>
      intro valid environment env value within
      cases valid with | or vp vq names =>
        have bindingNames := left.binding_names.symm
        have distinct := CommonPatternMatchPaths.source_names_nodup p vp
        have self : reorder p.names bindings = bindings := by
          rw [← bindingNames]
          exact CommonPatternBindingAlignment.reorder_self bindings (bindingNames ▸ distinct)
        have roundtrip : reorder p.names (reorder q.names bindings) = bindings :=
          CommonPatternBindingAlignment.reorder_roundtrip p.names q.names bindings bindingNames distinct
            (fun name member => (names name).mp member)
        simp only [run, align]
        apply logic.bind_safe (pre := fun option : Option (Bindings Empty) =>
          OptionHolds bindings (option.map (reorder p.names)))
        ·
          apply logic.bind_safe (ihl vp environment env value within)
          intro option returnedTyped
          cases option with
          | some values =>
              apply logic.ret_safe
              simpa only [self] using option_reorder p.names (some values) returnedTyped
          | none =>
              apply logic.weaken (ihr vq environment env value within)
              intro option returnedTyped
              simpa only [roundtrip] using option_reorder p.names option returnedTyped
        · intro option good
          exact logic.ret_safe _ _ _ good
  | as child ih =>
      intro valid environment env value within
      cases valid with | as vp fresh =>
        apply logic.bind_safe (ih vp environment env value within)
        intro option returnedTyped
        cases option with
        | none => exact logic.ret_safe _ _ _ True.intro
        | some values => exact logic.ret_safe _ _ _ (.cons within returnedTyped)
  | narrow below child ih =>
      intro valid environment env value within
      exact ih valid environment env value (typing_change_result within _ below)

end Yulang.CommonPatternComputationSafety
