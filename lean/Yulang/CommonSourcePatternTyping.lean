import Yulang.CommonAlignedPatternTyping
import Yulang.CommonOptionalBound
import Yulang.CommonPatternTyping
import Yulang.CommonPatternBindingAlignment
import Yulang.PatternBindingChecks

/-!
# Source structural patterns with optional-input field matching

T2 / X22, spec/03b-patterns.md §3b.3: a field without a default
requires presence only on success; absent fields miss. This additive
successor to CommonAlignedPatternTyping changes that rule recursively,
including nested fields, and preserves Q4 scopes and source-name alignment.
The old judgment, generator and strict rejection theorems remain unchanged.
Lists/nominals and the public Core.infer integration remain outside this
structural fragment; this module does not claim full B2 completion.
-/

namespace Yulang.CommonSourcePatternTyping

open CommonPatternEnvironment (NamedTypes)
open CommonDefaultRequired (OptionalPayload)
open CommonPatternBindingAlignment (reorder)
open CasePatterns (Pattern)

inductive RawTyping (DefaultTyped : NamedTypes → D → Common.Ty → Prop) :
    NamedTypes → Pattern Empty D → Common.Ty → NamedTypes → Prop where
  | wildcard : RawTyping DefaultTyped types .wildcard input []
  | bind : RawTyping DefaultTyped types (.bind name) input [(name, input)]
  | literal : Common.Subtype input (.base (Core.CommonData.literalBase expected)) →
      RawTyping DefaultTyped types (.literal expected) input []
  | intRange : Common.Subtype input (.base .int) → lower.isSome ∨ upper.isSome →
      RawTyping DefaultTyped types (.intRange lower upper) input []
  | pair : RawTyping DefaultTyped types p a left →
      RawTyping DefaultTyped (left ++ types) q b right →
      RawTyping DefaultTyped types (.pair p q) (Common.pair a b) (left ++ right)
  | recordEnd : RawTyping DefaultTyped types .recordEnd Common.emptyRecord []
  | field : OptionalPayload name input payload →
      RawTyping DefaultTyped types p payload left →
      RawTyping DefaultTyped (left ++ types) rest input right →
      RawTyping DefaultTyped types (.field name p rest) input (left ++ right)
  | defaultField : OptionalPayload name input payload →
      DefaultTyped types fallback fallbackType →
      RawTyping DefaultTyped types p (.union payload fallbackType) left →
      RawTyping DefaultTyped (left ++ types) rest input right →
      RawTyping DefaultTyped types (.defaultField name fallback p rest) input (left ++ right)
  | variant : RawTyping DefaultTyped types p payload bindings →
      RawTyping DefaultTyped types (.variant tag p) (Common.variant tag payload) bindings
  | or : RawTyping DefaultTyped types p input bindings →
      RawTyping DefaultTyped types q input (reorder q.names bindings) →
      RawTyping DefaultTyped types (.or p q) input bindings
  | as : RawTyping DefaultTyped types p input bindings →
      RawTyping DefaultTyped types (.as p name) input ((name, input) :: bindings)
  | narrow : Common.Subtype input original →
      RawTyping DefaultTyped types p original bindings →
      RawTyping DefaultTyped types p input bindings

/-- Source traversal order is retained exactly, including the outer `as`
binder before its child. Or alternatives share types by resolved name. -/
theorem RawTyping.binding_names (typed : RawTyping DefaultTyped types pattern input bindings) :
    pattern.names = bindings.map Prod.fst := by
  induction typed
  case or left right leftIH rightIH => exact leftIH
  all_goals simp_all [Pattern.names]

/-- The source name check is an independent judgment and includes Q7. -/
def Typing (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (types : NamedTypes) (pattern : Pattern Empty D) (input : Common.Ty) (bindings : NamedTypes) : Prop :=
  PatternBindingChecks.NamesValid pattern ∧ RawTyping DefaultTyped types pattern input bindings

/-- Required presence implies the new optional-payload condition. This does
not assert that defaults are legal on a declared required field. -/
theorem required_optional {input payload : Common.Ty} {name : Nat}
    (required : Common.Subtype input (Common.required name payload)) :
    OptionalPayload name input payload := by
  have head : OptionalPayload name (Common.required name payload) payload :=
    (CommonDefaultRequired.optionalPayload_record_same name payload Common.emptyRecord payload).mpr
      (Common.subtype_refl _)
  exact (CommonOptionalBound.optional_payload_bound_exact name input payload).mpr
    (Common.subtype_trans required
      ((CommonOptionalBound.optional_payload_bound_exact name _ payload).mp head))

/-- Every derivation of the historical structural judgment is retained with
exactly the same defaults, environments, pattern, input and binding types. -/
theorem legacy_preserved
    (typed : CommonAlignedPatternTyping.RawTyping defaults types pattern input bindings) :
    RawTyping defaults types pattern input bindings := by
  induction typed with
  | wildcard => exact .wildcard
  | bind => exact .bind
  | literal h => exact .literal h
  | intRange h b => exact .intRange h b
  | pair p q ihp ihq => exact .pair ihp ihq
  | recordEnd => exact .recordEnd
  | field h p r ihp ihr => exact .field (required_optional h) ihp ihr
  | defaultField h d p r ihp ihr => exact .defaultField h d ihp ihr
  | variant p ih => exact .variant ih
  | or p q ihp ihq => exact .or ihp ihq
  | as p ih => exact .as ih
  | narrow h p ih => exact .narrow h ih

end Yulang.CommonSourcePatternTyping
