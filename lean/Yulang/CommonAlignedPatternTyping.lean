import Yulang.CommonPatternTyping
import Yulang.CommonPatternBindingAlignment
import Yulang.PatternBindingChecks

/-!
# Independent Common pattern typing with source or-name alignment

The right alternative is checked in its own written binder order using the
same name-indexed output types. Each completed or boundary exposes the left
alternative's name interface, as in CommonPatternAlignedMatcher. All other
Q4 scopes and pure monomorphic binders remain the original independent rules.
No constraint formula or successful runtime match defines these rules.
-/

namespace Yulang.CommonAlignedPatternTyping

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
  | field : Common.Subtype input (Common.required name payload) →
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

end Yulang.CommonAlignedPatternTyping
