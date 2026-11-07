import Yulang.CommonPatternTyping

/-!
# Removing root subsumption from the independent Common pattern rules

The root view retains the exact binding list, the default relation, and the
Q4 environments. Children still use the original independent judgment.
This is an inversion tool, not a replacement judgment for the full B2 target.
-/

namespace Yulang.CommonPatternInversion

open CommonPatternTyping (Typing)
open CommonPatternEnvironment (NamedTypes)
open CommonDefaultRequired (OptionalPayload)
open CasePatterns (Pattern)

inductive Root (DefaultTyped : NamedTypes → D → Common.Ty → Prop) :
    NamedTypes → Pattern Empty D → Common.Ty → NamedTypes → Prop where
  | wildcard : Root DefaultTyped types .wildcard input []
  | bind : Root DefaultTyped types (.bind name) input [(name, input)]
  | literal : Common.Subtype input (.base (Core.CommonData.literalBase expected)) →
      Root DefaultTyped types (.literal expected) input []
  | intRange : Common.Subtype input (.base .int) → lower.isSome ∨ upper.isSome →
      Root DefaultTyped types (.intRange lower upper) input []
  | pair : Typing DefaultTyped types p a left →
      Typing DefaultTyped (left ++ types) q b right →
      Root DefaultTyped types (.pair p q) (Common.pair a b) (left ++ right)
  | recordEnd : Root DefaultTyped types .recordEnd Common.emptyRecord []
  | field : Common.Subtype input (Common.required name payload) →
      Typing DefaultTyped types p payload left →
      Typing DefaultTyped (left ++ types) rest input right →
      Root DefaultTyped types (.field name p rest) input (left ++ right)
  | defaultField : OptionalPayload name input payload →
      DefaultTyped types fallback fallbackType →
      Typing DefaultTyped types p (.union payload fallbackType) left →
      Typing DefaultTyped (left ++ types) rest input right →
      Root DefaultTyped types (.defaultField name fallback p rest) input (left ++ right)
  | variant : Typing DefaultTyped types p payload bindings →
      Root DefaultTyped types (.variant tag p) (Common.variant tag payload) bindings
  | or : Typing DefaultTyped types p input bindings →
      Typing DefaultTyped types q input bindings →
      Root DefaultTyped types (.or p q) input bindings
  | as : Typing DefaultTyped types p input bindings →
      Root DefaultTyped types (.as p name) input ((name, input) :: bindings)

theorem Root.typing (root : Root defaults types pattern input bindings) :
    Typing defaults types pattern input bindings := by
  cases root with
  | wildcard => exact .wildcard
  | bind => exact .bind
  | literal h => exact .literal h
  | intRange h b => exact .intRange h b
  | pair h k => exact .pair h k
  | recordEnd => exact .recordEnd
  | field h p r => exact .field h p r
  | defaultField h d p r => exact .defaultField h d p r
  | variant h => exact .variant h
  | or h k => exact .or h k
  | as h => exact .as h

/-- Any finite chain of root narrowing is collapsed without changing any
binding type or accumulated environment. All Common inputs are allowed. -/
theorem typing_root_exact
    (defaults : NamedTypes → D → Common.Ty → Prop)
    (types : NamedTypes) (pattern : Pattern Empty D)
    (input : Common.Ty) (bindings : NamedTypes) :
    Typing defaults types pattern input bindings ↔
      ∃ original, Common.Subtype input original ∧
        Root defaults types pattern original bindings := by
  constructor
  · intro typed
    induction typed with
    | wildcard => exact ⟨_, Common.subtype_refl _, .wildcard⟩
    | bind => exact ⟨_, Common.subtype_refl _, .bind⟩
    | literal h => exact ⟨_, Common.subtype_refl _, .literal h⟩
    | intRange h b => exact ⟨_, Common.subtype_refl _, .intRange h b⟩
    | pair h k => exact ⟨_, Common.subtype_refl _, .pair h k⟩
    | recordEnd => exact ⟨_, Common.subtype_refl _, .recordEnd⟩
    | field h p r => exact ⟨_, Common.subtype_refl _, .field h p r⟩
    | defaultField h d p r => exact ⟨_, Common.subtype_refl _, .defaultField h d p r⟩
    | variant h => exact ⟨_, Common.subtype_refl _, .variant h⟩
    | or h k => exact ⟨_, Common.subtype_refl _, .or h k⟩
    | as h => exact ⟨_, Common.subtype_refl _, .as h⟩
    | narrow below _ ih =>
      obtain ⟨original, above, root⟩ := ih
      exact ⟨original, Common.subtype_trans below above, root⟩
  · rintro ⟨original, below, root⟩
    exact .narrow below root.typing

variable {D : Type} {defaults : NamedTypes → D → Common.Ty → Prop}
  {types bindings : NamedTypes} {input : Common.Ty}

theorem wildcard_iff : Typing defaults types (.wildcard : Pattern Empty D) input bindings ↔
    bindings = [] := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, _, root⟩; cases root; rfl
  · rintro rfl; exact ⟨_, Common.subtype_refl _, .wildcard⟩

theorem bind_iff : Typing defaults types (.bind name : Pattern Empty D) input bindings ↔
    ∃ result, bindings = [(name, result)] ∧ Common.Subtype input result := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩; cases root; exact ⟨_, rfl, below⟩
  · rintro ⟨_, rfl, below⟩; exact ⟨_, below, .bind⟩

theorem literal_iff : Typing defaults types (.literal expected : Pattern Empty D) input bindings ↔
    bindings = [] ∧ Common.Subtype input (.base (Core.CommonData.literalBase expected)) := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | literal h => exact ⟨rfl, Common.subtype_trans below h⟩
  · rintro ⟨rfl, below⟩; exact ⟨_, Common.subtype_refl _, .literal below⟩

theorem range_iff : Typing defaults types (.intRange lower upper : Pattern Empty D) input bindings ↔
    bindings = [] ∧ Common.Subtype input (.base .int) ∧ (lower.isSome ∨ upper.isSome) := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | intRange h bound => exact ⟨rfl, Common.subtype_trans below h, bound⟩
  · rintro ⟨rfl, below, bound⟩
    exact ⟨_, Common.subtype_refl _, .intRange below bound⟩

theorem pair_iff : Typing defaults types (.pair p q : Pattern Empty D) input bindings ↔
    ∃ a b left right, bindings = left ++ right ∧ Common.Subtype input (Common.pair a b) ∧
      Typing defaults types p a left ∧ Typing defaults (left ++ types) q b right := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | pair h k => exact ⟨_, _, _, _, rfl, below, h, k⟩
  · rintro ⟨_, _, _, _, rfl, below, h, k⟩; exact ⟨_, below, .pair h k⟩

theorem recordEnd_iff : Typing defaults types (.recordEnd : Pattern Empty D) input bindings ↔
    bindings = [] ∧ Common.Subtype input Common.emptyRecord := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩; cases root; exact ⟨rfl, below⟩
  · rintro ⟨rfl, below⟩; exact ⟨_, below, .recordEnd⟩

theorem field_iff : Typing defaults types (.field name p rest : Pattern Empty D) input bindings ↔
    ∃ original payload left right, bindings = left ++ right ∧ Common.Subtype input original ∧
      Common.Subtype original (Common.required name payload) ∧
      Typing defaults types p payload left ∧ Typing defaults (left ++ types) rest original right := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | field h p r => exact ⟨_, _, _, _, rfl, below, h, p, r⟩
  · rintro ⟨_, _, _, _, rfl, below, h, p, r⟩; exact ⟨_, below, .field h p r⟩

theorem defaultField_iff :
    Typing defaults types (.defaultField name fallback p rest : Pattern Empty D) input bindings ↔
    ∃ original payload fallbackType left right, bindings = left ++ right ∧
      Common.Subtype input original ∧ OptionalPayload name original payload ∧
      defaults types fallback fallbackType ∧ Typing defaults types p (.union payload fallbackType) left ∧
      Typing defaults (left ++ types) rest original right := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | defaultField h d p r => exact ⟨_, _, _, _, _, rfl, below, h, d, p, r⟩
  · rintro ⟨_, _, _, _, _, rfl, below, h, d, p, r⟩
    exact ⟨_, below, .defaultField h d p r⟩

theorem variant_iff : Typing defaults types (.variant tag p : Pattern Empty D) input bindings ↔
    ∃ payload, Common.Subtype input (Common.variant tag payload) ∧
      Typing defaults types p payload bindings := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | variant p => exact ⟨_, below, p⟩
  · rintro ⟨_, below, p⟩; exact ⟨_, below, .variant p⟩

theorem or_iff : Typing defaults types (.or p q : Pattern Empty D) input bindings ↔
    Typing defaults types p input bindings ∧ Typing defaults types q input bindings := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | or p q => exact ⟨.narrow below p, .narrow below q⟩
  · rintro ⟨p, q⟩; exact ⟨_, Common.subtype_refl _, .or p q⟩

theorem as_iff : Typing defaults types (.as p name : Pattern Empty D) input bindings ↔
    ∃ original rest, bindings = (name, original) :: rest ∧ Common.Subtype input original ∧
      Typing defaults types p original rest := by
  rw [typing_root_exact]
  constructor
  · rintro ⟨_, below, root⟩
    cases root with | as p => exact ⟨_, _, rfl, below, p⟩
  · rintro ⟨_, _, rfl, below, p⟩; exact ⟨_, below, .as p⟩

end Yulang.CommonPatternInversion
