import Yulang.Types

/-!
# Literal payloads and parameterized pattern comparison

Spec §3.1 fixes arbitrary-precision integers and IEEE binary64 decimal values;
§3b.1 fixes numeric float equality. `Binary64` provides that concrete model.
This generic layer also remains useful for the existing float-free proofs.
Integers below use `Int`, strings use decoded `String`, and booleans and unit
retain their values. `FloatValue` is an explicit parameter. The executable
pattern comparison has a supplied float comparator with a separately stated
relation; no reflexivity is assumed for that relation.

`DecimalToken` records an already decoded finite decimal as sign, arbitrary
precision significand and decimal exponent. It is syntax data, not a decision
to interpret the language's `float` as an exact decimal number. `ofDecimal`
requires an explicit interpretation. Lexer/string-escape correctness and a
particular float interpretation are outside this module.
-/

namespace Yulang.LiteralValues

structure DecimalToken where
  negative : Bool
  significand : Nat
  exponent : Int
  deriving DecidableEq, Repr

/-- A leading minus is retained even when the significand is zero. -/
def DecimalToken.negate (token : DecimalToken) : DecimalToken :=
  { token with negative := !token.negative }

@[simp] theorem DecimalToken.negate_negate (token : DecimalToken) :
    token.negate.negate = token := by
  cases token
  simp [DecimalToken.negate]

inductive Kind where
  | int | float | str | bool | unit
  deriving DecidableEq, Repr

inductive Literal (FloatValue : Type := Empty) where
  | int : Int → Literal FloatValue
  | float : FloatValue → Literal FloatValue
  | str : String → Literal FloatValue
  | bool : Bool → Literal FloatValue
  | unit : Literal FloatValue
  deriving DecidableEq, Repr

def Literal.kind : Literal FloatValue → Kind
  | .int _ => .int
  | .float _ => .float
  | .str _ => .str
  | .bool _ => .bool
  | .unit => .unit

/-- The legacy inference core has no `float` base constructor. -/
def Literal.legacyBase : Literal FloatValue → Option Inference.Base
  | .int _ => some .int
  | .float _ => none
  | .str _ => some .str
  | .bool _ => some .bool
  | .unit => some .unit

def ofDecimal (interpret : DecimalToken → FloatValue) (token : DecimalToken) :
    Literal FloatValue := .float (interpret token)

@[simp] theorem ofDecimal_kind (interpret : DecimalToken → FloatValue)
    (token : DecimalToken) : (ofDecimal interpret token).kind = .float := rfl

/-- Equality of stored payloads, separate from the language float comparison. -/
def eqCheck [DecidableEq FloatValue] (left right : Literal FloatValue) : Bool :=
  decide (left = right)

theorem eqCheck_exact [DecidableEq FloatValue] (left right : Literal FloatValue) :
    eqCheck left right = true ↔ left = right := by
  simp [eqCheck]

/-- Independent literal-pattern judgement. Distinct literal kinds never match. -/
inductive Matches (floatRel : FloatValue → FloatValue → Prop) :
    Literal FloatValue → Literal FloatValue → Prop where
  | int (value : Int) : Matches floatRel (.int value) (.int value)
  | float : floatRel left right → Matches floatRel (.float left) (.float right)
  | str (value : String) : Matches floatRel (.str value) (.str value)
  | bool (value : Bool) : Matches floatRel (.bool value) (.bool value)
  | unit : Matches floatRel .unit .unit

def matchCheck (floatCheck : FloatValue → FloatValue → Bool) :
    Literal FloatValue → Literal FloatValue → Bool
  | .int left, .int right => decide (left = right)
  | .float left, .float right => floatCheck left right
  | .str left, .str right => decide (left = right)
  | .bool left, .bool right => decide (left = right)
  | .unit, .unit => true
  | _, _ => false

theorem matchCheck_exact (floatCheck : FloatValue → FloatValue → Bool)
    (floatRel : FloatValue → FloatValue → Prop)
    (floatExact : ∀ left right, floatCheck left right = true ↔ floatRel left right)
    (left right : Literal FloatValue) :
    matchCheck floatCheck left right = true ↔ Matches floatRel left right := by
  constructor
  · intro checked
    cases left <;> cases right <;> simp only [matchCheck] at checked
    all_goals first | contradiction | skip
    · exact (of_decide_eq_true checked) ▸ Matches.int _
    · exact .float ((floatExact _ _).mp checked)
    · exact (of_decide_eq_true checked) ▸ Matches.str _
    · exact (of_decide_eq_true checked) ▸ Matches.bool _
    · exact .unit
  · intro matched
    cases matched with
    | int value => simp [matchCheck]
    | float related => exact (floatExact _ _).mpr related
    | str value => simp [matchCheck]
    | bool value => simp [matchCheck]
    | unit => rfl

theorem matches_kind (floatRel : FloatValue → FloatValue → Prop)
    {left right : Literal FloatValue} (matched : Matches floatRel left right) :
    left.kind = right.kind := by
  cases matched <;> rfl

theorem kind_mismatch_rejects (floatCheck : FloatValue → FloatValue → Bool)
    (left right : Literal FloatValue) (different : left.kind ≠ right.kind) :
    matchCheck floatCheck left right = false := by
  cases left <;> cases right <;> simp_all [Literal.kind, matchCheck]

/-- Every float-free literal pattern uses ordinary exact payload equality. -/
theorem matches_without_floats (floatRel : Empty → Empty → Prop)
    (left right : Literal Empty) : Matches floatRel left right ↔ left = right := by
  constructor
  · intro matched
    cases matched with
    | int | str | bool | unit => rfl
    | float related => contradiction
  · intro same
    subst right
    cases left with
    | int value => exact .int value
    | float impossible => exact Empty.elim impossible
    | str value => exact .str value
    | bool value => exact .bool value
    | unit => exact .unit

/-- Closed integer bounds are the pattern meaning fixed by spec §3b.1.
The helper permits two absent bounds; source syntax must reject bare `..`. -/
def InIntRange (lower upper : Option Int) (value : Int) : Prop :=
  (∀ bound, lower = some bound → bound ≤ value) ∧
  (∀ bound, upper = some bound → value ≤ bound)

def intRangeCheck (lower upper : Option Int) (value : Literal FloatValue) : Bool :=
  match value with
  | .int integer =>
      (match lower with | none => true | some bound => decide (bound ≤ integer)) &&
      (match upper with | none => true | some bound => decide (integer ≤ bound))
  | _ => false

inductive InRange (lower upper : Option Int) : Literal FloatValue → Prop where
  | int : InIntRange lower upper value → InRange lower upper (.int value)

theorem intRangeCheck_exact (lower upper : Option Int) (value : Literal FloatValue) :
    intRangeCheck lower upper value = true ↔ InRange lower upper value := by
  cases value with
  | int integer =>
      have bounds : intRangeCheck lower upper (.int integer : Literal FloatValue) = true ↔
          InIntRange lower upper integer := by
        cases lower <;> cases upper <;>
          simp [intRangeCheck, InIntRange]
      constructor
      · exact fun checked => .int (bounds.mp checked)
      · intro matched
        cases matched with
        | int valid => exact bounds.mpr valid
  | float | str | bool | unit =>
      constructor
      · simp [intRangeCheck]
      · intro matched; cases matched

@[simp] theorem integer_match_exact (left right : Int)
    (floatCheck : FloatValue → FloatValue → Bool) :
    matchCheck floatCheck (.int left) (.int right) = true ↔ left = right := by
  simp [matchCheck]

end Yulang.LiteralValues
