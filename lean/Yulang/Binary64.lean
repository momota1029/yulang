import Yulang.LiteralValues

/-!
# IEEE binary64 values and numeric pattern equality

The storage model is exactly one sign bit, eleven exponent bits and fifty-two
fraction bits. It does not use Lean's opaque native `Float` operations.
Finite values are interpreted as signed integer multiples of `2^-1074`;
this common scale represents every finite binary64 value exactly, including
subnormals. Infinities have a sign, and NaNs have no numeric equality value.

The structural `DecidableEq Value` distinguishes the two zeros and NaN payloads.
`eqCheck` implements the separate numeric equality required by spec §3b.1.
Decimal parsing and rounding are a separate layer; this module never invokes
a host floating-point conversion.
-/

namespace Yulang.Binary64

@[ext] structure Value where
  negative : Bool
  exponent : Fin 2048
  fraction : Fin (2 ^ 52)
  deriving DecidableEq, Repr

/-- The IEEE storage word, with the sign in bit 63. -/
def toWord (value : Value) : Fin (2 ^ 64) :=
  ⟨(if value.negative then 2 ^ 63 else 0) + value.exponent.val * 2 ^ 52 +
      value.fraction.val, by
    have he := value.exponent.isLt
    have hf := value.fraction.isLt
    split <;> omega⟩

/-- Decode all 64-bit words, retaining NaN payloads and the zero sign. -/
def ofWord (word : Fin (2 ^ 64)) : Value where
  negative := decide (2 ^ 63 ≤ word.val)
  exponent := ⟨word.val / 2 ^ 52 % 2048, Nat.mod_lt _ (by decide)⟩
  fraction := ⟨word.val % 2 ^ 52, Nat.mod_lt _ (by decide)⟩

@[simp] theorem ofWord_toWord (value : Value) : ofWord (toWord value) = value := by
  rcases value with ⟨negative, ⟨exponent, he⟩, ⟨fraction, hf⟩⟩
  cases negative <;> apply Value.ext
  all_goals simp only [ofWord, toWord, Bool.false_eq_true, ite_false, ite_true, Fin.mk.injEq]
  all_goals first | apply Fin.ext | skip
  all_goals try simp only [decide_eq_false_iff_not, decide_eq_true_eq]
  all_goals omega

@[simp] theorem toWord_ofWord (word : Fin (2 ^ 64)) : toWord (ofWord word) = word := by
  apply Fin.ext
  have hw := word.isLt
  simp only [ofWord, toWord, Fin.val_mk]
  by_cases h : 2 ^ 63 ≤ word.val
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem toWord_injective (left right : Value) : toWord left = toWord right ↔ left = right := by
  constructor
  · intro same
    have := congrArg ofWord same
    simpa using this
  · exact congrArg toWord

def IsNaN (value : Value) : Prop := value.exponent.val = 2047 ∧ value.fraction.val ≠ 0
def IsZero (value : Value) : Prop := value.exponent.val = 0 ∧ value.fraction.val = 0
def IsFinite (value : Value) : Prop := value.exponent.val < 2047

instance (value : Value) : Decidable (IsNaN value) := inferInstanceAs (Decidable (_ ∧ _))
instance (value : Value) : Decidable (IsZero value) := inferInstanceAs (Decidable (_ ∧ _))
instance (value : Value) : Decidable (IsFinite value) := inferInstanceAs (Decidable (_ < _))

def zero (negative : Bool := false) : Value := ⟨negative, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
def infinity (negative : Bool := false) : Value := ⟨negative, ⟨2047, by decide⟩, ⟨0, by decide⟩⟩
def nan (negative : Bool) (payload : Fin (2 ^ 52)) (_nonzero : payload.val ≠ 0) : Value :=
  ⟨negative, ⟨2047, by decide⟩, payload⟩

/-- Magnitude measured in units of the least positive subnormal, `2^-1074`.
Only the finite branch of `number` uses this quantity. -/
def units (value : Value) : Nat :=
  if value.exponent.val = 0 then value.fraction.val
  else (2 ^ 52 + value.fraction.val) * 2 ^ (value.exponent.val - 1)

inductive Number where
  | finite : Int → Number
  | infinite : Bool → Number
  deriving DecidableEq, Repr

/-- An exact numeric interpretation. NaN has no interpretation, so absence
must never be compared by ordinary `Option` equality. -/
def number (value : Value) : Option Number :=
  if value.exponent.val = 2047 then
    if value.fraction.val = 0 then some (.infinite value.negative) else none
  else some (.finite (if value.negative then -(units value : Int) else units value))

/-- Numeric equality is a shared interpreted number, not storage equality. -/
def Equal (left right : Value) : Prop :=
  ∃ value, number left = some value ∧ number right = some value

def eqCheck (left right : Value) : Bool :=
  match number left, number right with
  | some a, some b => decide (a = b)
  | _, _ => false

theorem eqCheck_exact (left right : Value) : eqCheck left right = true ↔ Equal left right := by
  unfold eqCheck Equal
  cases number left <;> cases number right <;> simp [eq_comm]

theorem number_none_iff (value : Value) : number value = none ↔ IsNaN value := by
  unfold number IsNaN
  split <;> simp_all

theorem nan_never_matches_left (left right : Value) (nan : IsNaN left) :
    eqCheck left right = false := by
  simp [eqCheck, (number_none_iff _).mpr nan]

theorem nan_never_matches_right (left right : Value) (nan : IsNaN right) :
    eqCheck left right = false := by
  simp only [eqCheck, (number_none_iff _).mpr nan]
  cases number left <;> rfl

theorem reflexive_iff_not_nan (value : Value) : eqCheck value value = true ↔ ¬ IsNaN value := by
  rw [← number_none_iff]
  unfold eqCheck
  cases number value <;> simp

@[simp] theorem number_zero (negative : Bool) : number (zero negative) = some (.finite 0) := by
  cases negative <;> rfl

@[simp] theorem number_infinity (negative : Bool) :
    number (infinity negative) = some (.infinite negative) := by
  simp only [number, infinity, Fin.val_mk, ite_true]

theorem signed_zeros_match (leftSign rightSign : Bool) :
    eqCheck (zero leftSign) (zero rightSign) = true := by
  simp [eqCheck]

theorem signed_zeros_distinct : zero false ≠ zero true := by
  intro same
  have := congrArg Value.negative same
  cases this

theorem infinity_matches_iff (leftSign rightSign : Bool) :
    eqCheck (infinity leftSign) (infinity rightSign) = true ↔ leftSign = rightSign := by
  simp [eqCheck]

theorem nan_not_reflexive (negative : Bool) (payload : Fin (2 ^ 52))
    (nonzero : payload.val ≠ 0) :
    eqCheck (nan negative payload nonzero) (nan negative payload nonzero) = false := by
  apply nan_never_matches_left
  exact ⟨rfl, nonzero⟩

theorem eqCheck_symmetric (left right : Value) : eqCheck left right = eqCheck right left := by
  unfold eqCheck
  cases number left <;> cases number right <;> simp [eq_comm]

/-- Every finite bit pattern has the stipulated exact signed dyadic value. -/
theorem finite_number (value : Value) (finite : IsFinite value) :
    number value = some (.finite (if value.negative then -(units value : Int) else units value)) := by
  have different : value.exponent.val ≠ 2047 := by unfold IsFinite at finite; omega
  simp [number, different]

theorem subnormal_units (value : Value) (subnormal : value.exponent.val = 0) :
    units value = value.fraction.val := by simp [units, subnormal]

theorem normal_units (value : Value) (normal : value.exponent.val ≠ 0) :
    units value = (2 ^ 52 + value.fraction.val) * 2 ^ (value.exponent.val - 1) := by
  simp [units, normal]

end Yulang.Binary64

namespace Yulang.LiteralValues

abbrev Binary64Literal := Literal Binary64.Value

/-- The concrete comparator for the answered float policy. The original
parameterized comparison theorem remains available unchanged. -/
def binary64MatchCheck : Binary64Literal → Binary64Literal → Bool := matchCheck Binary64.eqCheck

theorem binary64MatchCheck_exact (left right : Binary64Literal) :
    binary64MatchCheck left right = true ↔ Matches Binary64.Equal left right :=
  matchCheck_exact Binary64.eqCheck Binary64.Equal Binary64.eqCheck_exact left right

theorem binary64_signed_zero_pattern (leftSign rightSign : Bool) :
    binary64MatchCheck (.float (Binary64.zero leftSign)) (.float (Binary64.zero rightSign)) = true :=
  Binary64.signed_zeros_match leftSign rightSign

theorem binary64_nan_pattern_rejected (expected actual : Binary64.Value)
    (nan : Binary64.IsNaN actual) :
    binary64MatchCheck (.float expected) (.float actual) = false :=
  Binary64.nan_never_matches_right expected actual nan

end Yulang.LiteralValues
