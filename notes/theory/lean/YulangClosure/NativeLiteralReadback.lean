import YulangClosure.CallLiteralResponse

/-! Candidate faithful primitive observation. This does not claim that Lean
executes Rust or that kind acceptance validates decimal text. -/
namespace YulangClosure.NativeLiteral

open Original

/-- ASCII only; no Unicode digit classification or machine-integer bound. -/
def AsciiDigit (c : UInt8) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57
instance (c : UInt8) : Decidable (AsciiDigit c) := inferInstanceAs
  (Decidable (48 ≤ c.toNat ∧ c.toNat ≤ 57))

def Digits : List UInt8 → Prop
  | [] => True
  | c :: cs => AsciiDigit c ∧ Digits cs
instance digitsDecidable : (cs : List UInt8) → Decidable (Digits cs)
  | [] => isTrue True.intro
  | c :: cs =>
      letI := digitsDecidable cs
      inferInstanceAs (Decidable (AsciiDigit c ∧ Digits cs))

/-- Strip exactly one optional ASCII minus. -/
def splitSign : List UInt8 → Bool × List UInt8
  | [] => (false, [])
  | c :: cs => if c = (45 : UInt8) then (true, cs) else (false, c :: cs)

def Grammar (text : String) : Prop :=
  (splitSign text.toUTF8.data.toList).2 ≠ [] ∧
    Digits (splitSign text.toUTF8.data.toList).2
instance (text : String) : Decidable (Grammar text) := inferInstanceAs
  (Decidable ((splitSign text.toUTF8.data.toList).2 ≠ [] ∧
    Digits (splitSign text.toUTF8.data.toList).2))

/-- Independent mathematical positional fold, starting with a natural prefix. -/
def decimalFold (acc : Nat) (digits : List UInt8) : Nat :=
  digits.foldl (fun n c => 10 * n + (c.toNat - 48)) acc

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

def mathematicalValue (text : String) : Int :=
  signedValue (splitSign text.toUTF8.data.toList).1
    (decimalFold 0 (splitSign text.toUTF8.data.toList).2)

/-- Checking grammar here is readback, NOT an additional native acceptance
check. The source producers separately establish Grammar before application. -/
def decodeInteger (text : String) : Option Int :=
  if Grammar text then some (mathematicalValue text) else none

theorem decodeInteger_success {text : String} (h : Grammar text) :
    decodeInteger text = some (mathematicalValue text) := by
  simp [decodeInteger, h]

theorem decodeInteger_exact {text : String} {value : Int} :
    decodeInteger text = some value ↔
      Grammar text ∧ mathematicalValue text = value := by
  by_cases h : Grammar text <;> simp [decodeInteger, h]

theorem decodeInteger_reject {text : String} :
    decodeInteger text = none ↔ ¬ Grammar text := by
  by_cases h : Grammar text <;> simp [decodeInteger, h]

theorem decodeInteger_unique {text : String} {a b : Int}
    (ha : decodeInteger text = some a) (hb : decodeInteger text = some b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

/-- This recurrence identifies the positional interpretation explicitly. -/
theorem decimalFold_cons (acc : Nat) (c : UInt8) (cs : List UInt8) :
    decimalFold acc (c :: cs) = decimalFold (10 * acc + (c.toNat - 48)) cs :=
  List.foldl_cons (a := c) (l := cs)
    (f := fun (n : Nat) (d : UInt8) => 10 * n + (d.toNat - 48)) (b := acc)

/-- Primitive native data; unsupported covers all other RuntimeValueKind cases.
Integer payload remains text. String payload is already decoded UTF-8 data. -/
inductive Datum where
  | unit
  | integer (text : String)
  | boolean (value : Bool)
  | string (text : String)
  | unsupported

inductive Role where | value | other
  deriving DecidableEq

def kindBase : Datum → Option Base
  | .unit => some .unit
  | .integer _ => some .int
  | .boolean _ => some .bool
  | .string _ => some .string
  | .unsupported => none

/-- Source non-base forms map to none. Base cases outside the four primitive
kinds also fail. sameValue is the separately supplied matches_value observation. -/
def Accepted (expected : Option Base) (role : Role) (sameValue : Prop) (d : Datum) : Prop :=
  role = .value ∧ sameValue ∧ expected ≠ none ∧ kindBase d = expected

def WellFormed : Datum → Prop
  | .integer text => Grammar text
  | _ => True

def readback : Datum → Option Literal
  | .unit => some .unit
  | .integer text => (decodeInteger text).map Literal.int
  | .boolean value => some (.bool value)
  | .string text => some (.string text)
  | .unsupported => none

theorem readback_exists {d : Datum} {b : Base}
    (hk : kindBase d = some b) (hw : WellFormed d) :
    ∃ l, readback d = some l ∧ l.base = b := by
  cases d with
  | unit => cases hk; exact ⟨.unit, rfl, rfl⟩
  | integer text =>
      cases hk
      refine ⟨.int (mathematicalValue text), ?_, rfl⟩
      simp [readback, decodeInteger_success hw]
  | boolean value => cases hk; exact ⟨.bool value, rfl, rfl⟩
  | string text => cases hk; exact ⟨.string text, rfl, rfl⟩
  | unsupported => cases hk

/-- Closed response typing is constructed from the recovered literal. -/
theorem accepted_readback {expected : Option Base} {role : Role}
    {sameValue : Prop} {d : Datum}
    (ha : Accepted expected role sameValue d) (hw : WellFormed d) :
    ∃ l, readback d = some l ∧ expected = some l.base ∧
      TypedCall.ValueTyped Original.emptyContext (TypedCall.literalResponse l) (.base l.base) := by
  obtain ⟨hr, hs, hn, hk⟩ := ha
  cases expected with
  | none => exact False.elim (hn rfl)
  | some b =>
      obtain ⟨l, hl, hb⟩ := readback_exists hk hw
      exact ⟨l, hl, congrArg some hb.symm, TypedCall.literalResponse_typed l _⟩

/-! Kernel-reduction examples; they supplement the universal statements. -/
example : decodeInteger "-73" = some (-73) := by decide
example : decodeInteger "-0" = some 0 := by decide
example : decodeInteger "00042" = some 42 := by decide
example : decodeInteger "123456789012345678901234567890" =
    some 123456789012345678901234567890 := by decide
example : decodeInteger "" = none := by decide
example : decodeInteger "-" = none := by decide
example : decodeInteger "１２" = none := by decide
example : decodeInteger "+1" = none := by decide
example : decodeInteger "1x" = none := by decide
example : readback (.string "λ雪") = some (.string "λ雪") := rfl
example : kindBase (.boolean true) ≠ kindBase (.integer "1") := by decide
example : readback (.integer "11") = some (.int 11) := rfl
example : readback (.integer "23") = some (.int 23) := rfl
example : Accepted (some .int) .value True (.integer "bad") := by
  exact ⟨rfl, True.intro, by decide, rfl⟩
example : readback (.integer "bad") = none := rfl

end YulangClosure.NativeLiteral
