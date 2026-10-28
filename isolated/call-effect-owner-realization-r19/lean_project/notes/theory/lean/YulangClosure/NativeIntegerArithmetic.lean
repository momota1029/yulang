import YulangClosure.NativeIntegerComparison
import YulangClosure.CallNativeLiteralResponse

/-! Exact decimal carry/borrow arithmetic for the successful native helpers in
`runtime/machine.rs::decimal_add` and `runtime/decimal.rs::negate`.
The digit loops compute their result independently of its mathematical readback.
Allocation failure and the whole Rust-machine realization are separate. -/
namespace YulangClosure.NativeIntegerArithmetic

open NativeLiteral NativeIntegerComparison

/-- Little-endian positional interpretation, used only in the specification. -/
def little : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * little ds

def Digits10 : List Nat → Prop
  | [] => True
  | d :: ds => d < 10 ∧ Digits10 ds

/-- Native `add_magnitude`: absent high digits are zero; the final carry gets
its own iteration. The successful-input invariant bounds that carry by one. -/
def addDigits : List Nat → List Nat → Nat → List Nat
  | [], [], carry => if carry = 0 then [] else [carry]
  | a :: as, [], carry =>
      let sum := a + carry
      sum % 10 :: addDigits as [] (sum / 10)
  | [], b :: bs, carry =>
      let sum := b + carry
      sum % 10 :: addDigits [] bs (sum / 10)
  | a :: as, b :: bs, carry =>
      let sum := a + b + carry
      sum % 10 :: addDigits as bs (sum / 10)
  termination_by xs ys _ => xs.length + ys.length

theorem addDigits_value (xs ys : List Nat) (carry : Nat) :
    little (addDigits xs ys carry) = little xs + little ys + carry := by
  induction xs generalizing ys carry with
  | nil =>
      induction ys generalizing carry with
      | nil => by_cases hc : carry = 0 <;> simp [addDigits, little, hc]
      | cons b bs ih =>
          simp only [addDigits, little, ih]
          have h := Nat.mod_add_div (b + carry) 10
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          simp only [addDigits, little, ih]
          have h := Nat.mod_add_div (a + carry) 10
          omega
      | cons b bs =>
          simp only [addDigits, little, ih]
          have h := Nat.mod_add_div (a + b + carry) 10
          omega

theorem addDigits_digits {xs ys : List Nat} {carry : Nat}
    (hx : Digits10 xs) (hy : Digits10 ys) (hc : carry ≤ 1) :
    Digits10 (addDigits xs ys carry) := by
  induction xs generalizing ys carry with
  | nil =>
      induction ys generalizing carry with
      | nil =>
          by_cases he : carry = 0 <;> simp [addDigits, he, Digits10] <;> omega
      | cons b bs ih =>
          obtain ⟨hb, hbs⟩ := hy
          simp only [addDigits, Digits10]
          exact ⟨Nat.mod_lt _ (by decide), ih hbs (by omega)⟩
  | cons a as ih =>
      obtain ⟨ha, has⟩ := hx
      cases ys with
      | nil =>
          simp only [addDigits, Digits10]
          exact ⟨Nat.mod_lt _ (by decide), ih has True.intro (by omega)⟩
      | cons b bs =>
          obtain ⟨hb, hbs⟩ := hy
          simp only [addDigits, Digits10]
          exact ⟨Nat.mod_lt _ (by decide), ih has hbs (by omega)⟩

/-- Native signed i16 subtraction encoded as nonnegative digit and borrow.
Under the digit bounds the intermediate lies in [-10,9]. -/
def subtractDigit (a b borrow : Nat) : Nat × Nat :=
  if a < b + borrow then (a + 10 - (b + borrow), 1)
  else (a - (b + borrow), 0)

theorem subtractDigit_spec {a b borrow : Nat}
    (ha : a < 10) (hb : b < 10) (hc : borrow ≤ 1) :
    (subtractDigit a b borrow).1 < 10 ∧
    (subtractDigit a b borrow).2 ≤ 1 ∧
    (((subtractDigit a b borrow).1 : Int) -
      10 * ((subtractDigit a b borrow).2 : Int)) =
      (a : Int) - (b : Int) - (borrow : Int) := by
  unfold subtractDigit
  split <;> dsimp only <;> omega

/-- Native `subtract_magnitude` visits exactly the larger input's digits.
The final borrow is retained for the proof even though native code ignores it. -/
def subtractDigits : List Nat → List Nat → Nat → List Nat × Nat
  | [], _, borrow => ([], borrow)
  | a :: as, ys, borrow =>
      let digit := subtractDigit a (ys.headD 0) borrow
      let rest := subtractDigits as ys.tail digit.2
      (digit.1 :: rest.1, rest.2)

theorem subtractDigit_equation {a b borrow : Nat}
    (ha : a < 10) (hb : b < 10) (hc : borrow ≤ 1) :
    (subtractDigit a b borrow).1 + b + borrow =
      a + 10 * (subtractDigit a b borrow).2 := by
  unfold subtractDigit
  split <;> dsimp only <;> omega

theorem little_bound {ds : List Nat} (hd : Digits10 ds) :
    little ds < 10 ^ ds.length := by
  induction ds with
  | nil => simp [little]
  | cons d ds ih =>
      obtain ⟨hd, hds⟩ := hd
      have ht := ih hds
      simp only [little, List.length_cons, Nat.pow_succ]
      omega

/-- The complete borrow invariant, including every intermediate carry-in.
No mathematical subtraction is used to define the computed output. -/
theorem subtractDigits_spec {xs ys : List Nat} {borrow : Nat}
    (hx : Digits10 xs) (hy : Digits10 ys) (hc : borrow ≤ 1)
    (hlen : ys.length ≤ xs.length) :
    Digits10 (subtractDigits xs ys borrow).1 ∧
    (subtractDigits xs ys borrow).1.length = xs.length ∧
    (subtractDigits xs ys borrow).2 ≤ 1 ∧
    little (subtractDigits xs ys borrow).1 + little ys + borrow =
      little xs + 10 ^ xs.length * (subtractDigits xs ys borrow).2 := by
  induction xs generalizing ys borrow with
  | nil =>
      have he : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst ys
      simp [subtractDigits, Digits10, little, hc]
  | cons a as ih =>
      obtain ⟨ha, has⟩ := hx
      have hb : ys.headD 0 < 10 := by cases ys <;> simp_all [Digits10]
      have hys : Digits10 ys.tail := by cases ys <;> simp_all [Digits10]
      have hl : ys.tail.length ≤ as.length := by cases ys <;> simp_all
      have he : little ys = ys.headD 0 + 10 * little ys.tail := by
        cases ys <;> rfl
      have hd := subtractDigit_spec ha hb hc
      have hdEq := subtractDigit_equation ha hb hc
      obtain ⟨ht, hlength, hborrow, hEq⟩ := ih has hys hd.2.1 hl
      refine ⟨⟨hd.1, ht⟩, ?_, hborrow, ?_⟩
      · simpa only [subtractDigits, List.length_cons] using congrArg Nat.succ hlength
      · have hm := congrArg (fun n => 10 * n) hEq
        simp only [Nat.mul_add] at hm
        simp only [subtractDigits, little, List.length_cons, Nat.pow_succ]
        rw [he]
        simp only [Nat.mul_assoc, Nat.mul_comm _ 10] at hm ⊢
        omega

/-- Native magnitude comparison supplies the nonnegative difference. This
discharges the previously unchecked final-borrow fact. -/
theorem subtractDigits_value {xs ys : List Nat}
    (hx : Digits10 xs) (hy : Digits10 ys)
    (hlen : ys.length ≤ xs.length) (hge : little ys ≤ little xs) :
    (subtractDigits xs ys 0).2 = 0 ∧
    little (subtractDigits xs ys 0).1 = little xs - little ys := by
  obtain ⟨hd, hl, hb, he⟩ := subtractDigits_spec hx hy (by decide : 0 ≤ 1) hlen
  have hbound := little_bound hd
  rw [hl] at hbound
  have hz : (subtractDigits xs ys 0).2 = 0 := by
    by_cases hn : (subtractDigits xs ys 0).2 = 0
    · exact hn
    · have hone : (subtractDigits xs ys 0).2 = 1 := by omega
      rw [hone, Nat.mul_one] at he
      omega
  rw [hz, Nat.mul_zero] at he
  exact ⟨hz, by omega⟩

/-- Decimal bytes enter the native loops from the low end. -/
def lowDigits (bytes : List UInt8) : List Nat :=
  bytes.reverse.map (fun b => b.toNat - 48)

/-- Native output bytes after the loop's final reversal. -/
def magnitudeBytes (digits : List Nat) : List UInt8 :=
  (digits.map (fun d => UInt8.ofNat (48 + d))).reverse

theorem little_append (xs ys : List Nat) :
    little (xs ++ ys) = little xs + 10 ^ xs.length * little ys := by
  induction xs with
  | nil => simp [little]
  | cons a as ih =>
      simp only [List.cons_append, little, List.length_cons, Nat.pow_succ, ih]
      simp [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm]

theorem lowDigits_value (bytes : List UInt8) :
    little (lowDigits bytes) = value bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
      simp only [lowDigits, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        little_append, little, List.length_map, List.length_reverse, Nat.mul_zero, Nat.add_zero]
      change little (lowDigits bs) + 10 ^ bs.length * (b.toNat - 48) = _
      rw [ih]
      simp [value, Nat.mul_comm, Nat.add_comm]

theorem digits10_append {xs ys : List Nat} (hx : Digits10 xs) (hy : Digits10 ys) :
    Digits10 (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons a as ih => exact ⟨hx.1, ih hx.2⟩

theorem lowDigits_digits {bytes : List UInt8} (hd : Digits bytes) :
    Digits10 (lowDigits bytes) := by
  induction bytes with
  | nil => trivial
  | cons b bs ih =>
      obtain ⟨⟨hb0, hb9⟩, hbs⟩ := hd
      simp only [lowDigits, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      exact digits10_append (ih hbs) ⟨by omega, True.intro⟩

theorem byteDigit_spec {d : Nat} (hd : d < 10) :
    (UInt8.ofNat (48 + d)).toNat = 48 + d ∧
    AsciiDigit (UInt8.ofNat (48 + d)) := by
  have hlt : 48 + d < 256 := by omega
  have he : (UInt8.ofNat (48 + d)).toNat = 48 + d := by
    simpa using Nat.mod_eq_of_lt hlt
  exact ⟨he, by unfold AsciiDigit; rw [he]; omega⟩

theorem digits_append {xs ys : List UInt8} (hx : Digits xs) (hy : Digits ys) :
    Digits (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons a as ih => exact ⟨hx.1, ih hx.2⟩

theorem magnitudeBytes_digits {ds : List Nat} (hd : Digits10 ds) :
    Digits (magnitudeBytes ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih =>
      obtain ⟨hd, hds⟩ := hd
      simp only [magnitudeBytes, List.map_cons, List.reverse_cons]
      exact digits_append (ih hds) ⟨(byteDigit_spec hd).2, True.intro⟩

theorem lowDigits_magnitudeBytes {ds : List Nat} (hd : Digits10 ds) :
    lowDigits (magnitudeBytes ds) = ds := by
  simp only [lowDigits, magnitudeBytes, List.reverse_reverse, List.map_map]
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, Function.comp_def]
      rw [(byteDigit_spec hd.1).1, Nat.add_sub_cancel_left]
      exact congrArg (List.cons d) (by simpa only [Function.comp_def] using ih hd.2)

theorem magnitudeBytes_value {ds : List Nat} (hd : Digits10 ds) :
    value (magnitudeBytes ds) = little ds := by
  rw [← lowDigits_value, lowDigits_magnitudeBytes hd]

def ByteGrammar (bytes : List UInt8) : Prop :=
  (splitSign bytes).2 ≠ [] ∧ Digits (splitSign bytes).2

instance (bytes : List UInt8) : Decidable (ByteGrammar bytes) := inferInstanceAs
  (Decidable ((splitSign bytes).2 ≠ [] ∧ Digits (splitSign bytes).2))

def decodeBytes (bytes : List UInt8) : Option Int :=
  if ByteGrammar bytes then
    some (signedValue (splitSign bytes).1 (decimalFold 0 (splitSign bytes).2))
  else none

theorem decodeBytes_string (text : String) :
    decodeBytes text.toUTF8.data.toList = decodeInteger text := rfl

theorem splitSign_digits {ds : List UInt8} (hd : Digits ds) :
    splitSign ds = (false, ds) := by
  cases ds with
  | nil => rfl
  | cons d ds =>
      have hne : d ≠ (45 : UInt8) := by
        intro he
        have hd0 := hd.1.1
        rw [he] at hd0
        contradiction
      simp [splitSign, hne]

/-- Native `signed` inserts a minus unless the magnitude is exactly "0". -/
def signedBytes (negative : Bool) (ds : List UInt8) : List UInt8 :=
  if negative = false ∨ ds = [48] then ds else 45 :: ds

theorem signedBytes_decode {ds : List UInt8} (negative : Bool)
    (hd : Digits ds) (hn : ds ≠ []) :
    decodeBytes (signedBytes negative ds) = some (signedValue negative (value ds)) := by
  cases negative with
  | false =>
      simp [signedBytes, decodeBytes, ByteGrammar, splitSign_digits hd, hn, hd,
        signedValue, fold_zero]
  | true =>
      by_cases hz : ds = [48]
      · subst ds
        simp [signedBytes, decodeBytes, ByteGrammar, splitSign, Digits, AsciiDigit,
          decimalFold, value, signedValue]
      · simp [signedBytes, hz, decodeBytes, ByteGrammar, splitSign, hn, hd, fold_zero]

/-- Unlike decimal.rs::parts, decimal_add::split retains the sign of zero. -/
def splitAddBytes (bytes : List UInt8) : Option (Bool × List UInt8) :=
  let p := splitSign bytes
  if p.2 ≠ [] ∧ Digits p.2 then
    some (p.1, (normalize false p.2).2)
  else none

theorem canonical_nonempty {ds : List UInt8} (hc : Canonical ds) : ds ≠ [] := by
  rcases hc with rfl | ⟨d, ds, rfl, _⟩ <;> simp

theorem normalize_false_sign (ds : List UInt8) : (normalize false ds).1 = false := by
  unfold normalize
  split <;> rfl

theorem normalize_false_value {ds : List UInt8} (hd : Digits ds) :
    value (normalize false ds).2 = value ds := by
  have he := (normalize_spec false hd).2.2.1
  have hi : (value (normalize false ds).2 : Int) = (value ds : Int) := by
    simpa [normalize_false_sign, signedValue] using he
  omega

theorem splitAddBytes_spec {bytes : List UInt8} {p : Bool × List UInt8}
    (hp : splitAddBytes bytes = some p) :
    ByteGrammar bytes ∧ Digits p.2 ∧ Canonical p.2 ∧
      signedValue p.1 (value p.2) =
        signedValue (splitSign bytes).1 (decimalFold 0 (splitSign bytes).2) := by
  unfold splitAddBytes at hp
  dsimp only at hp
  split at hp
  next hg =>
    have he := Option.some.inj hp
    rw [← he]
    obtain ⟨hd, hc, _, _⟩ := normalize_spec false hg.2
    have hv' : value (normalize false (splitSign bytes).2).2 =
        value (splitSign bytes).2 := by
      exact normalize_false_value hg.2
    exact ⟨hg, hd, hc, by rw [hv', fold_zero]⟩
  next hg => cases hp

theorem splitAddBytes_exists {bytes : List UInt8} (hg : ByteGrammar bytes) :
    ∃ p, splitAddBytes bytes = some p := by
  exact ⟨((splitSign bytes).1, (normalize false (splitSign bytes).2).2),
    by unfold splitAddBytes; dsimp only; exact ite_eq_left hg⟩

def addMagnitude (left right : List UInt8) : List UInt8 :=
  magnitudeBytes (addDigits (lowDigits left) (lowDigits right) 0)

theorem addDigits_nonempty {xs ys : List Nat} (hx : xs ≠ []) (carry : Nat) :
    addDigits xs ys carry ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons x xs => cases ys <;> simp [addDigits]

theorem lowDigits_nonempty {ds : List UInt8} (hn : ds ≠ []) : lowDigits ds ≠ [] := by
  simpa [lowDigits] using hn

theorem magnitudeBytes_nonempty {ds : List Nat} (hn : ds ≠ []) :
    magnitudeBytes ds ≠ [] := by simpa [magnitudeBytes] using hn

theorem addMagnitude_spec {left right : List UInt8}
    (hl : Digits left) (hr : Digits right) (hn : left ≠ []) :
    Digits (addMagnitude left right) ∧ addMagnitude left right ≠ [] ∧
      value (addMagnitude left right) = value left + value right := by
  have hd := addDigits_digits (lowDigits_digits hl) (lowDigits_digits hr) (by decide : 0 ≤ 1)
  exact ⟨magnitudeBytes_digits hd,
    magnitudeBytes_nonempty (addDigits_nonempty (lowDigits_nonempty hn) 0),
    by rw [addMagnitude, magnitudeBytes_value hd, addDigits_value,
      lowDigits_value, lowDigits_value, Nat.add_zero]⟩

/-- Removing high zeros while retaining one digit, expressed after reversal.
This is the byte-level value returned by native `subtract_magnitude`. -/
def subtractMagnitude (left right : List UInt8) : List UInt8 :=
  (normalize false (magnitudeBytes (subtractDigits (lowDigits left) (lowDigits right) 0).1)).2

theorem subtractMagnitude_spec {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (hlen : right.length ≤ left.length) (hge : value right ≤ value left) :
    Digits (subtractMagnitude left right) ∧ Canonical (subtractMagnitude left right) ∧
      value (subtractMagnitude left right) = value left - value right := by
  have hx := lowDigits_digits hl
  have hy := lowDigits_digits hr
  have hlen' : (lowDigits right).length ≤ (lowDigits left).length := by
    simpa [lowDigits] using hlen
  have hge' : little (lowDigits right) ≤ little (lowDigits left) := by
    simpa [lowDigits_value] using hge
  have hd := (subtractDigits_spec hx hy (by decide : 0 ≤ 1) hlen').1
  have hv := (subtractDigits_value hx hy hlen' hge').2
  obtain ⟨ho, hc, _, _⟩ := normalize_spec false (magnitudeBytes_digits hd)
  have he' : value (subtractMagnitude left right) =
      value (magnitudeBytes (subtractDigits (lowDigits left) (lowDigits right) 0).1) := by
    exact normalize_false_value (magnitudeBytes_digits hd)
  exact ⟨ho, hc, by rw [he', magnitudeBytes_value hd, hv, lowDigits_value, lowDigits_value]⟩

def addParsed (left right : Bool × List UInt8) : List UInt8 :=
  if left.1 = right.1 then signedBytes left.1 (addMagnitude left.2 right.2)
  else match magnitude left.2 right.2 with
    | .eq => [48]
    | .gt => signedBytes left.1 (subtractMagnitude left.2 right.2)
    | .lt => signedBytes right.1 (subtractMagnitude right.2 left.2)

def decimalAddBytes (left right : List UInt8) : Option (List UInt8) := do
  let l ← splitAddBytes left
  let r ← splitAddBytes right
  pure (addParsed l r)

theorem signedValue_add (negative : Bool) (a b : Nat) :
    signedValue negative (a + b) = signedValue negative a + signedValue negative b := by
  cases negative <;> simp [signedValue, Int.ofNat_eq_natCast, Int.neg_add]

theorem signedValue_difference (negative : Bool) {a b : Nat} (h : b ≤ a) :
    signedValue negative (a - b) = signedValue negative a + signedValue (!negative) b := by
  cases negative <;> simp only [signedValue, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast] <;> omega

theorem magnitude_gt_length {left right : List UInt8}
    (h : magnitude left right = .gt) : right.length ≤ left.length := by
  by_cases hl : left.length < right.length
  · simp [magnitude, hl] at h
  · omega

theorem magnitude_lt_length {left right : List UInt8}
    (h : magnitude left right = .lt) : left.length ≤ right.length := by
  by_cases hl : left.length < right.length
  · omega
  · by_cases hr : right.length < left.length
    · simp [magnitude, hl, hr] at h
    · omega

theorem addParsed_decode {left right : Bool × List UInt8}
    (hl : Digits left.2) (hr : Digits right.2)
    (cl : Canonical left.2) (cr : Canonical right.2) :
    decodeBytes (addParsed left right) =
      some (signedValue left.1 (value left.2) + signedValue right.1 (value right.2)) := by
  have hm := magnitude_value hl hr cl cr
  by_cases hs : left.1 = right.1
  · obtain ⟨hd, hn, hv⟩ := addMagnitude_spec hl hr (canonical_nonempty cl)
    simp only [addParsed, ite_eq_left hs]
    rw [signedBytes_decode _ hd hn, hv, signedValue_add, hs]
  · have hop : right.1 = !left.1 := by
      cases hl : left.1 <;> cases hr : right.1 <;> simp_all
    have hop' : left.1 = !right.1 := by rw [hop, Bool.not_not]
    simp only [addParsed, ite_eq_right hs]
    cases hc : magnitude left.2 right.2 with
    | eq =>
        have hv : value left.2 = value right.2 :=
          Nat.compare_eq_eq.mp (hc ▸ hm.symm)
        have hz : signedValue left.1 (value left.2) + signedValue right.1 (value right.2) = 0 := by
          rw [hv, hop]
          cases left.1 <;> simp only [signedValue, Bool.not_false, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast] <;> omega
        rw [hz]
        rfl
    | gt =>
        have hge : value right.2 ≤ value left.2 :=
          Nat.le_of_lt (Nat.compare_eq_gt.mp (hc ▸ hm.symm))
        obtain ⟨hd, hcanon, hv⟩ := subtractMagnitude_spec hl hr (magnitude_gt_length hc) hge
        rw [signedBytes_decode _ hd (canonical_nonempty hcanon), hv,
          signedValue_difference _ hge, ← hop]
    | lt =>
        have hge : value left.2 ≤ value right.2 :=
          Nat.le_of_lt (Nat.compare_eq_lt.mp (hc ▸ hm.symm))
        obtain ⟨hd, hcanon, hv⟩ := subtractMagnitude_spec hr hl (magnitude_lt_length hc) hge
        rw [signedBytes_decode _ hd (canonical_nonempty hcanon), hv,
          signedValue_difference _ hge, ← hop', Int.add_comm]

/-- All source signed branches, including leading zeros and negative zero. -/
theorem decimalAddBytes_decode {left right : List UInt8} {a b : Int}
    (ha : decodeBytes left = some a) (hb : decodeBytes right = some b) :
    ∃ output, decimalAddBytes left right = some output ∧
      decodeBytes output = some (a + b) := by
  have hga : ByteGrammar left := by
    unfold decodeBytes at ha
    split at ha
    next h => exact h
    next h => cases ha
  have hgb : ByteGrammar right := by
    unfold decodeBytes at hb
    split at hb
    next h => exact h
    next h => cases hb
  obtain ⟨l, hl⟩ := splitAddBytes_exists hga
  obtain ⟨r, hr⟩ := splitAddBytes_exists hgb
  obtain ⟨_, hld, hlc, hlv⟩ := splitAddBytes_spec hl
  obtain ⟨_, hrd, hrc, hrv⟩ := splitAddBytes_spec hr
  have hav : signedValue l.1 (value l.2) = a := by
    rw [hlv]
    exact Option.some.inj (by simpa only [decodeBytes, ite_eq_left hga] using ha)
  have hbv : signedValue r.1 (value r.2) = b := by
    rw [hrv]
    exact Option.some.inj (by simpa only [decodeBytes, ite_eq_left hgb] using hb)
  exact ⟨addParsed l r, by simp [decimalAddBytes, hl, hr],
    by simpa [hav, hbv] using addParsed_decode hld hrd hlc hrc⟩

theorem decodeBytes_exact {bytes : List UInt8} {a : Int} :
    decodeBytes bytes = some a ↔ ByteGrammar bytes ∧
      signedValue (splitSign bytes).1 (decimalFold 0 (splitSign bytes).2) = a := by
  by_cases hg : ByteGrammar bytes <;> simp [decodeBytes, hg]

theorem parseBytes_spec {bytes : List UInt8} {p : Bool × List UInt8}
    (hp : parseBytes bytes = some p) :
    ByteGrammar bytes ∧ Digits p.2 ∧ Canonical p.2 ∧
      signedValue p.1 (value p.2) =
        signedValue (splitSign bytes).1 (decimalFold 0 (splitSign bytes).2) := by
  unfold parseBytes at hp
  dsimp only at hp
  split at hp
  next hg =>
    have he := Option.some.inj hp
    rw [← he]
    obtain ⟨hd, hc, hv, _⟩ := normalize_spec (splitSign bytes).1 hg.2
    exact ⟨hg, hd, hc, by simpa only [fold_zero] using hv⟩
  next hg => cases hp

/-- Native negate uses the decimal.rs parser, which normalizes negative zero. -/
def negateBytes (bytes : List UInt8) : Option (List UInt8) := do
  let p ← parseBytes bytes
  pure (signedBytes (!p.1) p.2)

theorem signedValue_negate (negative : Bool) (a : Nat) :
    signedValue (!negative) a = -signedValue negative a := by
  cases negative <;> simp [signedValue, Int.neg_neg]

theorem negateBytes_decode {bytes : List UInt8} {a : Int}
    (ha : decodeBytes bytes = some a) :
    ∃ output, negateBytes bytes = some output ∧ decodeBytes output = some (-a) := by
  obtain ⟨hg, hv⟩ := decodeBytes_exact.mp ha
  obtain ⟨p, hp⟩ := (parseBytes_success_iff bytes).mpr hg
  obtain ⟨_, hd, hc, he⟩ := parseBytes_spec hp
  refine ⟨signedBytes (!p.1) p.2, by simp [negateBytes, hp], ?_⟩
  rw [signedBytes_decode _ hd (canonical_nonempty hc), signedValue_negate, he, hv]

/-- Native IntSub calls negate on the right, then the same addition helper. -/
def decimalSubtractBytes (left right : List UInt8) : Option (List UInt8) := do
  let negative ← negateBytes right
  decimalAddBytes left negative

theorem decimalSubtractBytes_decode {left right : List UInt8} {a b : Int}
    (ha : decodeBytes left = some a) (hb : decodeBytes right = some b) :
    ∃ output, decimalSubtractBytes left right = some output ∧
      decodeBytes output = some (a - b) := by
  obtain ⟨negative, hn, hv⟩ := negateBytes_decode hb
  obtain ⟨output, ho, hvo⟩ := decimalAddBytes_decode ha hv
  exact ⟨output, by simp [decimalSubtractBytes, hn, ho],
    by simpa only [Int.sub_eq_add_neg] using hvo⟩

/-- Conversion is only from already computed bytes, never from a decoded Int. -/
def asciiString (bytes : List UInt8) : String :=
  String.ofList (bytes.map (fun b => Char.ofNat b.toNat))

theorem asciiChar_bytes (b : UInt8) (hb : b.toNat < 128) :
    String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
  have hv : b.toNat.isValidChar := Or.inl (by omega)
  have h127 : b.toNat ≤ 127 := by omega
  simp only [Char.ofNat, dite_eq_left hv, String.utf8EncodeChar, Char.ofNatAux]
  change (if b.toNat ≤ 127 then [UInt8.ofNat b.toNat] else _) = [b]
  simp [h127]

theorem asciiString_bytes {bytes : List UInt8}
    (h : ∀ b, b ∈ bytes → b.toNat < 128) :
    (asciiString bytes).toUTF8.data.toList = bytes := by
  simp only [asciiString, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode, List.toList_data_toByteArray]
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [asciiChar_bytes b (h b (by simp)), ih (fun c hc => h c (by simp [hc]))]
      rfl

theorem digits_ascii {bytes : List UInt8} (hd : Digits bytes) :
    ∀ b, b ∈ bytes → b.toNat < 128 := by
  induction bytes with
  | nil => simp
  | cons b bs ih =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · have hb := hd.1.2; omega
      · exact ih hd.2 c hc

theorem byteGrammar_ascii {bytes : List UInt8} (hg : ByteGrammar bytes) :
    ∀ b, b ∈ bytes → b.toNat < 128 := by
  cases bytes with
  | nil => simp
  | cons b bs =>
      by_cases hb : b = (45 : UInt8)
      · subst b
        have hd : Digits bs := hg.2
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · exact digits_ascii hd c hc
      · have hd : Digits (b :: bs) := by simpa [ByteGrammar, splitSign, hb] using hg.2
        exact digits_ascii hd

theorem asciiString_decode {bytes : List UInt8} {a : Int}
    (h : decodeBytes bytes = some a) :
    decodeInteger (asciiString bytes) = some a := by
  rw [← decodeBytes_string, asciiString_bytes (byteGrammar_ascii (decodeBytes_exact.mp h).1)]
  exact h

theorem negateBytes_grammar {bytes output : List UInt8}
    (hout : negateBytes bytes = some output) : ByteGrammar output := by
  cases hp : parseBytes bytes with
  | none => simp [negateBytes, hp] at hout
  | some p =>
      have he : signedBytes (!p.1) p.2 = output := by
        simpa [negateBytes, hp] using hout
      obtain ⟨_, hd, hc, _⟩ := parseBytes_spec hp
      rw [← he]
      exact (decodeBytes_exact.mp (signedBytes_decode (!p.1) hd (canonical_nonempty hc))).1

def decimalAdd (left right : String) : Option String :=
  (decimalAddBytes left.toUTF8.data.toList right.toUTF8.data.toList).map asciiString

def negate (text : String) : Option String :=
  (negateBytes text.toUTF8.data.toList).map asciiString

def decimalSubtract (left right : String) : Option String :=
  (decimalSubtractBytes left.toUTF8.data.toList right.toUTF8.data.toList).map asciiString

/-- The byte composition is exactly the native String-level negate-then-add
path, including malformed-input rejection. No intermediate text is redefined. -/
theorem decimalSubtract_eq_negate_add (left right : String) :
    decimalSubtract left right = (do
      let negative ← negate right
      decimalAdd left negative) := by
  cases hn : negateBytes right.toUTF8.data.toList with
  | none =>
      simp only [decimalSubtract, decimalSubtractBytes, negate, hn,
        Option.map_none]
      rfl
  | some bytes =>
      have hround := asciiString_bytes (byteGrammar_ascii (negateBytes_grammar hn))
      simp only [decimalSubtract, decimalSubtractBytes, negate, hn,
        Option.map_some, decimalAdd]
      change (decimalAddBytes left.toUTF8.data.toList bytes).map asciiString =
        (decimalAddBytes left.toUTF8.data.toList
          (asciiString bytes).toUTF8.data.toList).map asciiString
      rw [hround]

/-- Native arbitrary-precision addition computes the mathematical sum. -/
theorem decimalAdd_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    ∃ output, decimalAdd left right = some output ∧ decodeInteger output = some (a + b) := by
  obtain ⟨bytes, ho, hv⟩ := decimalAddBytes_decode ha hb
  exact ⟨asciiString bytes, by simp only [decimalAdd, ho, Option.map_some], asciiString_decode hv⟩

theorem negate_decode {text : String} {a : Int}
    (ha : decodeInteger text = some a) :
    ∃ output, negate text = some output ∧ decodeInteger output = some (-a) := by
  obtain ⟨bytes, ho, hv⟩ := negateBytes_decode ha
  exact ⟨asciiString bytes, by simp only [negate, ho, Option.map_some], asciiString_decode hv⟩

/-- Native subtraction composes its actual negate/add helper path. -/
theorem decimalSubtract_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    ∃ output, decimalSubtract left right = some output ∧ decodeInteger output = some (a - b) := by
  obtain ⟨bytes, ho, hv⟩ := decimalSubtractBytes_decode ha hb
  exact ⟨asciiString bytes, by simp only [decimalSubtract, ho, Option.map_some], asciiString_decode hv⟩

theorem decimalAdd_result {left right output : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b)
    (ho : decimalAdd left right = some output) :
    decodeInteger output = some (a + b) := by
  obtain ⟨result, hr, hv⟩ := decimalAdd_decode ha hb
  have he := Option.some.inj (ho.symm.trans hr)
  exact he ▸ hv

theorem decimalSubtract_result {left right output : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b)
    (ho : decimalSubtract left right = some output) :
    decodeInteger output = some (a - b) := by
  obtain ⟨result, hr, hv⟩ := decimalSubtract_decode ha hb
  have he := Option.some.inj (ho.symm.trans hr)
  exact he ▸ hv

/-- Apply exact arithmetic to the existing native-literal response consumer;
output well-formedness is a consequence and is not a hypothesis. -/
theorem decimalAdd_response {left right output : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b)
    (ho : decimalAdd left right = some output) :
    NativeLiteral.readback (.integer output) = some (.int (a + b)) ∧
    TypedCall.ValueTyped Original.emptyContext
      (TypedCall.literalResponse (.int (a + b))) (.base .int) := by
  exact ⟨by simp only [NativeLiteral.readback, decimalAdd_result ha hb ho, Option.map_some],
    TypedCall.literalResponse_typed _ _⟩

theorem decimalSubtract_response {left right output : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b)
    (ho : decimalSubtract left right = some output) :
    NativeLiteral.readback (.integer output) = some (.int (a - b)) ∧
    TypedCall.ValueTyped Original.emptyContext
      (TypedCall.literalResponse (.int (a - b))) (.base .int) := by
  exact ⟨by simp only [NativeLiteral.readback, decimalSubtract_result ha hb ho, Option.map_some],
    TypedCall.literalResponse_typed _ _⟩

/-- Every real carry step fits in native u8 before quotient/remainder. -/
theorem carry_step_bounds {a b carry : Nat}
    (ha : a < 10) (hb : b < 10) (hc : carry ≤ 1) :
    a + b + carry ≤ 19 ∧ (a + b + carry) % 10 < 10 ∧
      (a + b + carry) / 10 ≤ 1 := by omega

/-- The final carry-only branch is the native loop's last quotient/remainder
iteration, with no further carry. -/
theorem final_carry_iteration {carry : Nat} (hc : carry ≤ 1) :
    carry % 10 = carry ∧ carry / 10 = 0 ∧
    addDigits [] [] carry = (if carry = 0 then [] else [carry % 10]) := by
  have hm : carry % 10 = carry := Nat.mod_eq_of_lt (by omega)
  exact ⟨hm, by omega, by simp only [addDigits, hm]⟩

/-- Every signed native subtraction intermediate fits in i16. -/
theorem borrow_step_bounds {a b borrow : Nat}
    (ha : a < 10) (hb : b < 10) (hc : borrow ≤ 1) :
    -10 ≤ (a : Int) - borrow - b ∧ (a : Int) - borrow - b ≤ 9 := by omega

theorem addDigits_length (xs ys : List Nat) (carry : Nat) :
    (addDigits xs ys carry).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys carry with
  | nil =>
      induction ys generalizing carry with
      | nil => by_cases hc : carry = 0 <;> simp [addDigits, hc]
      | cons b bs ih =>
          simp only [addDigits, List.length_cons]
          have h := ih ((b + carry) / 10)
          simp only [List.length_nil, Nat.zero_max] at h ⊢
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          simp only [addDigits, List.length_cons]
          have h := ih [] ((a + carry) / 10)
          simp only [List.length_nil, Nat.max_zero] at h ⊢
          omega
      | cons b bs =>
          simp only [addDigits, List.length_cons]
          have h := ih bs ((a + b + carry) / 10)
          omega

/-- The native subtraction trim, viewed after the final reversal. -/
def trimLeadingKeepOne : List UInt8 → List UInt8
  | [] => []
  | [d] => [d]
  | d :: e :: rest =>
      if d.toNat = 48 then trimLeadingKeepOne (e :: rest) else d :: e :: rest

theorem trimLeadingKeepOne_normalize {ds : List UInt8} (hn : ds ≠ []) :
    trimLeadingKeepOne ds = (normalize false ds).2 := by
  induction ds with
  | nil => contradiction
  | cons d ds ih =>
      cases ds with
      | nil =>
          by_cases hd : d.toNat = 48
          · have he : d = (48 : UInt8) := UInt8.toNat_inj.mp hd
            subst d
            rfl
          · simp [trimLeadingKeepOne, normalize, trimZeros, hd]
      | cons e rest =>
          by_cases hd : d.toNat = 48
          · simpa only [trimLeadingKeepOne, hd, ↓reduceIte, normalize, trimZeros] using
              ih (by simp)
          · simp [trimLeadingKeepOne, normalize, trimZeros, hd]

theorem subtractMagnitude_nativeTrim {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (hlen : right.length ≤ left.length) (hn : left ≠ []) :
    subtractMagnitude left right =
      trimLeadingKeepOne (magnitudeBytes
        (subtractDigits (lowDigits left) (lowDigits right) 0).1) := by
  have hlength := (subtractDigits_spec (lowDigits_digits hl) (lowDigits_digits hr)
    (by decide : 0 ≤ 1) (by simpa [lowDigits] using hlen)).2.1
  have hn' : (subtractDigits (lowDigits left) (lowDigits right) 0).1 ≠ [] := by
    intro he
    have hzero : (lowDigits left).length = 0 := by simpa [he] using hlength.symm
    exact lowDigits_nonempty hn (List.eq_nil_of_length_eq_zero hzero)
  exact (trimLeadingKeepOne_normalize (magnitudeBytes_nonempty hn')).symm

/-! Distinguishing kernel computations; universal proofs above cover all widths. -/
example : decimalAdd "999999999999999999999999999999" "1" =
    some "1000000000000000000000000000000" := by decide +kernel
example : decimalAdd "-000" "000" = some "0" := by decide +kernel
example : decimalAdd "-0012" "0005" = some "-7" := by decide +kernel
example : decimalAdd "5" "-12" = some "-7" := by decide +kernel
example : decimalAdd "12" "-5" = some "7" := by decide +kernel
example : decimalAdd "-5" "12" = some "7" := by decide +kernel
example : decimalAdd "-12" "-5" = some "-17" := by decide +kernel
example : decimalSubtract "1000000000000000000000000" "1" =
    some "999999999999999999999999" := by decide +kernel
example : decimalSubtract "-12" "-5" = some "-7" := by decide +kernel
example : decimalSubtract "5" "-12" = some "17" := by decide +kernel
example : negate "-0000" = some "0" := by decide +kernel
example : decimalAdd "+1" "2" = none := by decide +kernel
example : decimalAdd "１" "2" = none := by decide +kernel

end YulangClosure.NativeIntegerArithmetic

namespace YulangClosure.Control

/-- Apply computed native addition to the original completed actual-request
theorem. Its producer/WellFormed premise is discharged by the arithmetic proof;
the operation instance, actual prefix, current world and full suffix are kept. -/
theorem actual_call_request_completed_add_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n m : Nat} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hpost : YulangClosure.Prefix (CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    {left right output : String} {a b : Int}
    (ha : NativeLiteral.decodeInteger left = some a)
    (hb : NativeLiteral.decodeInteger right = some b)
    (hout : NativeIntegerArithmetic.decimalAdd left right = some output)
    {role : NativeLiteral.Role} {sameValue : Prop}
    (haccept : NativeLiteral.Accepted (some .int) role sameValue (.integer output))
    (hinstance : op.responseType = .base .int) :
    NativeLiteral.readback (.integer output) = some (.int (a + b)) ∧
    TypedCall.ValueTyped Original.emptyContext
      (TypedCall.literalResponse (.int (a + b))) op.responseType ∧
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k)
        (TypedCall.literalResponse (.int (a + b)))) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames
        (plugResponse k (TypedCall.literalResponse (.int (a + b))))) term.resultType := by
  have hvalue := NativeIntegerArithmetic.decimalAdd_result ha hb hout
  have hproducer : NativeLiteral.WellFormed (.integer output) :=
    (NativeLiteral.decodeInteger_exact.mp hvalue).1
  obtain ⟨l, hl, _, rest⟩ := actual_call_request_completed_native_literal_response
    hsuffix hp hhead hpost hcomplete (.integer output) haccept hproducer hinstance
  have hread := (NativeIntegerArithmetic.decimalAdd_response ha hb hout).1
  have he : l = .int (a + b) := Option.some.inj (hl.symm.trans hread)
  subst l
  exact ⟨hl, rest⟩

theorem actual_call_request_completed_subtract_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n m : Nat} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hpost : YulangClosure.Prefix (CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    {left right output : String} {a b : Int}
    (ha : NativeLiteral.decodeInteger left = some a)
    (hb : NativeLiteral.decodeInteger right = some b)
    (hout : NativeIntegerArithmetic.decimalSubtract left right = some output)
    {role : NativeLiteral.Role} {sameValue : Prop}
    (haccept : NativeLiteral.Accepted (some .int) role sameValue (.integer output))
    (hinstance : op.responseType = .base .int) :
    NativeLiteral.readback (.integer output) = some (.int (a - b)) ∧
    TypedCall.ValueTyped Original.emptyContext
      (TypedCall.literalResponse (.int (a - b))) op.responseType ∧
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k)
        (TypedCall.literalResponse (.int (a - b)))) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames
        (plugResponse k (TypedCall.literalResponse (.int (a - b))))) term.resultType := by
  have hvalue := NativeIntegerArithmetic.decimalSubtract_result ha hb hout
  have hproducer : NativeLiteral.WellFormed (.integer output) :=
    (NativeLiteral.decodeInteger_exact.mp hvalue).1
  obtain ⟨l, hl, _, rest⟩ := actual_call_request_completed_native_literal_response
    hsuffix hp hhead hpost hcomplete (.integer output) haccept hproducer hinstance
  have hread := (NativeIntegerArithmetic.decimalSubtract_response ha hb hout).1
  have he : l = .int (a - b) := Option.some.inj (hl.symm.trans hread)
  subst l
  exact ⟨hl, rest⟩

end YulangClosure.Control
