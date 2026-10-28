import YulangClosure.NativeLiteralReadback
import Init.Data.Int.Compare
import Init.Data.Nat.Compare
import Init.Omega

/-! R40 candidate source correspondence for decimal.rs:6–27.
The algorithm below compares normalized byte lengths and lexicographic ASCII
order. Its specification uses NativeLiteral's independent positional fold.
This file does not execute Rust or establish native trace realization. -/
namespace YulangClosure.NativeIntegerComparison

open NativeLiteral

/-- Independent positional expansion used only in proofs, never by comparison. -/
def value : List UInt8 → Nat
  | [] => 0
  | c :: cs => (c.toNat - 48) * 10 ^ cs.length + value cs

theorem fold_expansion (ds : List UInt8) (acc : Nat) :
    decimalFold acc ds = acc * 10 ^ ds.length + value ds := by
  induction ds generalizing acc with
  | nil => simp [decimalFold, value]
  | cons c cs ih =>
      rw [decimalFold_cons, ih]
      simp [value, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

theorem fold_zero (ds : List UInt8) : decimalFold 0 ds = value ds := by
  simp [fold_expansion]

/-- Rust trim_start_matches('0'), on the already checked ASCII digit bytes. -/
def trimZeros : List UInt8 → List UInt8
  | [] => []
  | c :: cs => if c.toNat = 48 then trimZeros cs else c :: cs

/-- Canonical zero is the one-byte word 0; every other word starts nonzero. -/
def Canonical (ds : List UInt8) : Prop :=
  ds = [48] ∨ ∃ c cs, ds = c :: cs ∧ 48 < c.toNat

/-- Both outputs of Rust parts, including its negative-zero rule. -/
def normalize (negative : Bool) (ds : List UInt8) : Bool × List UInt8 :=
  match trimZeros ds with
  | [] => (false, [48])
  | c :: cs => (negative, c :: cs)

/-- Byte-list parser: exactly one optional minus, nonempty ASCII digits. -/
def parseBytes (bytes : List UInt8) : Option (Bool × List UInt8) :=
  let p := splitSign bytes
  if p.2 ≠ [] ∧ Digits p.2 then some (normalize p.1 p.2) else none

def parts (text : String) : Option (Bool × List UInt8) :=
  parseBytes text.toUTF8.data.toList

theorem parseBytes_success_iff (bytes : List UInt8) :
    (∃ p, parseBytes bytes = some p) ↔
      (splitSign bytes).2 ≠ [] ∧ Digits (splitSign bytes).2 := by
  simp only [parseBytes]
  split <;> simp_all

theorem parts_success_iff (text : String) :
    (∃ p, parts text = some p) ↔ Grammar text :=
  parseBytes_success_iff _

theorem parts_reject_iff (text : String) :
    parts text = none ↔ ¬ Grammar text := by
  change (if Grammar text then
    some (normalize (splitSign text.toUTF8.data.toList).1
      (splitSign text.toUTF8.data.toList).2) else none) = none ↔ ¬ Grammar text
  by_cases h : Grammar text <;> simp [h]

theorem trim_spec {ds : List UInt8} (hd : Digits ds) :
    Digits (trimZeros ds) ∧ value (trimZeros ds) = value ds ∧
      (trimZeros ds = [] ∨ ∃ c cs, trimZeros ds = c :: cs ∧ 48 < c.toNat) := by
  induction ds with
  | nil => simp [trimZeros, value, Digits]
  | cons c cs ih =>
      obtain ⟨hc, hcs⟩ := hd
      obtain ⟨ht, hv, hz⟩ := ih hcs
      by_cases hzero : c.toNat = 48
      · simpa [trimZeros, hzero, value] using And.intro ht (And.intro hv hz)
      · have hpos : 48 < c.toNat := by
          obtain ⟨hlo, hhi⟩ := hc
          omega
        simpa only [trimZeros, hzero, ↓reduceIte] using
          (show Digits (c :: cs) ∧ value (c :: cs) = value (c :: cs) ∧
            ((c :: cs) = [] ∨ ∃ d es, c :: cs = d :: es ∧ 48 < d.toNat) from
              ⟨⟨hc, hcs⟩, rfl, Or.inr ⟨c, cs, rfl, hpos⟩⟩)

theorem normalize_spec (negative : Bool) {ds : List UInt8} (hd : Digits ds) :
    Digits (normalize negative ds).2 ∧ Canonical (normalize negative ds).2 ∧
    signedValue (normalize negative ds).1 (value (normalize negative ds).2) =
      signedValue negative (value ds) ∧
    ((normalize negative ds).1 = true → 0 < value (normalize negative ds).2) := by
  obtain ⟨ht, hv, hz⟩ := trim_spec hd
  cases he : trimZeros ds with
  | nil =>
      have hv0 : value ds = 0 := by simpa [he, value] using hv.symm
      simp [normalize, he, Digits, AsciiDigit, Canonical, value, hv0, signedValue]
  | cons c cs =>
      have hcpos : 48 < c.toNat := by
        rcases hz with hz | ⟨d, es, hde, hp⟩
        · simp [he] at hz
        · rw [he] at hde
          cases hde
          exact hp
      have hp : 0 < value (c :: cs) := by
        have hm := Nat.mul_le_mul_right (10 ^ cs.length)
          (show 1 ≤ c.toNat - 48 by omega)
        have hpow : 0 < 10 ^ cs.length := by
          have hh := Nat.pow_le_pow_right (n := 10) (by decide : 0 < 10)
            (i := 0) (j := cs.length) (Nat.zero_le _)
          have hh' : 1 ≤ 10 ^ cs.length := by simpa using hh
          omega
        simp only [Nat.one_mul] at hm
        simp only [value]
        omega
      have hv' : value (c :: cs) = value ds := by simpa [he] using hv
      simp only [normalize, he]
      exact ⟨by simpa [he] using ht, Or.inr ⟨c, cs, rfl, hcpos⟩,
        congrArg (signedValue negative) hv', fun _ => hp⟩

/-- Lexicographic order on bytes, using their unsigned ASCII codes. -/
def lexCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then .lt
      else if b.toNat < a.toNat then .gt else lexCompare as bs

/-- Rust: left.len().cmp(right.len()).then_with(|| left.cmp(right)). -/
def magnitude (left right : List UInt8) : Ordering :=
  if left.length < right.length then .lt
  else if right.length < left.length then .gt else lexCompare left right

/-- The exact four Rust sign arms; negative-negative swaps magnitudes. -/
def compareParts (left right : Bool × List UInt8) : Ordering :=
  match left.1, right.1 with
  | true, false => .lt
  | false, true => .gt
  | false, false => magnitude left.2 right.2
  | true, true => magnitude right.2 left.2

def compare (left right : String) : Option Ordering := do
  let l ← parts left
  let r ← parts right
  pure (compareParts l r)

/-- Every n-digit word denotes less than 10^n, even with leading zeros. -/
theorem value_bound {ds : List UInt8} (hd : Digits ds) :
    value ds < 10 ^ ds.length := by
  induction ds with
  | nil => simp [value]
  | cons c cs ih =>
      obtain ⟨⟨hlo, hhi⟩, hcs⟩ := hd
      have ht := ih hcs
      have hm := Nat.mul_le_mul_right (10 ^ cs.length)
        (show c.toNat - 48 + 1 ≤ 10 by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hm
      simp only [value, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (10 ^ cs.length) 10]
      omega

/-- A positive leading digit supplies the lower bound for a canonical word. -/
theorem value_lower {c : UInt8} {cs : List UInt8} (hp : 48 < c.toNat) :
    10 ^ cs.length ≤ value (c :: cs) := by
  have hm := Nat.mul_le_mul_right (10 ^ cs.length)
    (show 1 ≤ c.toNat - 48 by omega)
  simp only [Nat.one_mul] at hm
  simp only [value]
  omega

/-- Different digit blocks cannot overlap when their remainders are < p. -/
theorem block_lt {a b p x y : Nat} (hab : a < b) (hx : x < p) :
    a * p + x < b * p + y := by
  have hm := Nat.mul_le_mul_right p (show a + 1 ≤ b by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem compare_add_prefix (pre x y : Nat) :
    Ord.compare (pre + x) (pre + y) = Ord.compare x y := by
  simp only [Nat.compare_eq_ite_lt, Nat.add_lt_add_iff_left]

/-- Equal-width lexicographic order is positional order; no canonical premise. -/
theorem lex_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right) (hlen : left.length = right.length) :
    lexCompare left right = Ord.compare (value left) (value right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          change Ordering.eq = Ord.compare (0 : Nat) 0
          exact (Nat.compare_eq_eq.mpr rfl).symm
      | cons b bs =>
          simp only [List.length_nil, List.length_cons] at hlen
          exact Nat.noConfusion hlen
  | cons a as ih =>
      cases right with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlen
          exact Nat.noConfusion hlen
      | cons b bs =>
          obtain ⟨⟨ha0, ha9⟩, has⟩ := hl
          obtain ⟨⟨hb0, hb9⟩, hbs⟩ := hr
          have he : as.length = bs.length := by simpa using hlen
          have hva := value_bound has
          have hvb := value_bound hbs
          by_cases hab : a.toNat < b.toNat
          · have hv : value (a :: as) < value (b :: bs) := by
              simp only [value, he]
              apply block_lt (Nat.sub_lt_sub_right ha0 hab)
              simpa [he] using hva
            rw [lexCompare, ite_eq_left hab]
            exact (Nat.compare_eq_lt.mpr hv).symm
          · by_cases hba : b.toNat < a.toNat
            · have hv : value (b :: bs) < value (a :: as) := by
                simp only [value, he]
                exact block_lt (Nat.sub_lt_sub_right hb0 hba) hvb
              rw [lexCompare, ite_eq_right hab, ite_eq_left hba]
              exact (Nat.compare_eq_gt.mpr hv).symm
            · have heq : a.toNat = b.toNat :=
                Nat.le_antisymm (Nat.le_of_not_lt hba) (Nat.le_of_not_lt hab)
              simp only [lexCompare, hab, hba, ↓reduceIte]
              rw [ih has hbs he]
              simp only [value, heq, he, compare_add_prefix]

/-- Canonical shorter words have smaller mathematical magnitude. -/
theorem shorter_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (cl : Canonical left) (cr : Canonical right)
    (hlen : left.length < right.length) : value left < value right := by
  have hleft : 0 < left.length := by
    rcases cl with rfl | ⟨c, cs, rfl, hp⟩ <;> simp
  rcases cr with rfl | ⟨c, cs, rfl, hp⟩
  · simp only [List.length_cons, List.length_nil] at hlen
    omega
  · have hu := value_bound hl
    have hlo := value_lower (cs := cs) hp
    have hexp : left.length ≤ cs.length := by
      simp only [List.length_cons] at hlen
      omega
    have hm := Nat.pow_le_pow_right (n := 10) (by decide : 0 < 10) hexp
    omega

theorem magnitude_value {left right : List UInt8}
    (hl : Digits left) (hr : Digits right)
    (cl : Canonical left) (cr : Canonical right) :
    magnitude left right = Ord.compare (value left) (value right) := by
  unfold magnitude
  split
  next h => exact (Nat.compare_eq_lt.mpr (shorter_value hl hr cl cr h)).symm
  next h =>
    split
    next h' => exact (Nat.compare_eq_gt.mpr (shorter_value hr hl cr cl h')).symm
    next h' => exact lex_value hl hr (by omega)

/-- The comparison bridge for the four normalized sign cases. -/
theorem compareParts_value {left right : Bool × List UInt8}
    (hl : Digits left.2) (hr : Digits right.2)
    (cl : Canonical left.2) (cr : Canonical right.2)
    (nl : left.1 = true → 0 < value left.2)
    (nr : right.1 = true → 0 < value right.2) :
    compareParts left right =
      Ord.compare (signedValue left.1 (value left.2))
        (signedValue right.1 (value right.2)) := by
  obtain ⟨ls, ld⟩ := left
  obtain ⟨rs, rd⟩ := right
  cases ls <;> cases rs
  · simpa [compareParts, signedValue, Int.compare_eq_ite_lt,
      Nat.compare_eq_ite_lt] using magnitude_value hl hr cl cr
  · have hp : 0 < value rd := nr rfl
    have hpos : (0 : Int) < Int.ofNat (value rd) := Int.ofNat_lt.mpr hp
    have hlt : -(Int.ofNat (value rd)) < Int.ofNat (value ld) :=
      Int.lt_of_lt_of_le (Int.neg_neg_of_pos hpos) (Int.natCast_nonneg _)
    simpa [compareParts, signedValue] using (Int.compare_eq_gt.mpr hlt).symm
  · have hp : 0 < value ld := nl rfl
    have hpos : (0 : Int) < Int.ofNat (value ld) := Int.ofNat_lt.mpr hp
    have hlt : -(Int.ofNat (value ld)) < Int.ofNat (value rd) :=
      Int.lt_of_lt_of_le (Int.neg_neg_of_pos hpos) (Int.natCast_nonneg _)
    simpa [compareParts, signedValue] using (Int.compare_eq_lt.mpr hlt).symm
  · simpa [compareParts, signedValue, Int.compare_eq_ite_lt,
      Nat.compare_eq_ite_lt] using magnitude_value hr hl cr cl

/-- Successful parsing preserves exactly NativeLiteral's signed positional value. -/
theorem parts_spec {text : String} {p : Bool × List UInt8}
    (hp : parts text = some p) :
    Grammar text ∧ Digits p.2 ∧ Canonical p.2 ∧
      signedValue p.1 (value p.2) = mathematicalValue text ∧
      (p.1 = true → 0 < value p.2) := by
  have hg := (parts_success_iff text).mp ⟨p, hp⟩
  have he : p = normalize (splitSign text.toUTF8.data.toList).1
      (splitSign text.toUTF8.data.toList).2 := by
    have hp' := hp
    change (if Grammar text then some (normalize
      (splitSign text.toUTF8.data.toList).1
      (splitSign text.toUTF8.data.toList).2) else none) = some p at hp'
    simpa [hg] using hp'.symm
  subst p
  obtain ⟨hd, hc, hv, hn⟩ := normalize_spec
    (splitSign text.toUTF8.data.toList).1 hg.2
  exact ⟨hg, hd, hc, by simpa [mathematicalValue, fold_zero] using hv, hn⟩

/-- R40 parent: every successfully decoded pair has exactly Int.compare order. -/
theorem compare_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    compare left right = some (Ord.compare a b) := by
  obtain ⟨hgl, hvl⟩ := decodeInteger_exact.mp ha
  obtain ⟨hgr, hvr⟩ := decodeInteger_exact.mp hb
  obtain ⟨lp, hlp⟩ := (parts_success_iff left).mpr hgl
  obtain ⟨rp, hrp⟩ := (parts_success_iff right).mpr hgr
  obtain ⟨_, hld, hlc, hlv, hln⟩ := parts_spec hlp
  obtain ⟨_, hrd, hrc, hrv, hrn⟩ := parts_spec hrp
  have hc := compareParts_value hld hrd hlc hrc hln hrn
  rw [hlv, hrv, hvl, hvr] at hc
  simp [compare, hlp, hrp, hc]

def intEq (left right : String) : Option Bool :=
  (compare left right).map Ordering.isEq

def intLt (left right : String) : Option Bool :=
  (compare left right).map Ordering.isLT

def intLe (left right : String) : Option Bool :=
  (compare left right).map (fun o => !o.isGT)

def intGt (left right : String) : Option Bool :=
  (compare left right).map Ordering.isGT

def intGe (left right : String) : Option Bool :=
  (compare left right).map (fun o => !o.isLT)

/-- The five concrete consumer projections, retaining shared decoded a and b. -/
theorem boolean_projections {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intEq left right = some (decide (a = b)) ∧
    intLt left right = some (decide (a < b)) ∧
    intLe left right = some (decide (a ≤ b)) ∧
    intGt left right = some (decide (a > b)) ∧
    intGe left right = some (decide (a ≥ b)) := by
  have hc := compare_decode ha hb
  have he : (Ord.compare a b).isEq = decide (a = b) := by
    exact Bool.eq_iff_iff.mpr (Ordering.isEq_iff_eq_eq.trans
      (Int.compare_eq_eq.trans decide_eq_true_iff.symm))
  have hlt : (Ord.compare a b).isLT = decide (a < b) := by
    apply Bool.eq_iff_iff.mpr
    simp [Int.compare_eq_lt]
  have hle : (Ord.compare a b).isLE = decide (a ≤ b) := by
    apply Bool.eq_iff_iff.mpr
    simp [Int.isLE_compare]
  have hgt : (Ord.compare a b).isGT = decide (a > b) := by
    apply Bool.eq_iff_iff.mpr
    simp [Int.compare_eq_gt]
  have hge : (Ord.compare a b).isGE = decide (a ≥ b) := by
    apply Bool.eq_iff_iff.mpr
    simp [Int.isGE_compare]
  simp [intEq, intLt, intLe, intGt, intGe, hc, he, hlt, hle, hgt, hge]

theorem intEq_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intEq left right = some (decide (a = b)) := (boolean_projections ha hb).1

theorem intLt_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intLt left right = some (decide (a < b)) := (boolean_projections ha hb).2.1

theorem intLe_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intLe left right = some (decide (a ≤ b)) := (boolean_projections ha hb).2.2.1

theorem intGt_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intGt left right = some (decide (a > b)) := (boolean_projections ha hb).2.2.2.1

theorem intGe_decode {left right : String} {a b : Int}
    (ha : decodeInteger left = some a) (hb : decodeInteger right = some b) :
    intGe left right = some (decide (a ≥ b)) := (boolean_projections ha hb).2.2.2.2

/-! Kernel-reduction discriminators; primary verification is required. -/
example : compare "-0" "000" = some .eq := by decide
example : compare "00042" "42" = some .eq := by decide
example : compare "-00042" "-42" = some .eq := by decide
example : compare "-10" "-2" = some .lt := by decide
example : compare "-1" "0" = some .lt := by decide
example : compare "0" "-1" = some .gt := by decide
example : compare "9" "10" = some .lt := by decide
example : compare "12" "19" = some .lt := by decide
example : compare "123456789012345678901234567890" "123456789012345678901234567891" =
    some .lt := by decide
example : compare "-123456789012345678901234567891" "-123456789012345678901234567890" =
    some .lt := by decide
example : parts "" = none := by decide
example : parts "-" = none := by decide
example : parts "+1" = none := by decide
example : parts "--1" = none := by decide
example : parts "１２" = none := by decide
example : compare "1x" "2" = none := by decide
example : compare "2" " 1" = none := by decide
example : intEq "-0" "00" = some true := by decide
example : intLt "-2" "-10" = some false := by decide
example : intLe "0003" "3" = some true := by decide
example : intGt "4" "-4" = some true := by decide
example : intGe "-4" "4" = some false := by decide

end YulangClosure.NativeIntegerComparison
