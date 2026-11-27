import Yulang.GeneralDeclarativeI65I74RoutedRecordEntry455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTrail455.MixedNative456
open Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open RecordTraversal455 (OpenOps)

inductive ExactExtra : TyTerm Nat → Expr → Prop where
  | variant : ExactExtra (.variant tag (.var child)) (.variant tag (.variable child))
  | pair : ExactExtra (.pair (.var left) (.var right)) (.primitive .pair [.variable left,.variable right])

def checkExtra : TyTerm Nat → Expr → Bool
  | .variant tag (.var a), .variant name (.variable b) => (tag == name) && (a == b)
  | .pair (.var x) (.var y), .primitive .pair [.variable a,.variable b] => (x == a) && (y == b)
  | _,_ => false

theorem extra_exact (term : TyTerm Nat) (raw : Expr) :
    checkExtra term raw = true ↔ ExactExtra term raw := by
  constructor
  · intro passed
    unfold checkExtra at passed
    split at passed
    · rename_i t x u y
      have same : t = u ∧ x = y := by simpa [Bool.and_eq_true] using passed
      obtain ⟨rfl,rfl⟩ := same
      exact .variant
    · rename_i a b c d
      have same : a = c ∧ b = d := by simpa [Bool.and_eq_true] using passed
      obtain ⟨rfl,rfl⟩ := same
      exact .pair
    · cases passed
  · intro syntaxFact
    cases syntaxFact <;> simp [checkExtra]

def AuthorizedExtra (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation) : Prop :=
  ∃ o ∈ s.origins, OriginRoute s o logical ∧ o.slot = row.left ∧ ∃ term,
    o.endpoint = .ordinary term ∧ ExactExtra term row.right

def checkAuthExtra (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation)
    (i : Nat) : Bool :=
  match s.origins[i]? with
  | some origin =>
    match origin.endpoint with
    | .ordinary term => ((origin.slot == row.left) && checkOriginalRoute s origin logical) &&
      checkExtra term row.right
    | _ => false
  | none => false

theorem real_extra_original_iff_finite_ordinal455 (s : GeneralDeclarativeI65.State)
    (logical : Nat) (row : Equation) :
    (∃ i, checkAuthExtra s logical row i = true) ↔ AuthorizedExtra s logical row := by
  constructor
  · rintro ⟨i,passed⟩
    cases src : s.origins[i]? with
    | none => simp [checkAuthExtra,src] at passed
    | some o =>
      cases k : o.endpoint with
      | nominal name args => simp [checkAuthExtra,src,k] at passed
      | ordinary term =>
        have yes : (o.slot = row.left ∧ checkOriginalRoute s o logical = true) ∧
            checkExtra term row.right = true := by
          simpa [checkAuthExtra,src,k,Bool.and_eq_true] using passed
        exact ⟨o,List.mem_of_getElem? src,(original_route_iff_data455 ..).mp yes.1.2,yes.1.1,
          term,k,(extra_exact ..).mp yes.2⟩
  · rintro ⟨o,atOrigin,route,slot,term,formed,correct⟩
    obtain ⟨i,src⟩ := List.mem_iff_getElem?.mp atOrigin
    exact ⟨i,by simp [checkAuthExtra,src,formed,slot,
      (original_route_iff_data455 ..).mpr route,(extra_exact ..).mpr correct]⟩

theorem named_variant_or_pair_opener_keeps_original_issuer_and_model455
    {s : GeneralDeclarativeI65.State} {logical row} (w : AuthorizedExtra s logical row)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ o ∈ s.origins, OriginRoute s o logical ∧ o.slot = row.left ∧ ∃ term,
      m.nativeSyntax row.left = some (.ordinary term) ∧ ExactExtra term row.right := by
  obtain ⟨o,atOrigin,route,slot,term,observed,correct⟩ := w
  exact ⟨o,atOrigin,route,slot,term,by simpa only [slot,observed] using fit.2 o atOrigin,correct⟩

/-- Proof-only next scope. No use by the public C455 entry. -/
def extraOpenOps (s : GeneralDeclarativeI65.State) : OpenOps where
  Token := Nat
  allowed := fun root row => RoutedOpen s root row ∨ AuthorizedExtra s root row
  check := fun root row i => checkRoutedOpen s root row i || checkAuthExtra s root row i
  exactCheck := by
    intro root row
    constructor
    · rintro ⟨i,passed⟩
      rcases Bool.or_eq_true_iff.mp passed with left | right
      · exact .inl ((routed_open_iff_finite_same_origin_wire455 ..).mp ⟨i,left⟩)
      · exact .inr ((real_extra_original_iff_finite_ordinal455 ..).mp ⟨i,right⟩)
    · intro has
      rcases has with left | right
      · obtain ⟨i,l⟩ := (routed_open_iff_finite_same_origin_wire455 ..).mpr left
        exact ⟨i,Bool.or_eq_true_iff.mpr (.inl l)⟩
      · obtain ⟨i,r⟩ := (real_extra_original_iff_finite_ordinal455 ..).mpr right
        exact ⟨i,Bool.or_eq_true_iff.mpr (.inr r)⟩

end Yulang.GeneralDeclarativeI65.I72.RecordTrail455.MixedNative456
open Yulang.GeneralDeclarativeI65.I72.RecordTrail455.MixedNative456
