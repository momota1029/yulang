import Yulang.GeneralDeclarativeI65I74IdenticalTagProjection459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.HomogeneousWrittenTags459
open GeneralDeclarationPatterns
open IdenticalTagProjection459

/-- One unchanged written tag and payload, repeated along an arbitrary finite
source join tree. The count is evidence of how many original leaves occur;
it does not choose an implementation or diagnostic representative. -/
inductive Family : Pattern → Nat → Pattern → Nat → Prop where
  | leaf : Family (.variant tag payload) tag payload 1
  | join : Family first tag payload n → Family last tag payload m →
      Family (.join first last) tag payload (n+m)

def read : Pattern → Option (Nat × Pattern × Nat)
  | .variant tag payload => some (tag,payload,1)
  | .join first last => do
    let (tag,payload,n) ← read first
    let (other,body,m) ← read last
    if tag = other ∧ payload = body then some (tag,payload,n+m)
    else none
  | _ => none

theorem exact_independent_literal_family459 {p tag payload n} :
    read p = some (tag,payload,n) ↔ Family p tag payload n := by
  constructor
  · intro seen
    cases p with
    | var => cases seen
    | app => cases seen
    | record => cases seen
    | variant t body =>
      have h := Option.some.inj seen
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact .leaf
    | join a b =>
      cases foundA : read a <;> simp [read,foundA,Option.bind] at seen
      rename_i tripleA
      obtain ⟨first,A,ni⟩ := tripleA
      cases foundB : read b <;> simp [foundB] at seen
      rename_i tripleB
      obtain ⟨last,B,mi⟩ := tripleB
      by_cases equal : first = last ∧ A = B
      · simp [equal] at seen
        obtain ⟨rfl,rfl,rfl⟩ := seen
        obtain ⟨rfl,rfl⟩ := equal
        exact .join ((exact_independent_literal_family459).mp foundA)
          ((exact_independent_literal_family459).mp foundB)
      · simp [equal] at seen
  · intro actual
    induction actual with
    | leaf => rfl
    | join one two h1 h2 => simp [read,h1,h2,Option.bind]
termination_by sizeOf p

theorem actual_nonempty_written_family459 {p tag payload n} (f : Family p tag payload n) : n > 0 := by
  induction f
  · decide
  · omega

theorem exact_homogeneous_house_normalizes_after_every_capture459
    {p tag payload n} (f : Family p tag payload n) (capture : Nat → Pattern) :
    normalize (p.subst capture) = normalize ((Pattern.variant tag payload).subst capture) := by
  induction f with
  | leaf => rfl
  | join lhs rhs l r =>
    simp [Pattern.subst,normalize,merge,l,r]

/-- Auxiliary source query projection only; does not delete written occurrence
data or select a raw graph row. -/
def collapse (p : Pattern) : Pattern :=
  match read p with
  | some (key,body,count) =>
    if count > 1 then .variant key body else p
  | none => p

theorem safely_collapse_only_a_real_written_homogeneous_family459 (p : Pattern) (capture : Nat → Pattern) :
    normalize ((collapse p).subst capture) = normalize (p.subst capture) := by
  cases found : read p with
  | none => simp [collapse,found]
  | some triple =>
    obtain ⟨key,body,count⟩ := triple
    by_cases redundant : count > 1
    · simpa [collapse,found,redundant] using
        (exact_homogeneous_house_normalizes_after_every_capture459
          ((exact_independent_literal_family459).mp found) capture).symm
    · simp [collapse,found,redundant]

theorem identical_three_original_arms_have_same_tree459 (key : Nat) (body : Pattern) :
    let item := Pattern.variant key body
    read (.join item (.join item item)) = some (key,body,3) ∧
      read (.join (.join item item) item) = some (key,body,3) := by
  simp [read,Option.bind]

theorem nonidentical_same_tag_originals_not_collapsed459 (key : Nat) {p q : Pattern}
    (distinct : p ≠ q) : collapse (.join (.variant key p) (.variant key q)) =
      .join (.variant key p) (.variant key q) := by
  simp [collapse,read,Option.bind,distinct]

end Yulang.GeneralDeclarativeI65.I72.HomogeneousWrittenTags459
