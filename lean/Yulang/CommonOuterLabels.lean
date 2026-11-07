import Yulang.CommonPayloadProjection

/-!
# Finite outer-label support for common record inspection

Only record heads, default heads and masks can distinguish the label queried
at the current constructor layer. Guarded payload references are retained
without inspection. All labels outside this finite support therefore have
the same field and optional payload profiles; one fresh representative covers
them uniformly, including for arbitrary regular payloads.
-/

namespace Yulang.CommonOuterLabels

open CommonSyntax (Layer)
open CommonPayloadProjection

universe u v

variable {Row : Type u} {Index : Type v}

def labels : Layer Row Index → List Nat
  | .union first last | .inter first last => labels first ++ labels last
  | .record label _ rest | .recordDefault label rest _ => label :: labels rest
  | .mask hidden source => hidden ++ labels source
  | _ => []

theorem labels_map (rename : Index → Target) (source : Layer Row Index) :
    labels (source.map rename) = labels source := by
  induction source <;> simp_all [labels, Layer.map]

theorem optionalProject_outside (source : Layer Row Index) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    optionalProject hidden first source = optionalProject hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, optionalProject, List.mem_append, List.mem_cons]

theorem fieldProject_outside (source : Layer Row Index) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    fieldProject hidden first source = fieldProject hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, fieldProject, List.mem_append, List.mem_cons]

theorem fieldPresence_outside (source : Layer Row Index) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    CommonDefaultRequired.fieldPresence hidden first source =
      CommonDefaultRequired.fieldPresence hidden last source := by
  induction source generalizing hidden <;>
    simp_all [labels, CommonDefaultRequired.fieldPresence, List.mem_append, List.mem_cons]

theorem optionalType_outside (source : Common.Ty) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    optionalType hidden first source = optionalType hidden last source := by
  unfold optionalType
  rw [optionalProject_outside source hidden first last firstHidden lastHidden firstOutside lastOutside]

theorem fieldType_outside (source : Common.Ty) (hidden : List Nat)
    (first last : Nat) (firstHidden : first ∉ hidden) (lastHidden : last ∉ hidden)
    (firstOutside : first ∉ labels source) (lastOutside : last ∉ labels source) :
    fieldType hidden first source = fieldType hidden last source := by
  unfold fieldType
  rw [fieldProject_outside source hidden first last firstHidden lastHidden firstOutside lastOutside]

/-- A finite representative strictly larger than every listed label. -/
def fresh : List Nat → Nat
  | [] => 0
  | label :: rest => label + fresh rest + 1

theorem member_lt_fresh (support : List Nat) (label : Nat) (member : label ∈ support) :
    label < fresh support := by
  induction support with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | remaining
      · simp only [fresh]
        omega
      · have smaller := ih remaining
        simp only [fresh]
        omega

theorem fresh_not_mem (support : List Nat) : fresh support ∉ support :=
  fun member => Nat.lt_irrefl _ (member_lt_fresh support (fresh support) member)

def representatives (support : List Nat) : List Nat := fresh support :: support

/-- A property invariant outside finite support is completely checked by the
listed labels and one fresh label. The property itself need not be decidable. -/
theorem forall_iff_representatives (support : List Nat) (property : Nat → Prop)
    (outside : ∀ first last, first ∉ support → last ∉ support →
      (property first ↔ property last)) :
    (∀ label, property label) ↔ ∀ label ∈ representatives support, property label := by
  constructor
  · intro allLabels label _
    exact allLabels label
  · intro finite label
    by_cases member : label ∈ support
    · exact finite label (List.mem_cons.mpr (Or.inr member))
    · exact (outside label (fresh support) member (fresh_not_mem support)).mpr
        (finite (fresh support) (List.mem_cons.mpr (Or.inl rfl)))

end Yulang.CommonOuterLabels
