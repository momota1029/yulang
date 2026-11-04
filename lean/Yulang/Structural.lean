import Yulang.Effects
import Yulang.Inference

/-!
# A concrete structural model for generated constraints

This is a reference ground type algebra, not a canonical MLsub model or a
subtyping decision procedure. Its subtype judgement has actual structural
rules and uses scoped `Effects.Row` occurrences for computation effects. It
provides a non-vacuous instance of the generic inference interface.

Record comparisons inspect the first occurrence of each field. Width applies
only to finite record spines, and must preserve every effective target field;
there is no unconditional rule discarding a possibly shadowing field.
-/

namespace Yulang.Structural

open Yulang.Inference
open Yulang.Effects

inductive Ty (Key : Type u) where
  | base : Base → Ty Key
  | bottom : Ty Key
  | union : Ty Key → Ty Key → Ty Key
  | inter : Ty Key → Ty Key → Ty Key
  | pair : Ty Key → Ty Key → Ty Key
  | emptyRecord : Ty Key
  | record : Nat → Ty Key → Ty Key → Ty Key
  | variant : Nat → Ty Key → Ty Key
  | arrow : Ty Key → Row Key → Ty Key → Row Key → Ty Key

/-- Lookup stops at the first field; a hidden duplicate is not a requirement. -/
def Ty.lookup (label : Nat) : Ty Key → Option (Ty Key)
  | .record current value rest => if label = current then some value else rest.lookup label
  | _ => none

inductive IsRecord : Ty Key → Prop where
  | empty : IsRecord .emptyRecord
  | field : IsRecord rest → IsRecord (.record label value rest)

/-- A structural preorder; it is intentionally not defined by solver success. -/
inductive Subtype : Ty Key → Ty Key → Prop where
  | refl (a : Ty Key) : Subtype a a
  | trans : Subtype a b → Subtype b c → Subtype a c
  | bottom (a : Ty Key) : Subtype .bottom a
  | unionLeft (a b : Ty Key) : Subtype a (.union a b)
  | unionRight (a b : Ty Key) : Subtype b (.union a b)
  | unionElim : Subtype a c → Subtype b c → Subtype (.union a b) c
  | interLeft (a b : Ty Key) : Subtype (.inter a b) a
  | interRight (a b : Ty Key) : Subtype (.inter a b) b
  | interIntro : Subtype c a → Subtype c b → Subtype c (.inter a b)
  | pair : Subtype a a' → Subtype b b' → Subtype (.pair a b) (.pair a' b')
  | variant : Subtype a b → Subtype (.variant label a) (.variant label b)
  | arrow : Subtype input' input → RowSubset inputRow' inputRow →
      Subtype output output' → RowSubset outputRow outputRow' →
      Subtype (.arrow input inputRow output outputRow)
        (.arrow input' inputRow' output' outputRow')
  | record : IsRecord source → IsRecord target →
      (∀ label value, target.lookup label = some value →
        ∃ actual, source.lookup label = some actual) →
      (∀ label actual expected, source.lookup label = some actual →
        target.lookup label = some expected → Subtype actual expected) →
      Subtype source target

/-- Actual scoped occurrence rows, with inclusion and union as their order/join. -/
def model (Key : Type u) : Model where
  Ty := Ty Key
  Row := Row Key
  base := Ty.base
  bottom := Ty.bottom
  union := Ty.union
  inter := Ty.inter
  pair := Ty.pair
  emptyRecord := Ty.emptyRecord
  record := Ty.record
  variant := Ty.variant
  arrow := Ty.arrow
  empty := []
  join := List.append
  subTy := Subtype
  subRow := RowSubset

theorem row_refl (row : Row Key) : RowSubset row row := fun _ h => h

theorem row_trans {a b c : Row Key} (ab : RowSubset a b) (bc : RowSubset b c) :
    RowSubset a c := fun o ho => bc o (ab o ho)

theorem row_bottom (row : Row Key) : RowSubset [] row := by
  intro occurrence impossible
  cases impossible

theorem row_join_left (a b : Row Key) : RowSubset a (a ++ b) :=
  fun _ h => List.mem_append.mpr (Or.inl h)

theorem row_join_right (a b : Row Key) : RowSubset b (a ++ b) :=
  fun _ h => List.mem_append.mpr (Or.inr h)

theorem row_join_least {a b c : Row Key} (ac : RowSubset a c) (bc : RowSubset b c) :
    RowSubset (a ++ b) c := by
  intro occurrence h
  exact (List.mem_append.mp h).elim (ac occurrence) (bc occurrence)

theorem row_join_comm (a b : Row Key) : RowEquiv (a ++ b) (b ++ a) := by
  intro occurrence
  simp only [List.mem_append, or_comm]

theorem row_join_idempotent (a : Row Key) : RowEquiv (a ++ a) a := by
  intro occurrence
  simp only [List.mem_append, or_self]

theorem row_join_assoc (a b c : Row Key) : RowEquiv ((a ++ b) ++ c) (a ++ (b ++ c)) := by
  intro occurrence
  simp only [List.mem_append, or_assoc]

theorem union_is_join (a b c : Ty Key) :
    Subtype (.union a b) c ↔ Subtype a c ∧ Subtype b c := by
  constructor
  · intro h
    exact ⟨.trans (.unionLeft a b) h, .trans (.unionRight a b) h⟩
  · rintro ⟨ha, hb⟩
    exact .unionElim ha hb

theorem inter_is_meet (a b c : Ty Key) :
    Subtype c (.inter a b) ↔ Subtype c a ∧ Subtype c b := by
  constructor
  · intro h
    exact ⟨.trans h (.interLeft a b), .trans h (.interRight a b)⟩
  · rintro ⟨ha, hb⟩
    exact .interIntro ha hb

theorem union_mono {a a' b b' : Ty Key} (ha : Subtype a a') (hb : Subtype b b') :
    Subtype (.union a b) (.union a' b') :=
  .unionElim (.trans ha (.unionLeft a' b')) (.trans hb (.unionRight a' b'))

theorem inter_mono {a a' b b' : Ty Key} (ha : Subtype a a') (hb : Subtype b b') :
    Subtype (.inter a b) (.inter a' b') :=
  .interIntro (.trans (.interLeft a b) ha) (.trans (.interRight a b) hb)

/-! ## Non-vacuity

A scalar observation is a small sound interpretation of this judgement. It
distinguishes base types and unions, without asserting that it characterizes
all structural subtypes or function denotations.
-/

def Scalar (observed : Base) : Ty Key → Prop
  | .base actual => actual = observed
  | .union a b => Scalar observed a ∨ Scalar observed b
  | .inter a b => Scalar observed a ∧ Scalar observed b
  | _ => False

theorem record_not_scalar (observed : Base) {record : Ty Key} (shape : IsRecord record) :
    ¬ Scalar observed record := by
  cases shape <;> simp [Scalar]

theorem scalar_preserved {a b : Ty Key} (subtype : Subtype a b) :
    ∀ observed, Scalar observed a → Scalar observed b := by
  induction subtype with
  | refl => exact fun _ h => h
  | trans _ _ ihab ihbc => exact fun observed h => ihbc observed (ihab observed h)
  | bottom => exact fun _ h => False.elim h
  | unionLeft => exact fun _ h => Or.inl h
  | unionRight => exact fun _ h => Or.inr h
  | unionElim _ _ iha ihb => exact fun observed h => h.elim (iha observed) (ihb observed)
  | interLeft => exact fun _ h => h.1
  | interRight => exact fun _ h => h.2
  | interIntro _ _ iha ihb => exact fun observed h => ⟨iha observed h, ihb observed h⟩
  | pair => exact fun _ h => False.elim h
  | variant => exact fun _ h => False.elim h
  | arrow => exact fun _ h => False.elim h
  | record sourceShape _ _ _ _ =>
    exact fun observed h => False.elim (record_not_scalar observed sourceShape h)

theorem distinct_bases_not_subtypes {left right : Base} (different : left ≠ right) :
    ¬ Subtype (Ty.base left : Ty Key) (.base right) := by
  intro h
  exact different ((scalar_preserved h left rfl).symm)

theorem int_not_str : ¬ Subtype (Ty.base .int : Ty Key) (.base .str) :=
  distinct_bases_not_subtypes (by decide)

theorem str_not_int : ¬ Subtype (Ty.base .str : Ty Key) (.base .int) :=
  distinct_bases_not_subtypes (by decide)

theorem int_union_str_not_int :
    ¬ Subtype (Ty.union (.base .int) (.base .str) : Ty Key) (.base .int) := by
  intro h
  exact str_not_int (.trans (.unionRight _ _) h)

/-! ## Record and variance witnesses -/

@[simp] theorem lookup_first (label : Nat) (head tail : Ty Key) :
    (Ty.record label head tail).lookup label = some head := by
  simp [Ty.lookup]

@[simp] theorem lookup_other (label other : Nat) (different : label ≠ other)
    (head tail : Ty Key) :
    (Ty.record other head tail).lookup label = tail.lookup label := by
  simp [Ty.lookup, different]

theorem first_field_wins (label : Nat) (first hidden tail : Ty Key) :
    (Ty.record label first (.record label hidden tail)).lookup label = some first := by
  simp

theorem record_width :
    Subtype (Ty.record 0 (.base .int) (.record 1 (.base .str) .emptyRecord) : Ty Key)
      (.record 0 (.base .int) .emptyRecord) := by
  apply Subtype.record (.field (.field .empty)) (.field .empty)
  · intro label value h
    by_cases hl : label = 0
    · subst label
      exact ⟨.base .int, by simp⟩
    · simp [Ty.lookup, hl] at h
  · intro label actual expected ha he
    by_cases hl : label = 0
    · subst label
      simp at ha he
      cases ha
      cases he
      exact .refl _
    · simp [Ty.lookup, hl] at he

theorem record_width_to_empty {record : Ty Key} (shape : IsRecord record) :
    Subtype record .emptyRecord := by
  apply Subtype.record shape .empty
  · intro label value h
    cases h
  · intro label actual expected _ h
    cases h

/-- Dropping a shadowing int head would expose str and fails the field obligation. -/
theorem shadowed_field_obligation_rejected :
    ¬ (∀ label actual expected,
      (Ty.record 0 (.base .int) (.record 0 (.base .str) .emptyRecord) : Ty Key).lookup
        label = some actual →
      (Ty.record 0 (.base .str) .emptyRecord : Ty Key).lookup label = some expected →
      Subtype actual expected) := by
  intro obligation
  exact int_not_str (obligation 0 (.base .int) (.base .str) (by simp) (by simp))

theorem arrow_variance (extra : Row Key) :
    Subtype
      (Ty.arrow (.union (.base .int) (.base .str)) extra (.base .int) [] : Ty Key)
      (.arrow (.base .int) [] (.union (.base .int) (.base .str)) extra) :=
  .arrow (.unionLeft _ _) (row_bottom _) (.unionLeft _ _) (row_bottom _)

/-! ## The generated constraints have concrete positive and negative instances -/

def heterogeneousBranch : Expr := .branch (.lit .bool) (.lit .int) (.lit .str)

theorem heterogeneous_branch_typing (Key : Type u) :
    Typing (model Key) [] heterogeneousBranch
      (.union (.base .int) (.base .str), []) := by
  apply Typing.branch (m := model Key)
    (a := (Ty.base .int, [])) (b := (Ty.base .str, [])) (eg := [])
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact ⟨.refl _, row_refl _⟩

theorem heterogeneous_branch_not_int (Key : Type u) (row : Row Key) :
    ¬ Typing (model Key) [] heterogeneousBranch (.base .int, row) := by
  intro h
  cases h with
  | branch _ _ no bound =>
    cases no with
    | lit noBound =>
      exact str_not_int (.trans noBound.1 (.trans (.unionRight _ _) bound.1))

theorem generated_heterogeneous_union_satisfied (environment : α → Comp (model Key)) :
    (generate [] heterogeneousBranch
      (CompTerm.pure (.union (.base .int) (.base .str)))).Holds (model Key) environment := by
  apply (generate_models_iff_typing (model Key) heterogeneousBranch [] [] environment
    _ (EnvRel.nil _ _)).mpr
  exact heterogeneous_branch_typing Key

theorem generated_heterogeneous_int_rejected (environment : α → Comp (model Key)) :
    ¬ (generate [] heterogeneousBranch (CompTerm.pure (.base .int))).Holds
      (model Key) environment := by
  intro h
  have typed := (generate_models_iff_typing (model Key) heterogeneousBranch [] [] environment
    _ (EnvRel.nil _ _)).mp h
  exact heterogeneous_branch_not_int Key [] typed

def identity : Expr := .lam (.var 0)

def identityType (base : Base) : Ty Key := .arrow (.base base) [] (.base base) []

theorem identity_typing (Key : Type u) (base : Base) :
    Typing (model Key) [] identity (identityType base, []) := by
  apply Typing.lam (m := model Key)
    (a := (Ty.base base, [])) (b := (Ty.base base, []))
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
  · exact ⟨.refl _, row_refl _⟩

theorem polymorphic_identity_application (Key : Type u) (base : Base) :
    Typing (model Key) [.poly identity []] (.app (.var 0) (.lit base)) (.base base, []) := by
  apply Typing.app (m := model Key)
    (a := (Ty.base base, [])) (b := (Ty.base base, [])) (ef := [])
  · exact Typing.var rfl (BindingTyping.poly (identity_typing Key base) (row_refl _))
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact ⟨.refl _, row_refl _⟩

def polymorphicIdentityPair : Expr :=
  .letE identity (.pair (.app (.var 0) (.lit .int)) (.app (.var 0) (.lit .str)))

/-- The value binding admits two independent instantiations, not just a finite formula. -/
theorem polymorphic_identity_pair_typing (Key : Type u) :
    Typing (model Key) [] polymorphicIdentityPair (.pair (.base .int) (.base .str), []) := by
  apply Typing.letValue (a := identityType .unit) rfl (identity_typing Key .unit)
  apply Typing.pair (m := model Key)
    (a := (Ty.base .int, [])) (b := (Ty.base .str, []))
  · exact polymorphic_identity_application Key .int
  · exact polymorphic_identity_application Key .str
  · exact ⟨.refl _, row_refl _⟩

theorem generated_polymorphic_identity_pair_satisfied
    (environment : α → Comp (model Key)) :
    (generate [] polymorphicIdentityPair
      (CompTerm.pure (.pair (.base .int) (.base .str)))).Holds (model Key) environment := by
  apply (generate_models_iff_typing (model Key) polymorphicIdentityPair [] [] environment
    _ (EnvRel.nil _ _)).mpr
  exact polymorphic_identity_pair_typing Key

def wideRecord : Expr := .record 0 (.lit .int) (.record 1 (.lit .str) .emptyRecord)

theorem wide_record_typing_at_narrow_type (Key : Type u) :
    Typing (model Key) [] wideRecord (.record 0 (.base .int) .emptyRecord, []) := by
  apply Typing.record (m := model Key)
    (a := (Ty.base .int, [])) (b := (Ty.record 1 (.base .str) .emptyRecord, []))
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · apply Typing.record (m := model Key)
      (a := (Ty.base .str, [])) (b := (Ty.emptyRecord, []))
    · exact Typing.lit ⟨.refl _, row_refl _⟩
    · exact Typing.emptyRecord ⟨.refl _, row_refl _⟩
    · exact record_width_to_empty .empty
    · exact ⟨.refl _, row_refl _⟩
  · exact record_width_to_empty (.field .empty)
  · exact ⟨record_width, row_refl _⟩

theorem record_field_uses_width (Key : Type u) :
    Typing (model Key) [] (.field 0 wideRecord) (.base .int, []) :=
  Typing.field (wide_record_typing_at_narrow_type Key) ⟨.refl _, row_refl _⟩

theorem generated_record_width_satisfied (environment : α → Comp (model Key)) :
    (generate [] (.field 0 wideRecord) (CompTerm.pure (.base .int))).Holds
      (model Key) environment := by
  apply (generate_models_iff_typing (model Key) (.field 0 wideRecord) [] [] environment
    _ (EnvRel.nil _ _)).mpr
  exact record_field_uses_width Key

/-- A scalar spread cannot be disguised as an arbitrary record tail. -/
theorem scalar_spread_rejected (out : Comp (model Key)) :
    ¬ Typing (model Key) [] (.record 0 (.lit .int) (.lit .str)) out := by
  intro h
  rcases (Typing.record_iff _ _ _ _ _ _).mp h with ⟨a, b, _, htail, hshape, _⟩
  have hbase := ((Typing.lit_iff _ _ _ _).mp htail).1
  have impossible := scalar_preserved (Subtype.trans hbase hshape) .str rfl
  exact impossible

theorem generated_scalar_spread_rejected (environment : α → Comp (model Key))
    (out : CompTerm α) :
    ¬ (generate [] (.record 0 (.lit .int) (.lit .str)) out).Holds
      (model Key) environment := by
  intro h
  exact scalar_spread_rejected (out.eval (model Key) environment)
    ((generate_models_iff_typing _ _ _ _ _ _ (EnvRel.nil _ _)).mp h)

end Yulang.Structural
