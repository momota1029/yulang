import Yulang.Effects
import Yulang.StructuralBase
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

abbrev Ty (Key : Type u) := StructuralBase.Ty (Row Key)

namespace Ty
export StructuralBase.Ty (base bottom union inter pair emptyRecord record variant arrow)

abbrev lookup (label : Nat) (ty : Ty Key) : Option (Ty Key) :=
  StructuralBase.Ty.lookup label ty
end Ty

abbrev IsRecord {Key : Type u} := @StructuralBase.IsRecord (Row Key)

namespace IsRecord
export StructuralBase.IsRecord (empty field)
end IsRecord

abbrev Subtype {Key : Type u} := StructuralBase.Subtype (@RowSubset Key)

namespace Subtype
export StructuralBase.Subtype
  (refl trans bottom unionLeft unionRight unionElim interLeft interRight interIntro
    pair variant arrow record)
end Subtype

/-- The legacy API specializes the shared type algebra to nonnegative rows. -/
abbrev model (Key : Type u) : Model :=
  StructuralBase.model (Row Key) [] List.append RowSubset

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
    Subtype (.union a b) c ↔ Subtype a c ∧ Subtype b c :=
  StructuralBase.union_is_join a b c

theorem inter_is_meet (a b c : Ty Key) :
    Subtype c (.inter a b) ↔ Subtype c a ∧ Subtype c b :=
  StructuralBase.inter_is_meet a b c

theorem union_mono {a a' b b' : Ty Key} (ha : Subtype a a') (hb : Subtype b b') :
    Subtype (.union a b) (.union a' b') := StructuralBase.union_mono ha hb

theorem inter_mono {a a' b b' : Ty Key} (ha : Subtype a a') (hb : Subtype b b') :
    Subtype (.inter a b) (.inter a' b') := StructuralBase.inter_mono ha hb

abbrev Scalar {Key : Type u} := @StructuralBase.Scalar (Row Key)

theorem record_not_scalar (observed : Base) {record : Ty Key} (shape : IsRecord record) :
    ¬ Scalar observed record := StructuralBase.record_not_scalar observed shape

theorem scalar_preserved {a b : Ty Key} (subtype : Subtype a b) :
    ∀ observed, Scalar observed a → Scalar observed b := StructuralBase.scalar_preserved subtype

theorem distinct_bases_not_subtypes {left right : Base} (different : left ≠ right) :
    ¬ Subtype (Ty.base left : Ty Key) (.base right) :=
  StructuralBase.distinct_bases_not_subtypes different

theorem int_not_str : ¬ Subtype (Ty.base .int : Ty Key) (.base .str) :=
  StructuralBase.int_not_str

theorem str_not_int : ¬ Subtype (Ty.base .str : Ty Key) (.base .int) :=
  StructuralBase.str_not_int

theorem int_union_str_not_int :
    ¬ Subtype (Ty.union (.base .int) (.base .str) : Ty Key) (.base .int) :=
  StructuralBase.int_union_str_not_int

@[simp] theorem lookup_first (label : Nat) (head tail : Ty Key) :
    (Ty.record label head tail).lookup label = some head :=
  StructuralBase.lookup_first label head tail

@[simp] theorem lookup_other (label other : Nat) (different : label ≠ other)
    (head tail : Ty Key) :
    (Ty.record other head tail).lookup label = tail.lookup label :=
  StructuralBase.lookup_other label other different head tail

theorem first_field_wins (label : Nat) (first hidden tail : Ty Key) :
    (Ty.record label first (.record label hidden tail)).lookup label = some first :=
  StructuralBase.first_field_wins label first hidden tail

theorem record_width :
    Subtype (Ty.record 0 (.base .int) (.record 1 (.base .str) .emptyRecord) : Ty Key)
      (.record 0 (.base .int) .emptyRecord) := StructuralBase.record_width

theorem record_width_to_empty {record : Ty Key} (shape : IsRecord record) :
    Subtype record .emptyRecord := StructuralBase.record_width_to_empty shape

theorem shadowed_field_obligation_rejected :
    ¬ (∀ label actual expected,
      (Ty.record 0 (.base .int) (.record 0 (.base .str) .emptyRecord) : Ty Key).lookup
        label = some actual →
      (Ty.record 0 (.base .str) .emptyRecord : Ty Key).lookup label = some expected →
      Subtype actual expected) := StructuralBase.shadowed_field_obligation_rejected

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
