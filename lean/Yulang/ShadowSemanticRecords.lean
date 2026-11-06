import Yulang.RigidSemanticRecords

/-!
# Records with arbitrary-tail hidden-field equality

Decision 40 extends the decision-39 relation by precisely the two directions
of `record l A (record l B R) = record l A R`, for every raw tail R.
The preceding relations and their boundary theorems remain unchanged.
This is the least closure of the previous rules and the new equation;
it does not add arbitrary-tail covariance or constructor distribution.
-/

namespace Yulang.ShadowSemanticRecords

open Inference
open StructuralBase (Ty IsRecord)

universe u

variable {Row : Type u}

/-- The existing structural rules and decision 40, with recursive premises
in the extended relation. Neither hidden payload nor tail is restricted. -/
inductive Subtype (leRow : Row → Row → Prop) : Ty Row → Ty Row → Prop where
  | refl (a : Ty Row) : Subtype leRow a a
  | trans : Subtype leRow a b → Subtype leRow b c → Subtype leRow a c
  | bottom (a : Ty Row) : Subtype leRow .bottom a
  | top (a : Ty Row) : Subtype leRow a .top
  | unionLeft (a b : Ty Row) : Subtype leRow a (.union a b)
  | unionRight (a b : Ty Row) : Subtype leRow b (.union a b)
  | unionElim : Subtype leRow a c → Subtype leRow b c → Subtype leRow (.union a b) c
  | interLeft (a b : Ty Row) : Subtype leRow (.inter a b) a
  | interRight (a b : Ty Row) : Subtype leRow (.inter a b) b
  | interIntro : Subtype leRow c a → Subtype leRow c b → Subtype leRow c (.inter a b)
  | pair : Subtype leRow a a' → Subtype leRow b b' → Subtype leRow (.pair a b) (.pair a' b')
  | variant : Subtype leRow a b → Subtype leRow (.variant label a) (.variant label b)
  | arrow : Subtype leRow input' input → leRow inputRow' inputRow →
      Subtype leRow output output' → leRow outputRow outputRow' →
      Subtype leRow (.arrow input inputRow output outputRow)
        (.arrow input' inputRow' output' outputRow')
  | record : IsRecord source → IsRecord target →
      (∀ label value, target.lookup label = some value →
        ∃ actual, source.lookup label = some actual) →
      (∀ label actual expected, source.lookup label = some actual →
        target.lookup label = some expected → Subtype leRow actual expected) →
      Subtype leRow source target
  | recordCongr : Subtype leRow value value' → Subtype leRow value' value →
      Subtype leRow rest rest' → Subtype leRow rest' rest →
      Subtype leRow (.record label value rest) (.record label value' rest')
  | recordTail : IsRecord rest' → Subtype leRow rest rest' →
      Subtype leRow (.record label value rest) (.record label value rest')
  | shadowErase (label : Nat) (visible hidden rest : Ty Row) :
      Subtype leRow (.record label visible (.record label hidden rest))
        (.record label visible rest)
  | shadowInsert (label : Nat) (visible hidden rest : Ty Row) :
      Subtype leRow (.record label visible rest)
        (.record label visible (.record label hidden rest))

variable {leRow : Row → Row → Prop}

/-- Every old subtype derivation remains valid, without a record-spine
restriction on the statement being transported. -/
theorem old_subtype {a b : Ty Row} (old : StructuralBase.Subtype leRow a b) :
    Subtype leRow a b := by
  induction old with
  | refl a => exact .refl a
  | trans _ _ first last => exact .trans first last
  | bottom a => exact .bottom a
  | top a => exact .top a
  | unionLeft a b => exact .unionLeft a b
  | unionRight a b => exact .unionRight a b
  | unionElim _ _ first last => exact .unionElim first last
  | interLeft a b => exact .interLeft a b
  | interRight a b => exact .interRight a b
  | interIntro _ _ first last => exact .interIntro first last
  | pair _ _ first last => exact .pair first last
  | variant _ payload => exact .variant payload
  | arrow _ inputRow _ outputRow input output => exact .arrow input inputRow output outputRow
  | record sourceShape targetShape fields _ fieldSubtypes =>
      exact .record sourceShape targetShape fields fieldSubtypes

/-- Every decision-38 congruence derivation remains valid, including all
comparisons with arbitrary raw record tails. -/
theorem semantic_subtype {a b : Ty Row} (old : SemanticRecords.Subtype leRow a b) :
    Subtype leRow a b := by
  induction old with
  | refl a => exact .refl a
  | trans _ _ first last => exact .trans first last
  | bottom a => exact .bottom a
  | top a => exact .top a
  | unionLeft a b => exact .unionLeft a b
  | unionRight a b => exact .unionRight a b
  | unionElim _ _ first last => exact .unionElim first last
  | interLeft a b => exact .interLeft a b
  | interRight a b => exact .interRight a b
  | interIntro _ _ first last => exact .interIntro first last
  | pair _ _ first last => exact .pair first last
  | variant _ payload => exact .variant payload
  | arrow _ inputRow _ outputRow input output => exact .arrow input inputRow output outputRow
  | record sourceShape targetShape fields _ fieldSubtypes =>
      exact .record sourceShape targetShape fields fieldSubtypes

  | recordCongr _ _ _ _ headForward headBackward tailForward tailBackward =>
      exact .recordCongr headForward headBackward tailForward tailBackward

/-- Every decision-39 comparison survives, including its non-rigid tails. -/
theorem rigid_subtype {a b : Ty Row} (old : RigidSemanticRecords.Subtype leRow a b) :
    Subtype leRow a b := by
  induction old with
  | refl a => exact .refl a
  | trans _ _ first last => exact .trans first last
  | bottom a => exact .bottom a
  | top a => exact .top a
  | unionLeft a b => exact .unionLeft a b
  | unionRight a b => exact .unionRight a b
  | unionElim _ _ first last => exact .unionElim first last
  | interLeft a b => exact .interLeft a b
  | interRight a b => exact .interRight a b
  | interIntro _ _ first last => exact .interIntro first last
  | pair _ _ first last => exact .pair first last
  | variant _ payload => exact .variant payload
  | arrow _ inputRow _ outputRow input output => exact .arrow input inputRow output outputRow
  | record sourceShape targetShape fields _ fieldSubtypes =>
      exact .record sourceShape targetShape fields fieldSubtypes
  | recordCongr _ _ _ _ headForward headBackward tailForward tailBackward =>
      exact .recordCongr headForward headBackward tailForward tailBackward
  | recordTail shape _ tail => exact .recordTail shape tail

/-- Closure requirements for precisely the decision-40 extension. The new
covariance field still requires a rigid demanded tail. -/
structure Closed (leRow : Row → Row → Prop) (relation : Ty Row → Ty Row → Prop) : Prop where
  old : ∀ {a b}, StructuralBase.Subtype leRow a b → relation a b
  trans : ∀ {a b c}, relation a b → relation b c → relation a c
  unionElim : ∀ {a b c}, relation a c → relation b c → relation (.union a b) c
  interIntro : ∀ {a b c}, relation c a → relation c b → relation c (.inter a b)
  pair : ∀ {a a' b b'}, relation a a' → relation b b' → relation (.pair a b) (.pair a' b')
  variant : ∀ {label a b}, relation a b → relation (.variant label a) (.variant label b)
  arrow : ∀ {input input' output output' inputRow inputRow' outputRow outputRow'},
    relation input' input → leRow inputRow' inputRow →
    relation output output' → leRow outputRow outputRow' →
    relation (.arrow input inputRow output outputRow) (.arrow input' inputRow' output' outputRow')
  record : ∀ {source target}, IsRecord source → IsRecord target →
    (∀ label value, target.lookup label = some value → ∃ actual, source.lookup label = some actual) →
    (∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected → relation actual expected) → relation source target
  recordCongr : ∀ {label value value' rest rest'},
    relation value value' → relation value' value → relation rest rest' → relation rest' rest →
    relation (.record label value rest) (.record label value' rest')
  recordTail : ∀ {label value rest rest'}, IsRecord rest' → relation rest rest' →
    relation (.record label value rest) (.record label value rest')
  shadowErase : ∀ label visible hidden rest,
    relation (.record label visible (.record label hidden rest)) (.record label visible rest)
  shadowInsert : ∀ label visible hidden rest,
    relation (.record label visible rest) (.record label visible (.record label hidden rest))

theorem subtype_closed : Closed leRow (Subtype leRow) where
  old := old_subtype
  trans := .trans
  unionElim := .unionElim
  interIntro := .interIntro
  pair := .pair
  variant := .variant
  arrow := .arrow
  record := .record
  recordCongr := .recordCongr
  recordTail := .recordTail
  shadowErase := .shadowErase
  shadowInsert := .shadowInsert

/-- This relation is the least extension with the stated closure properties.
In particular, defining it introduces no additional constructor equations. -/
theorem Subtype.minimal {relation : Ty Row → Ty Row → Prop} (closed : Closed leRow relation)
    {a b : Ty Row} (below : Subtype leRow a b) : relation a b := by
  induction below with
  | refl a => exact closed.old (.refl a)
  | trans _ _ first last => exact closed.trans first last
  | bottom a => exact closed.old (.bottom a)
  | top a => exact closed.old (.top a)
  | unionLeft a b => exact closed.old (.unionLeft a b)
  | unionRight a b => exact closed.old (.unionRight a b)
  | unionElim _ _ first last => exact closed.unionElim first last
  | interLeft a b => exact closed.old (.interLeft a b)
  | interRight a b => exact closed.old (.interRight a b)
  | interIntro _ _ first last => exact closed.interIntro first last
  | pair _ _ first last => exact closed.pair first last
  | variant _ payload => exact closed.variant payload
  | arrow _ inputRow _ outputRow input output => exact closed.arrow input inputRow output outputRow
  | record sourceShape targetShape fields _ fieldSubtypes =>
      exact closed.record sourceShape targetShape fields fieldSubtypes
  | recordCongr _ _ _ _ headForward headBackward tailForward tailBackward =>
      exact closed.recordCongr headForward headBackward tailForward tailBackward
  | recordTail shape _ tail => exact closed.recordTail shape tail
  | shadowErase label visible hidden rest => exact closed.shadowErase label visible hidden rest
  | shadowInsert label visible hidden rest => exact closed.shadowInsert label visible hidden rest

theorem subtype_iff_all_closed (a b : Ty Row) :
    Subtype leRow a b ↔
      ∀ relation : Ty Row → Ty Row → Prop, Closed leRow relation → relation a b :=
  ⟨fun below _ closed => below.minimal closed, fun universal => universal _ subtype_closed⟩

def Equivalent (leRow : Row → Row → Prop) (a b : Ty Row) : Prop :=
  Subtype leRow a b ∧ Subtype leRow b a

theorem Equivalent.refl (a : Ty Row) : Equivalent leRow a a := ⟨.refl a, .refl a⟩

theorem Equivalent.symm {a b : Ty Row} (same : Equivalent leRow a b) :
    Equivalent leRow b a := ⟨same.2, same.1⟩

theorem Equivalent.trans {a b c : Ty Row}
    (first : Equivalent leRow a b) (last : Equivalent leRow b c) : Equivalent leRow a c :=
  ⟨.trans first.1 last.1, .trans last.2 first.2⟩

theorem old_equivalent {a b : Ty Row}
    (forward : StructuralBase.Subtype leRow a b) (backward : StructuralBase.Subtype leRow b a) :
    Equivalent leRow a b := ⟨old_subtype forward, old_subtype backward⟩

theorem union_is_join (a b c : Ty Row) :
    Subtype leRow (.union a b) c ↔ Subtype leRow a c ∧ Subtype leRow b c := by
  constructor
  · intro below
    exact ⟨.trans (.unionLeft a b) below, .trans (.unionRight a b) below⟩
  · rintro ⟨left, right⟩
    exact .unionElim left right

theorem inter_is_meet (a b c : Ty Row) :
    Subtype leRow c (.inter a b) ↔ Subtype leRow c a ∧ Subtype leRow c b := by
  constructor
  · intro below
    exact ⟨.trans below (.interLeft a b), .trans below (.interRight a b)⟩
  · rintro ⟨left, right⟩
    exact .interIntro left right

theorem union_mono {a a' b b' : Ty Row}
    (left : Subtype leRow a a') (right : Subtype leRow b b') :
    Subtype leRow (.union a b) (.union a' b') :=
  .unionElim (.trans left (.unionLeft a' b')) (.trans right (.unionRight a' b'))

theorem inter_mono {a a' b b' : Ty Row}
    (left : Subtype leRow a a') (right : Subtype leRow b b') :
    Subtype leRow (.inter a b) (.inter a' b') :=
  .interIntro (.trans (.interLeft a b) left) (.trans (.interRight a b) right)

theorem union_congr {a a' b b' : Ty Row}
    (left : Equivalent leRow a a') (right : Equivalent leRow b b') :
    Equivalent leRow (.union a b) (.union a' b') :=
  ⟨union_mono left.1 right.1, union_mono left.2 right.2⟩

theorem inter_congr {a a' b b' : Ty Row}
    (left : Equivalent leRow a a') (right : Equivalent leRow b b') :
    Equivalent leRow (.inter a b) (.inter a' b') :=
  ⟨inter_mono left.1 right.1, inter_mono left.2 right.2⟩

theorem pair_congr {a a' b b' : Ty Row}
    (left : Equivalent leRow a a') (right : Equivalent leRow b b') :
    Equivalent leRow (.pair a b) (.pair a' b') :=
  ⟨.pair left.1 right.1, .pair left.2 right.2⟩

theorem variant_congr (label : Nat) {a b : Ty Row} (same : Equivalent leRow a b) :
    Equivalent leRow (.variant label a) (.variant label b) :=
  ⟨.variant same.1, .variant same.2⟩

theorem arrow_congr {input input' output output' : Ty Row} (inputRow outputRow : Row)
    (inputRefl : leRow inputRow inputRow) (outputRefl : leRow outputRow outputRow)
    (inputEq : Equivalent leRow input input') (outputEq : Equivalent leRow output output') :
    Equivalent leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow output' outputRow) :=
  ⟨.arrow inputEq.2 inputRefl outputEq.1 outputRefl,
    .arrow inputEq.1 inputRefl outputEq.2 outputRefl⟩

/-- Head and tail are arbitrary types. In particular neither side has to
satisfy the historical syntactic `IsRecord` predicate. -/
theorem record_congr (label : Nat) {value value' rest rest' : Ty Row}
    (head : Equivalent leRow value value') (tail : Equivalent leRow rest rest') :
    Equivalent leRow (.record label value rest) (.record label value' rest') :=
  ⟨.recordCongr head.1 head.2 tail.1 tail.2, .recordCongr head.2 head.1 tail.2 tail.1⟩

theorem union_bottom_equivalent (a : Ty Row) : Equivalent leRow (.union a .bottom) a :=
  ⟨.unionElim (.refl a) (.bottom a), .unionLeft a .bottom⟩

theorem inter_top_equivalent (a : Ty Row) : Equivalent leRow (.inter a .top) a :=
  ⟨.interLeft a .top, .interIntro (.refl a) (.top a)⟩

theorem union_comm_equivalent (a b : Ty Row) :
    Equivalent leRow (.union a b) (.union b a) :=
  ⟨.unionElim (.unionRight b a) (.unionLeft b a),
    .unionElim (.unionRight a b) (.unionLeft a b)⟩

theorem inter_comm_equivalent (a b : Ty Row) :
    Equivalent leRow (.inter a b) (.inter b a) :=
  ⟨.interIntro (.interRight a b) (.interLeft a b),
    .interIntro (.interRight b a) (.interLeft b a)⟩

theorem union_idem_equivalent (a : Ty Row) : Equivalent leRow (.union a a) a :=
  ⟨.unionElim (.refl a) (.refl a), .unionLeft a a⟩

theorem inter_idem_equivalent (a : Ty Row) : Equivalent leRow (.inter a a) a :=
  ⟨.interLeft a a, .interIntro (.refl a) (.refl a)⟩

theorem record_tail_union_bottom (label : Nat) (value rest : Ty Row) :
    Equivalent leRow (.record label value (.union rest .bottom)) (.record label value rest) :=
  record_congr label (.refl value) (union_bottom_equivalent rest)

theorem record_tail_inter_top (label : Nat) (value rest : Ty Row) :
    Equivalent leRow (.record label value (.inter rest .top)) (.record label value rest) :=
  record_congr label (.refl value) (inter_top_equivalent rest)

/-- The pair separated by `RecordTailBoundary` in the old relation is now
equivalent, for every row relation and every field value. -/
theorem boundary_pair_equivalent (label : Nat) (value : Ty Row) :
    Equivalent leRow (.record label value .emptyRecord)
      (.record label value (.union .emptyRecord .bottom)) :=
  (record_tail_union_bottom label value .emptyRecord).symm

theorem boundary_raw_tail_below_empty (label : Nat) (value : Ty Row) :
    Subtype leRow (.record label value (.union .emptyRecord .bottom)) .emptyRecord :=
  .trans (record_tail_union_bottom label value .emptyRecord).1
    (old_subtype (StructuralBase.record_width_to_empty (.field .empty)))

/-- The existing variance rule still requires a rigid target. Its demanded tail is explicitly rigid. -/
theorem record_tail_covariant (label : Nat) (value : Ty Row) {rest rest' : Ty Row}
    (rigid : IsRecord rest') (below : Subtype leRow rest rest') :
    Subtype leRow (.record label value rest) (.record label value rest') :=
  .recordTail rigid below

/-- A semantically rigid demanded tail may use any equivalent spelling. This
is derived from congruence, not a covariance rule for arbitrary demanded tails. -/
theorem record_tail_semantically_rigid (label : Nat) (value : Ty Row)
    {rest rest' proper : Ty Row} (rigid : IsRecord proper)
    (same : Equivalent leRow rest' proper) (below : Subtype leRow rest rest') :
    Subtype leRow (.record label value rest) (.record label value rest') :=
  .trans (.recordTail rigid (.trans below same.1))
    (record_congr label (.refl _) same.symm).1

/-- Every admissible raw tail exposes its new head. No syntactic condition
on that tail, or row-algebra law, is required. -/
theorem record_head (label : Nat) (value : Ty Row) {rest : Ty Row}
    (admissible : Subtype leRow rest .emptyRecord) :
    Subtype leRow (.record label value rest) (.record label value .emptyRecord) :=
  .recordTail .empty admissible

/-- Every record with an admissible tail may forget all its fields. -/
theorem record_width (label : Nat) (value : Ty Row) {rest : Ty Row}
    (admissible : Subtype leRow rest .emptyRecord) :
    Subtype leRow (.record label value rest) .emptyRecord :=
  .trans (record_head label value admissible)
    (old_subtype (StructuralBase.record_width_to_empty (.field .empty)))

/-- In particular, the decision-38 minimum-relation width boundary is repaired. -/
theorem record_never_below_empty (label : Nat) (value : Ty Row) :
    Subtype leRow (.record label value .bottom) .emptyRecord :=
  record_width label value (.bottom _)

/-- Hidden fields disappear in either direction for every tail, including
`never` and opaque unions. No admissibility premise is needed. -/
theorem shadow_equivalent (label : Nat) (visible hidden rest : Ty Row) :
    Equivalent leRow (.record label visible (.record label hidden rest))
      (.record label visible rest) :=
  ⟨.shadowErase label visible hidden rest, .shadowInsert label visible hidden rest⟩

/-- Once hidden, a payload cannot affect any demanded type. -/
theorem shadow_left_iff (label : Nat) (visible hidden rest target : Ty Row) :
    Subtype leRow (.record label visible (.record label hidden rest)) target ↔
      Subtype leRow (.record label visible rest) target :=
  ⟨fun below => .trans (.shadowInsert label visible hidden rest) below,
    fun below => .trans (.shadowErase label visible hidden rest) below⟩

/-- Erasure also holds in demand position; it is genuine type equality. -/
theorem shadow_right_iff (label : Nat) (visible hidden rest source : Ty Row) :
    Subtype leRow source (.record label visible (.record label hidden rest)) ↔
      Subtype leRow source (.record label visible rest) :=
  ⟨fun below => .trans below (.shadowErase label visible hidden rest),
    fun below => .trans below (.shadowInsert label visible hidden rest)⟩

theorem hidden_payload_equivalent (label : Nat) (visible first last rest : Ty Row) :
    Equivalent leRow (.record label visible (.record label first rest))
      (.record label visible (.record label last rest)) :=
  (shadow_equivalent label visible first rest).trans
    (shadow_equivalent label visible last rest).symm

/-! ## Non-collapse

The same independent scalar observation that separates old ground types is
sound for the new relation. Record congruence cannot create a scalar value.
-/

theorem scalar_preserved {a b : Ty Row} (below : Subtype leRow a b) :
    ∀ observed, StructuralBase.Scalar observed a → StructuralBase.Scalar observed b := by
  induction below with
  | refl => exact fun _ h => h
  | trans _ _ first last => exact fun observed h => last observed (first observed h)
  | bottom => exact fun _ h => False.elim h
  | top => exact fun _ _ => trivial
  | unionLeft => exact fun _ h => Or.inl h
  | unionRight => exact fun _ h => Or.inr h
  | unionElim _ _ first last => exact fun observed h => h.elim (first observed) (last observed)
  | interLeft => exact fun _ h => h.1
  | interRight => exact fun _ h => h.2
  | interIntro _ _ first last => exact fun observed h => ⟨first observed h, last observed h⟩
  | pair => exact fun _ h => False.elim h
  | variant => exact fun _ h => False.elim h
  | arrow => exact fun _ h => False.elim h
  | record sourceShape _ _ _ _ =>
      exact fun observed h => False.elim (StructuralBase.record_not_scalar observed sourceShape h)
  | recordCongr => exact fun _ h => False.elim h
  | recordTail => exact fun _ h => False.elim h
  | shadowErase => exact fun _ h => False.elim h
  | shadowInsert => exact fun _ h => False.elim h

theorem distinct_bases_not_subtypes {left right : Base} (different : left ≠ right) :
    ¬ Subtype leRow (.base left) (.base right) := by
  intro below
  exact different ((scalar_preserved below left rfl).symm)

theorem int_not_str : ¬ Subtype leRow (.base .int) (.base .str) :=
  distinct_bases_not_subtypes (by decide)

theorem top_not_int : ¬ Subtype leRow .top (.base .int) := by
  intro below
  have impossible := scalar_preserved below .str trivial
  cases impossible

theorem top_not_bottom : ¬ Subtype leRow .top .bottom := by
  intro below
  exact scalar_preserved below .int trivial

theorem top_not_arrow (input output : Ty Row) (inputRow outputRow : Row) :
    ¬ Subtype leRow .top (.arrow input inputRow output outputRow) := by
  intro below
  exact scalar_preserved below .int trivial

/-- The original carrier and operations, with the shadow-erasure congruence relation.
No source typing rule or row interpretation is changed. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Model where
  Ty := Ty Row
  Row := Row
  base := Ty.base
  bottom := Ty.bottom
  top := Ty.top
  union := Ty.union
  inter := Ty.inter
  pair := Ty.pair
  emptyRecord := Ty.emptyRecord
  record := Ty.record
  variant := Ty.variant
  arrow := Ty.arrow
  empty := empty
  join := join
  subTy := Subtype leRow
  subRow := leRow

end Yulang.ShadowSemanticRecords
