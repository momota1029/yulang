import Yulang.StructuralCut
import Yulang.SignedStructural

/-!
# Executable ground structural subtyping

The checker searches only the finitely many immediate structural rules. It
never guesses an intermediate type for transitivity: `StructuralCut` proves
that no such guess is needed. Every recursive call reduces endpoint sizes.

The supplied row comparison is required to be exact only when proving the
generic correctness theorem. The signed-row entry point below supplies its
own executable occurrence-inclusion check, retaining all integer weights.

This decides ground subtyping in the existing reference algebra. It does not
solve unknown type bounds, recursive types, or quantified generated formulas.
-/

namespace Yulang.StructuralDecisions

open StructuralBase

variable {RowType : Type u}

deriving instance DecidableEq for Ty

def isRecord : Ty RowType → Bool
  | .emptyRecord => true
  | .record _ _ rest => isRecord rest
  | _ => false

@[simp] theorem isRecord_exact (type : Ty RowType) :
    isRecord type = true ↔ IsRecord type := by
  induction type with
  | emptyRecord => exact ⟨fun _ => .empty, fun _ => rfl⟩
  | record label value rest _ ih =>
      constructor
      · exact fun checked => .field (ih.mp checked)
      · intro shape
        cases shape with
        | field rest => exact ih.mpr rest
  | _ => constructor <;> intro impossible <;> cases impossible

/-- Repeated labels are harmless here: each is checked against its first
visible value, obtained with the existing lookup function. -/
def labels : Ty RowType → List Nat
  | .record label _ rest => label :: labels rest
  | _ => []

theorem lookup_mem_labels (type : Ty RowType) (label : Nat) (value : Ty RowType)
    (found : type.lookup label = some value) : label ∈ labels type := by
  induction type with
  | record name head tail _ ih =>
      by_cases equal : label = name
      · simp [labels, equal]
      · have inside : tail.lookup label = some value := by
          simpa only [Ty.lookup, ite_eq_right equal] using found
        exact List.mem_cons_of_mem name (ih inside)
  | _ => simp [Ty.lookup] at found

theorem mem_labels_has_lookup (type : Ty RowType) (label : Nat)
    (member : label ∈ labels type) : ∃ value, type.lookup label = some value := by
  induction type with
  | record name head tail _ ih =>
      by_cases equal : label = name
      · exact ⟨head, by simp [Ty.lookup, equal]⟩
      · have inside : label ∈ labels tail := by simpa [labels, equal] using member
        obtain ⟨value, found⟩ := ih inside
        exact ⟨value, by simpa only [Ty.lookup, ite_eq_right equal] using found⟩
  | _ => simp [labels] at member

/-- Lookup retains a size certificate as erased proof data, allowing the
recursive checker to use the field type without a partial recursive call. -/
def field (type : Ty RowType) (label : Nat) :
    Option {value : Ty RowType // nodes value < nodes type} :=
  match found : type.lookup label with
  | none => none
  | some value => some ⟨value, lookup_nodes_lt type label value found⟩

theorem field_eq_some (type : Ty RowType) (label : Nat) (value : Ty RowType)
    (found : type.lookup label = some value) :
    field type label = some ⟨value, lookup_nodes_lt type label value found⟩ := by
  unfold field
  split <;> simp_all
  rename_i other otherFound
  exact Option.some.inj (otherFound.symm.trans found)

theorem field_lookup (type : Ty RowType) (label : Nat)
    (entry : {value : Ty RowType // nodes value < nodes type})
    (found : field type label = some entry) : type.lookup label = some entry.val := by
  unfold field at found
  split at found
  · cases found
  · simp only [Option.some.injEq] at found
    cases found
    assumption

/-- A finite rule search, not a search bounded by external fuel. The equality
case also preserves the reference preorder's reflexivity on raw record spines
which are not well-formed records. -/
def check [DecidableEq RowType] (rowCheck : RowType → RowType → Bool)
    (source target : Ty RowType) : Bool :=
  decide (source = target) ||
  (match source with | .bottom => true | _ => false) ||
  (match target with | .top => true | _ => false) ||
  (match source with
    | .union left right => check rowCheck left target && check rowCheck right target
    | _ => false) ||
  (match target with
    | .inter left right => check rowCheck source left && check rowCheck source right
    | _ => false) ||
  (match target with
    | .union left right => check rowCheck source left || check rowCheck source right
    | _ => false) ||
  (match source with
    | .inter left right => check rowCheck left target || check rowCheck right target
    | _ => false) ||
  (match source, target with
    | .pair left right, .pair left' right' =>
        check rowCheck left left' && check rowCheck right right'
    | _, _ => false) ||
  (match source, target with
    | .variant label payload, .variant label' payload' =>
        decide (label = label') && check rowCheck payload payload'
    | _, _ => false) ||
  (match source, target with
    | .arrow input inputRow output outputRow, .arrow input' inputRow' output' outputRow' =>
        check rowCheck input' input && rowCheck inputRow' inputRow &&
          check rowCheck output output' && rowCheck outputRow outputRow'
    | _, _ => false) ||
  (isRecord source && isRecord target &&
    (labels target).all (fun label =>
      match field source label, field target label with
      | some actual, some expected => check rowCheck actual.val expected.val
      | _, _ => false))
termination_by nodes source + nodes target
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [nodes]
  all_goals first
    | omega
    | have sourceSmaller := actual.property
      have targetSmaller := expected.property
      omega

theorem check_complete [DecidableEq RowType]
    (rowCheck : RowType → RowType → Bool) {leRow : RowType → RowType → Prop}
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    {source target : Ty RowType} (comparison : Comparison leRow source target) :
    check rowCheck source target = true := by
  induction comparison with
  | refl => rw [check.eq_def]; simp
  | bottom => rw [check.eq_def]; simp
  | top => rw [check.eq_def]; simp
  | unionElim _ _ left right => rw [check.eq_def]; simp [left, right]
  | interIntro _ _ left right => rw [check.eq_def]; simp [left, right]
  | unionLeft _ ih => rw [check.eq_def]; simp [ih]
  | unionRight _ ih => rw [check.eq_def]; simp [ih]
  | interLeft _ ih => rw [check.eq_def]; simp [ih]
  | interRight _ ih => rw [check.eq_def]; simp [ih]
  | pair _ _ left right => rw [check.eq_def]; simp [left, right]
  | variant _ ih => rw [check.eq_def]; simp [ih]
  | arrow _ inputRow _ outputRow input output =>
      rw [check.eq_def]
      simp [input, output, (rowExact _ _).mpr inputRow, (rowExact _ _).mpr outputRow]
  | @record source target sourceShape targetShape fields _ ih =>
      have checkedFields : (labels target).all (fun label =>
          match field source label, field target label with
          | some actual, some expected => check rowCheck actual.val expected.val
          | _, _ => false) = true := by
        apply List.all_eq_true.mpr
        intro label member
        obtain ⟨expected, expectedFound⟩ := mem_labels_has_lookup target label member
        obtain ⟨actual, actualFound⟩ := fields label expected expectedFound
        simp only [field_eq_some source label actual actualFound,
          field_eq_some target label expected expectedFound,
          ih label actual expected actualFound expectedFound]
      rw [check.eq_def]
      simp only [(isRecord_exact source).mpr sourceShape,
        (isRecord_exact target).mpr targetShape, Bool.true_and, checkedFields, Bool.or_true]

theorem check_sound [DecidableEq RowType]
    (rowCheck : RowType → RowType → Bool) {leRow : RowType → RowType → Prop}
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    {source target : Ty RowType} (checked : check rowCheck source target = true) :
    Comparison leRow source target := by
  rw [check.eq_def] at checked
  simp only [Bool.or_eq_true, or_assoc] at checked
  rcases checked with equal | bottom | top | union | inter | toUnion | fromInter |
    pair | variant | arrow | record
  · have same : source = target := of_decide_eq_true equal
    subst target
    exact .refl _
  · split at bottom
    · exact .bottom _
    · cases bottom
  · split at top
    · exact .top _
    · cases top
  · split at union
    · simp only [Bool.and_eq_true] at union
      obtain ⟨left, right⟩ := union
      exact .unionElim (check_sound rowCheck rowExact left) (check_sound rowCheck rowExact right)
    · cases union
  · split at inter
    · simp only [Bool.and_eq_true] at inter
      obtain ⟨left, right⟩ := inter
      exact .interIntro (check_sound rowCheck rowExact left) (check_sound rowCheck rowExact right)
    · cases inter
  · split at toUnion
    · simp only [Bool.or_eq_true] at toUnion
      rcases toUnion with left | right
      · exact .unionLeft (check_sound rowCheck rowExact left)
      · exact .unionRight (check_sound rowCheck rowExact right)
    · cases toUnion
  · split at fromInter
    · simp only [Bool.or_eq_true] at fromInter
      rcases fromInter with left | right
      · exact .interLeft (check_sound rowCheck rowExact left)
      · exact .interRight (check_sound rowCheck rowExact right)
    · cases fromInter
  · split at pair
    · simp only [Bool.and_eq_true] at pair
      obtain ⟨left, right⟩ := pair
      exact .pair (check_sound rowCheck rowExact left) (check_sound rowCheck rowExact right)
    · cases pair
  · split at variant
    · simp only [Bool.and_eq_true] at variant
      obtain ⟨sameLabel, payload⟩ := variant
      have equal := of_decide_eq_true sameLabel
      cases equal
      exact .variant (check_sound rowCheck rowExact payload)
    · cases variant
  · split at arrow
    · simp only [Bool.and_eq_true, and_assoc] at arrow
      obtain ⟨input, inputRow, output, outputRow⟩ := arrow
      exact .arrow (check_sound rowCheck rowExact input) ((rowExact _ _).mp inputRow)
        (check_sound rowCheck rowExact output) ((rowExact _ _).mp outputRow)
    · cases arrow
  · simp only [Bool.and_eq_true, and_assoc] at record
    obtain ⟨sourceShape, targetShape, fields⟩ := record
    apply Comparison.record ((isRecord_exact source).mp sourceShape)
      ((isRecord_exact target).mp targetShape)
    · intro label expected expectedFound
      have checkedField := List.all_eq_true.mp fields label
        (lookup_mem_labels target label expected expectedFound)
      cases actualFound : field source label with
      | none => simp only [actualFound] at checkedField; contradiction
      | some actual => exact ⟨actual.val, field_lookup source label actual actualFound⟩
    · intro label actual expected actualFound expectedFound
      have checkedField := List.all_eq_true.mp fields label
        (lookup_mem_labels target label expected expectedFound)
      have accepted : check rowCheck actual expected = true := by
        simpa only [field_eq_some source label actual actualFound,
          field_eq_some target label expected expectedFound] using checkedField
      have sourceSmaller := lookup_nodes_lt source label actual actualFound
      have targetSmaller := lookup_nodes_lt target label expected expectedFound
      exact check_sound rowCheck rowExact accepted
termination_by nodes source + nodes target
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [nodes]
  all_goals omega

theorem check_exact [DecidableEq RowType]
    (rowCheck : RowType → RowType → Bool) {leRow : RowType → RowType → Prop}
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (source target : Ty RowType) :
    check rowCheck source target = true ↔ Subtype leRow source target := by
  constructor
  · exact fun accepted => (check_sound rowCheck rowExact accepted).sound
  · exact fun subtype => check_complete rowCheck rowExact
      (Comparison.complete (leRow := leRow) rowTrans subtype)

def signedRowCheck [DecidableEq Key] (left right : Directed.Row n Key) : Bool :=
  left.all (fun occurrence => decide (occurrence ∈ right))

@[simp] theorem signedRowCheck_exact [DecidableEq Key] (left right : Directed.Row n Key) :
    signedRowCheck left right = true ↔ SignedStructural.RowLe left right := by
  simp [signedRowCheck, SignedStructural.RowLe]

/-- This entry point needs no supplied subtype relation or row solver. Every
signed occurrence, including negative balances, participates in inclusion. -/
def checkSigned [DecidableEq Key] (source target : SignedStructural.Ty n Key) : Bool :=
  check signedRowCheck source target

theorem checkSigned_exact [DecidableEq Key] (source target : SignedStructural.Ty n Key) :
    checkSigned source target = true ↔ SignedStructural.Subtype source target := by
  apply check_exact signedRowCheck signedRowCheck_exact
  intro a b c first second occurrence member
  exact second occurrence (first occurrence member)

theorem checkSigned_rejects [DecidableEq Key] (source target : SignedStructural.Ty n Key) :
    checkSigned source target = false ↔ ¬ SignedStructural.Subtype source target := by
  rw [← checkSigned_exact]
  cases checkSigned source target <;> simp

def equivalentSigned [DecidableEq Key] (left right : SignedStructural.Ty n Key) : Bool :=
  checkSigned left right && checkSigned right left

theorem equivalentSigned_exact [DecidableEq Key] (left right : SignedStructural.Ty n Key) :
    equivalentSigned left right = true ↔
      SignedStructural.Subtype left right ∧ SignedStructural.Subtype right left := by
  simp only [equivalentSigned, Bool.and_eq_true, checkSigned_exact]

/-- A computable decision object, obtained from the exact Boolean checker. -/
def decideSigned [DecidableEq Key] (source target : SignedStructural.Ty n Key) :
    Decidable (SignedStructural.Subtype source target) :=
  if accepted : checkSigned source target = true then
    isTrue ((checkSigned_exact source target).mp accepted)
  else isFalse (fun subtype => accepted ((checkSigned_exact source target).mpr subtype))

end Yulang.StructuralDecisions
