import Yulang.ValueBoundElimination

/-!
# Variance-directed simplification of free value parameters

The input is the existing `TyTerm (Fin n)` syntax. Rows are fixed independently
of its value parameters. Each parameter's positive and negative occurrences are
computed through arrow variance. Parameters used only positively become `never`,
those used only negatively become `any`, and shared mixed parameters remain the
same variable. Record tails have the existing fixed record-spine restriction.

The main theorem compares all upward instances of the original and simplified
terms. It does not assume distributivity or identify different occurrences of a
mixed parameter independently. Row variables are preserved by the substitution.
-/

namespace Yulang.TypeSimplification

open Inference StructuralBase

variable {RowType : Type u} {n : Nat}

/-- `true` observes positive positions; `false` observes negative positions.
Rows are independent of value parameters and are not visited. -/
def occurs (positive : Bool) (index : Fin n) : TyTerm (Fin n) → Bool
  | .var actual => positive && decide (index = actual)
  | .base _ | .bottom | .top | .emptyRecord => false
  | .union left right | .inter left right | .pair left right | .record _ left right =>
      occurs positive index left || occurs positive index right
  | .variant _ payload => occurs positive index payload
  | .arrow input _ output _ =>
      occurs (!positive) index input || occurs positive index output

/-- Unknowns may occur inside record field values, but not as a record tail. -/
def supported : TyTerm (Fin n) → Bool
  | .var _ | .base _ | .bottom | .top | .emptyRecord => true
  | .union left right | .inter left right | .pair left right =>
      supported left && supported right
  | .record _ value rest =>
      ValueBoundElimination.recordSpine rest && supported value && supported rest
  | .variant _ payload => supported payload
  | .arrow input _ output _ => supported input && supported output

def environment (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (value : ValueBounds.Valuation n RowType) : Fin n → Comp (model RowType empty join leRow) :=
  fun index => (value index, rows index)

def evaluate (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (value : ValueBounds.Valuation n RowType) : Ty RowType :=
  term.eval (model RowType empty join leRow) (environment empty join leRow rows value)

theorem row_eval_independent (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : RowTerm (Fin n)) (left right : ValueBounds.Valuation n RowType) :
    term.eval (model RowType empty join leRow) (environment empty join leRow rows left) =
      term.eval (model RowType empty join leRow) (environment empty join leRow rows right) := by
  induction term with
  | var => rfl
  | empty => rfl
  | join a b iha ihb => simp only [RowTerm.eval, iha, ihb]

theorem evaluate_recordSpine (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (value : ValueBounds.Valuation n RowType)
    (shape : ValueBoundElimination.recordSpine term = true) :
    IsRecord (evaluate empty join leRow rows term value) := by
  induction term with
  | emptyRecord => exact .empty
  | record label head rest _ ih => exact .field (ih shape)
  | _ => cases shape

/-- Every variable is compared in each polarity in which it actually occurs.
The two requirements coincide with equivalence for mixed parameters. -/
theorem evaluate_ordered (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (shape : supported term = true)
    (left right : ValueBounds.Valuation n RowType)
    (positive : ∀ index, occurs true index term = true → Subtype leRow (left index) (right index))
    (negative : ∀ index, occurs false index term = true → Subtype leRow (right index) (left index)) :
    Subtype leRow (evaluate empty join leRow rows term left)
      (evaluate empty join leRow rows term right) := by
  induction term generalizing left right with
  | var index => exact positive index (by simp [occurs])
  | base | bottom | top | emptyRecord => exact .refl _
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb =>
      have shapes : supported a = true ∧ supported b = true := by
        simpa only [supported, Bool.and_eq_true] using shape
      have first := iha shapes.1 left right
        (fun i hi => positive i (by simp [occurs, hi]))
        (fun i hi => negative i (by simp [occurs, hi]))
      have last := ihb shapes.2 left right
        (fun i hi => positive i (by simp [occurs, hi]))
        (fun i hi => negative i (by simp [occurs, hi]))
      first | exact union_mono first last | exact inter_mono first last | exact .pair first last
  | variant label payload ih =>
      exact .variant (ih shape left right positive negative)
  | record label head rest ihh ihr =>
      have shapes : (ValueBoundElimination.recordSpine rest = true ∧ supported head = true) ∧
          supported rest = true := by
        simpa only [supported, Bool.and_eq_true] using shape
      have first := ihh shapes.1.2 left right
        (fun i hi => positive i (by simp [occurs, hi]))
        (fun i hi => negative i (by simp [occurs, hi]))
      have last := ihr shapes.2 left right
        (fun i hi => positive i (by simp [occurs, hi]))
        (fun i hi => negative i (by simp [occurs, hi]))
      exact ValueBoundElimination.record_cons_mono (leRow := leRow) rowTrans label
        (evaluate_recordSpine empty join leRow rows rest left shapes.1.1)
        (evaluate_recordSpine empty join leRow rows rest right shapes.1.1) first last
  | arrow input inputRow output outputRow ihi iho =>
      have shapes : supported input = true ∧ supported output = true := by
        simpa only [supported, Bool.and_eq_true] using shape
      have inputBound := ihi shapes.1 right left
        (fun i hi => negative i (by simp [occurs, hi]))
        (fun i hi => positive i (by simp [occurs, hi]))
      have outputBound := iho shapes.2 left right
        (fun i hi => positive i (by simp [occurs, hi]))
        (fun i hi => negative i (by simp [occurs, hi]))
      have inputRows := row_eval_independent empty join leRow rows inputRow right left
      have outputRows := row_eval_independent empty join leRow rows outputRow left right
      exact .arrow inputBound (inputRows ▸ rowRefl _) outputBound (outputRows ▸ rowRefl _)

/-- Adapter for arbitrary schemes: pointwise equivalent parameter assignments
produce equivalent type values, including shared parameters of both polarities. -/
theorem evaluate_congruent (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (shape : supported term = true)
    (left right : ValueBounds.Valuation n RowType)
    (equivalent : ∀ index, Subtype leRow (left index) (right index) ∧
      Subtype leRow (right index) (left index)) :
    Subtype leRow (evaluate empty join leRow rows term left)
        (evaluate empty join leRow rows term right) ∧
      Subtype leRow (evaluate empty join leRow rows term right)
        (evaluate empty join leRow rows term left) :=
  ⟨evaluate_ordered empty join leRow rowRefl rowTrans rows term shape left right
      (fun i _ => (equivalent i).1) (fun i _ => (equivalent i).2),
    evaluate_ordered empty join leRow rowRefl rowTrans rows term shape right left
      (fun i _ => (equivalent i).2) (fun i _ => (equivalent i).1)⟩

/-- An absent parameter can also become bottom: its value is unobservable. -/
def replacement (term : TyTerm (Fin n)) (index : Fin n) : TyTerm (Fin n) :=
  if occurs false index term then
    if occurs true index term then .var index else .top
  else .bottom

/-- The row slot is preserved even when the corresponding value slot is removed. -/
def simplify (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  term.subst (fun index => ⟨replacement term index, .var index⟩)

def selected (term : TyTerm (Fin n)) (value : ValueBounds.Valuation n RowType) :
    ValueBounds.Valuation n RowType :=
  fun index =>
    if occurs false index term then
      if occurs true index term then value index else .top
    else .bottom

theorem evaluate_simplify (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (value : ValueBounds.Valuation n RowType) :
    evaluate empty join leRow rows (simplify term) value =
      evaluate empty join leRow rows term (selected term value) := by
  unfold evaluate simplify
  rw [TyTerm.eval_subst]
  congr 1
  funext index
  by_cases hn : occurs false index term = true <;>
    by_cases hp : occurs true index term = true <;>
    simp [replacement, selected, environment, CompTerm.eval, TyTerm.eval, RowTerm.eval, model, hn, hp]

theorem simplified_below (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (shape : supported term = true)
    (value : ValueBounds.Valuation n RowType) :
    Subtype leRow (evaluate empty join leRow rows (simplify term) value)
      (evaluate empty join leRow rows term value) := by
  rw [evaluate_simplify]
  apply evaluate_ordered empty join leRow rowRefl rowTrans rows term shape
  · intro index hp
    by_cases hn : occurs false index term = true
    · simpa [selected, hn, hp] using (Subtype.refl (leRow := leRow) (value index))
    · simpa [selected, hn] using (Subtype.bottom (leRow := leRow) (value index))
  · intro index hn
    by_cases hp : occurs true index term = true
    · simpa [selected, hn, hp] using (Subtype.refl (leRow := leRow) (value index))
    · simpa [selected, hn, hp] using (Subtype.top (leRow := leRow) (value index))

def Instances (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (expected : Ty RowType) : Prop :=
  ∃ value, Subtype leRow (evaluate empty join leRow rows term value) expected

/-- Equality of the complete instance sets, not just of a selected ground run. -/
theorem simplify_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (shape : supported term = true)
    (expected : Ty RowType) :
    Instances empty join leRow rows (simplify term) expected ↔
      Instances empty join leRow rows term expected := by
  constructor
  · rintro ⟨value, fits⟩
    exact ⟨selected term value, (evaluate_simplify empty join leRow rows term value) ▸ fits⟩
  · rintro ⟨value, fits⟩
    exact ⟨value, .trans (simplified_below empty join leRow rowRefl rowTrans rows term shape value) fits⟩

def simplifyChecked (term : TyTerm (Fin n)) : Option (TyTerm (Fin n)) :=
  if supported term then some (simplify term) else none

theorem simplifyChecked_some_iff (term result : TyTerm (Fin n)) :
    simplifyChecked term = some result ↔ supported term = true ∧ simplify term = result := by
  unfold simplifyChecked
  split <;> simp_all


/-! ## A checked sufficient condition for shared-parameter simplifications

This symbolic checker treats each free parameter as an arbitrary rigid type.
It proves universal subtype comparisons using lattice rules and structural
variance. A rejected comparison is only an unavailable certificate: no
completeness or type-error claim is attached to this auxiliary checker.
-/

deriving instance DecidableEq for RowTerm
deriving instance DecidableEq for TyTerm

def nodes : TyTerm (Fin n) → Nat
  | .var _ | .base _ | .bottom | .top | .emptyRecord => 1
  | .union a b | .inter a b | .pair a b | .record _ a b => 1 + nodes a + nodes b
  | .variant _ a => 1 + nodes a
  | .arrow a _ b _ => 1 + nodes a + nodes b

/-- A universal symbolic subtype certificate; constructor distribution is not
one of its rules. Record comparisons preserve the fixed record spine. -/
def symbolicCheck (source target : TyTerm (Fin n)) : Bool :=
  decide (source = target) ||
  (match source with | .bottom => true | _ => false) ||
  (match target with | .top => true | _ => false) ||
  (match source with
    | .union a b => symbolicCheck a target && symbolicCheck b target
    | _ => false) ||
  (match target with
    | .inter a b => symbolicCheck source a && symbolicCheck source b
    | _ => false) ||
  (match target with
    | .union a b => symbolicCheck source a || symbolicCheck source b
    | _ => false) ||
  (match source with
    | .inter a b => symbolicCheck a target || symbolicCheck b target
    | _ => false) ||
  (match source, target with
    | .pair a b, .pair c d => symbolicCheck a c && symbolicCheck b d
    | _, _ => false) ||
  (match source, target with
    | .variant label a, .variant label' b => decide (label = label') && symbolicCheck a b
    | _, _ => false) ||
  (match source, target with
    | .arrow a ar b br, .arrow c cr d dr =>
        decide (ar = cr) && decide (br = dr) && symbolicCheck c a && symbolicCheck b d
    | _, _ => false) ||
  (match source, target with
    | .record label a rest, .record label' b rest' =>
        decide (label = label') && ValueBoundElimination.recordSpine rest &&
          ValueBoundElimination.recordSpine rest' && symbolicCheck a b && symbolicCheck rest rest'
    | _, _ => false)
termination_by nodes source + nodes target
decreasing_by all_goals simp_wf; simp only [nodes]; omega

theorem symbolicCheck_sound (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (source target : TyTerm (Fin n))
    (checked : symbolicCheck source target = true) (value : ValueBounds.Valuation n RowType) :
    Subtype leRow (evaluate empty join leRow rows source value)
      (evaluate empty join leRow rows target value) := by
  rw [symbolicCheck.eq_def] at checked
  simp only [Bool.or_eq_true, or_assoc] at checked
  rcases checked with same | bottom | top | union | inter | toUnion | fromInter |
    pair | variant | arrow | record
  · have equal : source = target := of_decide_eq_true same
    subst target
    exact .refl _
  · split at bottom
    · exact .bottom _
    · cases bottom
  · split at top
    · exact .top _
    · cases top
  · split at union
    · obtain ⟨first, last⟩ := Bool.and_eq_true_iff.mp union
      exact .unionElim
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ first value)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ last value)
    · cases union
  · split at inter
    · obtain ⟨first, last⟩ := Bool.and_eq_true_iff.mp inter
      exact .interIntro
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ first value)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ last value)
    · cases inter
  · split at toUnion
    · rcases Bool.or_eq_true_iff.mp toUnion with first | last
      · exact .trans (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ first value)
          (.unionLeft _ _)
      · exact .trans (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ last value)
          (.unionRight _ _)
    · cases toUnion
  · split at fromInter
    · rcases Bool.or_eq_true_iff.mp fromInter with first | last
      · exact .trans (.interLeft _ _)
          (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ first value)
      · exact .trans (.interRight _ _)
          (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ last value)
    · cases fromInter
  · split at pair
    · obtain ⟨first, last⟩ := Bool.and_eq_true_iff.mp pair
      exact .pair
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ first value)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ last value)
    · cases pair
  · split at variant
    · obtain ⟨label, payload⟩ := Bool.and_eq_true_iff.mp variant
      have equal := of_decide_eq_true label
      cases equal
      exact .variant (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ payload value)
    · cases variant
  · split at arrow
    · simp only [Bool.and_eq_true, and_assoc] at arrow
      obtain ⟨inputRows, outputRows, input, output⟩ := arrow
      have sameInput := of_decide_eq_true inputRows
      have sameOutput := of_decide_eq_true outputRows
      cases sameInput
      cases sameOutput
      exact .arrow
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ input value)
        (rowRefl _)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ output value)
        (rowRefl _)
    · cases arrow
  · split at record
    · simp only [Bool.and_eq_true, and_assoc] at record
      obtain ⟨label, sourceShape, targetShape, head, tail⟩ := record
      have equal := of_decide_eq_true label
      cases equal
      exact ValueBoundElimination.record_cons_mono (leRow := leRow) rowTrans _
        (evaluate_recordSpine empty join leRow rows _ value sourceShape)
        (evaluate_recordSpine empty join leRow rows _ value targetShape)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ head value)
        (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ tail value)
    · cases record
termination_by nodes source + nodes target
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals simp only [nodes]
  all_goals omega

/-- Substitute only value parameters; even a discarded value's row slot stays. -/
def substituteValues (term : TyTerm (Fin n)) (replacement : Fin n → TyTerm (Fin n)) :
    TyTerm (Fin n) :=
  term.subst (fun index => ⟨replacement index, .var index⟩)

theorem evaluate_substituteValues (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (replacement : Fin n → TyTerm (Fin n))
    (value : ValueBounds.Valuation n RowType) :
    evaluate empty join leRow rows (substituteValues term replacement) value =
      evaluate empty join leRow rows term
        (fun index => evaluate empty join leRow rows (replacement index) value) := by
  unfold evaluate substituteValues
  rw [TyTerm.eval_subst]
  rfl

/-- Any universally narrowing value substitution preserves all upward instances:
its own instances are already diagonal instances of the original term. -/
theorem substitution_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (term : TyTerm (Fin n)) (replacement : Fin n → TyTerm (Fin n))
    (narrowing : ∀ value : ValueBounds.Valuation n RowType,
      Subtype leRow (evaluate empty join leRow rows (substituteValues term replacement) value)
        (evaluate empty join leRow rows term value)) (expected : Ty RowType) :
    Instances empty join leRow rows (substituteValues term replacement) expected ↔
      Instances empty join leRow rows term expected := by
  constructor
  · rintro ⟨value, fits⟩
    exact ⟨fun index => evaluate empty join leRow rows (replacement index) value,
      (evaluate_substituteValues empty join leRow rows term replacement value) ▸ fits⟩
  · rintro ⟨value, fits⟩
    exact ⟨value, .trans (narrowing value) fits⟩

/-- A general executable sufficient check for a sandwich substitution. The
replacement must be independent of the eliminated value parameter. -/
def sandwichCheck (index : Fin n) (fixed term : TyTerm (Fin n)) : Bool :=
  !occurs true index fixed && !occurs false index fixed &&
    symbolicCheck (substituteValues term (fun i => if i = index then fixed else .var i)) term

def sandwich (index : Fin n) (fixed term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  substituteValues term (fun i => if i = index then fixed else .var i)

theorem sandwich_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (index : Fin n) (fixed term : TyTerm (Fin n))
    (checked : sandwichCheck index fixed term = true) (expected : Ty RowType) :
    Instances empty join leRow rows (sandwich index fixed term) expected ↔
      Instances empty join leRow rows term expected := by
  have certified : symbolicCheck (sandwich index fixed term) term = true :=
    (Bool.and_eq_true_iff.mp checked).2
  exact substitution_instances_exact empty join leRow rows term _
    (symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ certified) expected

/-- Identify two parameters without modifying either row slot. -/
def merge (first second : Fin n) (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  substituteValues term (fun index => if index = first then .var second else .var index)

def identify (first second : Fin n) (value : ValueBounds.Valuation n RowType) :
    ValueBounds.Valuation n RowType :=
  fun index => if index = first then value second else value index

def jointReplacement (positive : Bool) (first second index : Fin n) : TyTerm (Fin n) :=
  if index = first ∨ index = second then
    if positive then .union (.var first) (.var second) else .inter (.var first) (.var second)
  else .var index

def jointAssignment (positive : Bool) (first second : Fin n)
    (value : ValueBounds.Valuation n RowType) : ValueBounds.Valuation n RowType :=
  fun index =>
    if index = first ∨ index = second then
      if positive then .union (value first) (value second) else .inter (value first) (value second)
    else value index

/-- Positive co-occurrence can identify both parameters at their common union;
negative co-occurrence uses their common intersection. This sufficient check
validates the resulting whole-term inequality, not an assumed merge law. -/
def mergeCheck (positive : Bool) (first second : Fin n) (term : TyTerm (Fin n)) : Bool :=
  symbolicCheck (substituteValues term (jointReplacement positive first second)) term

theorem evaluate_merge (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (first second : Fin n) (term : TyTerm (Fin n)) (value : ValueBounds.Valuation n RowType) :
    evaluate empty join leRow rows (merge first second term) value =
      evaluate empty join leRow rows term (identify first second value) := by
  rw [merge, evaluate_substituteValues]
  congr 1
  funext index
  by_cases same : index = first <;> simp [identify, same, evaluate, TyTerm.eval, environment]

theorem evaluate_joint (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rows : Fin n → RowType)
    (positive : Bool) (first second : Fin n) (term : TyTerm (Fin n))
    (value : ValueBounds.Valuation n RowType) :
    evaluate empty join leRow rows
      (substituteValues term (jointReplacement positive first second)) value =
        evaluate empty join leRow rows term (jointAssignment positive first second value) := by
  rw [evaluate_substituteValues]
  congr 1
  funext index
  by_cases member : index = first ∨ index = second <;> cases positive <;>
    simp [jointReplacement, jointAssignment, member, evaluate, TyTerm.eval, environment, model]

theorem identify_joint (positive : Bool) (first second : Fin n)
    (value : ValueBounds.Valuation n RowType) :
    identify first second (jointAssignment positive first second value) =
      jointAssignment positive first second value := by
  funext index
  by_cases same : index = first
  · subst index
    simp [identify, jointAssignment]
  · simp [identify, same]

/-- The merged parameter ranges over all types. For the difficult direction,
assign it the join/meet of the two original parameters, justified by the checked
whole-term inequality. The converse is the original term's diagonal instance. -/
theorem merge_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (positive : Bool) (first second : Fin n)
    (term : TyTerm (Fin n)) (checked : mergeCheck positive first second term = true)
    (expected : Ty RowType) :
    Instances empty join leRow rows (merge first second term) expected ↔
      Instances empty join leRow rows term expected := by
  constructor
  · rintro ⟨value, fits⟩
    exact ⟨identify first second value, (evaluate_merge empty join leRow rows first second term value) ▸ fits⟩
  · rintro ⟨value, fits⟩
    refine ⟨jointAssignment positive first second value, ?_⟩
    rw [evaluate_merge, identify_joint]
    have below := symbolicCheck_sound empty join leRow rowRefl rowTrans rows _ _ checked value
    rw [evaluate_joint] at below
    exact .trans below fits

/-- Either polarity may certify a merge. Failure leaves the decision open. -/
def mergeChecked (first second : Fin n) (term : TyTerm (Fin n)) : Option (TyTerm (Fin n)) :=
  if mergeCheck true first second term || mergeCheck false first second term then
    some (merge first second term)
  else none

theorem mergeChecked_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (first second : Fin n) (term result : TyTerm (Fin n))
    (checked : mergeChecked first second term = some result) (expected : Ty RowType) :
    Instances empty join leRow rows result expected ↔ Instances empty join leRow rows term expected := by
  unfold mergeChecked at checked
  split at checked
  · rename_i accepted
    cases checked
    rcases Bool.or_eq_true_iff.mp accepted with positive | negative
    · exact merge_instances_exact empty join leRow rowRefl rowTrans rows true first second term positive expected
    · exact merge_instances_exact empty join leRow rowRefl rowTrans rows false first second term negative expected
  · cases checked


/-! ## Finite automatic pass

Candidate discovery below enumerates the finite parameter set and the scalar
atoms already in the kernel. Every accepted step preserves all instances.
This is a terminating simplification pass, not a unique display normal form or
a claim that every possible valid merge is discovered by the certificate.
-/

def simplifySafe (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  if supported term then simplify term else term

theorem simplifySafe_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (simplifySafe term) expected ↔
      Instances empty join leRow rows term expected := by
  unfold simplifySafe
  split
  · rename_i shape
    exact simplify_instances_exact empty join leRow rowRefl rowTrans rows term shape expected
  · rfl

def applyMerge (first second : Fin n) (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  (mergeChecked first second term).getD term

theorem applyMerge_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (first second : Fin n) (term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (applyMerge first second term) expected ↔
      Instances empty join leRow rows term expected := by
  unfold applyMerge
  cases found : mergeChecked first second term with
  | none => rfl
  | some result =>
      exact mergeChecked_exact empty join leRow rowRefl rowTrans rows first second term result found expected

def mergeCandidates : List (Fin n × Fin n) → TyTerm (Fin n) → TyTerm (Fin n)
  | [], term => term
  | (first, second) :: rest, term => mergeCandidates rest (applyMerge first second term)

theorem mergeCandidates_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (pairs : List (Fin n × Fin n))
    (term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (mergeCandidates pairs term) expected ↔
      Instances empty join leRow rows term expected := by
  induction pairs generalizing term with
  | nil => rfl
  | cons pair rest ih =>
      exact (ih _).trans (applyMerge_exact empty join leRow rowRefl rowTrans rows pair.1 pair.2 term expected)

def mergeAll (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  mergeCandidates ((List.finRange n).flatMap fun first =>
    (List.finRange n).map fun second => (first, second)) term

def applySandwich (index : Fin n) (fixed term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  if sandwichCheck index fixed term then sandwich index fixed term else term

theorem applySandwich_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (index : Fin n) (fixed term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (applySandwich index fixed term) expected ↔
      Instances empty join leRow rows term expected := by
  unfold applySandwich
  split
  · rename_i accepted
    exact sandwich_instances_exact empty join leRow rowRefl rowTrans rows index fixed term accepted expected
  · rfl

def sandwichCandidates : List (Fin n × TyTerm (Fin n)) → TyTerm (Fin n) → TyTerm (Fin n)
  | [], term => term
  | (index, fixed) :: rest, term => sandwichCandidates rest (applySandwich index fixed term)

theorem sandwichCandidates_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (candidates : List (Fin n × TyTerm (Fin n)))
    (term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (sandwichCandidates candidates term) expected ↔
      Instances empty join leRow rows term expected := by
  induction candidates generalizing term with
  | nil => rfl
  | cons pair rest ih =>
      exact (ih _).trans (applySandwich_exact empty join leRow rowRefl rowTrans rows pair.1 pair.2 term expected)

def sandwichAll (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  sandwichCandidates ((List.finRange n).flatMap fun index =>
    ([.int, .str, .bool, .unit] : List Base).map fun base => (index, .base base)) term

/-- Four finite stages: single-polarity elimination, scalar sandwiches, shared
parameter merges, then single-polarity elimination exposed by those changes. -/
def simplifyAll (term : TyTerm (Fin n)) : TyTerm (Fin n) :=
  simplifySafe (mergeAll (sandwichAll (simplifySafe term)))

/-- The automatic pass preserves the complete instance set for every input.
Unsupported record tails retain their original term in the variance stage. -/
theorem simplifyAll_instances_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (term : TyTerm (Fin n)) (expected : Ty RowType) :
    Instances empty join leRow rows (simplifyAll term) expected ↔
      Instances empty join leRow rows term expected :=
  (simplifySafe_exact empty join leRow rowRefl rowTrans rows _ expected).trans
    ((mergeCandidates_exact empty join leRow rowRefl rowTrans rows _ _ expected).trans
      ((sandwichCandidates_exact empty join leRow rowRefl rowTrans rows _ _ expected).trans
        (simplifySafe_exact empty join leRow rowRefl rowTrans rows term expected)))

end Yulang.TypeSimplification
