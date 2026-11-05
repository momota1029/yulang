import Yulang.StructuralBase

/-!
# Ground casts at known type boundaries

Conversions are separate from ordinary type compatibility. `Compatibility`
supplies an independently specified relation and its decision procedure; it is
not replaced by cast reachability. This module decides the additional boundary
relation: source unions require every member, arrow inputs are contravariant,
and outputs, tuple components, record fields, and variant payloads are covariant.
Nominal arguments are opaque. Only an explicit rule for the entire nominal type
can change them. A whole-rule cast from a nominal/base source may return any
ground target, including a structural type instantiated by `box 'a -> 'a`.

The ground syntax extends the effect-free fragment of `StructuralBase` with
nominal applications. It does not solve ordinary subtyping, ground polymorphic
cast declarations, choose a branch of an incompatible expected union, or give
runtime meanings/effect bounds to conversion bodies. Record lookup is first-field
wins; field conversion follows labels, not their list order. Cast search starts
only after the ordinary compatibility check fails.
Ground nominal arguments use syntax equality. Normalization of equivalent source
type spellings is an upstream obligation, not a theorem of this ground kernel.
-/

namespace Yulang.Casts

open Inference

inductive Ty where
  | base : Base → Ty
  | bottom
  | top
  | union : Ty → Ty → Ty
  | inter : Ty → Ty → Ty
  | pair : Ty → Ty → Ty
  | emptyRecord
  | record : Nat → Ty → Ty → Ty
  | variant : Nat → Ty → Ty
  | arrow : Ty → Ty → Ty
  | nominal : Nat → List Ty → Ty
  deriving Repr

mutual
  def Ty.decEq (left right : Ty) : Decidable (left = right) := by
    cases left <;> cases right <;>
      try (solve | apply isFalse; intro impossible; cases impossible)
    case base.base a b => exact decidable_of_iff (a = b) (by simp)
    case bottom.bottom => exact isTrue rfl
    case top.top => exact isTrue rfl
    case union.union a b c d =>
      have := Ty.decEq a c
      have := Ty.decEq b d
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
    case inter.inter a b c d =>
      have := Ty.decEq a c
      have := Ty.decEq b d
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
    case pair.pair a b c d =>
      have := Ty.decEq a c
      have := Ty.decEq b d
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
    case emptyRecord.emptyRecord => exact isTrue rfl
    case record.record l a r k b s =>
      have := Ty.decEq a b
      have := Ty.decEq r s
      exact decidable_of_iff (l = k ∧ a = b ∧ r = s) (by simp)
    case variant.variant l a k b =>
      have := Ty.decEq a b
      exact decidable_of_iff (l = k ∧ a = b) (by simp)
    case arrow.arrow a b c d =>
      have := Ty.decEq a c
      have := Ty.decEq b d
      exact decidable_of_iff (a = c ∧ b = d) (by simp)
    case nominal.nominal l as k bs =>
      have := argsDecEq as bs
      exact decidable_of_iff (l = k ∧ as = bs) (by simp)
  def argsDecEq (left right : List Ty) : Decidable (left = right) := by
    cases left with
    | nil => cases right <;> exact inferInstance
    | cons a rest =>
      cases right with
      | nil => exact isFalse (by intro impossible; cases impossible)
      | cons b tail =>
        have := Ty.decEq a b
        have := argsDecEq rest tail
        exact decidable_of_iff (a = b ∧ rest = tail) (by simp)
end

instance : DecidableEq Ty := Ty.decEq

/-- Nominal arguments are a single opaque leaf for structural cast traversal. -/
def Ty.size : Ty → Nat
  | .base _ | .bottom | .top | .emptyRecord | .nominal _ _ => 1
  | .union a b | .inter a b | .pair a b | .arrow a b => 1 + a.size + b.size
  | .record _ a rest => 1 + a.size + rest.size
  | .variant _ a => 1 + a.size

def Ty.isNominal : Ty → Bool
  | .base _ | .nominal _ _ => true
  | _ => false

def Ty.isRecord : Ty → Bool
  | .emptyRecord => true
  | .record _ _ rest => rest.isRecord
  | _ => false

def Ty.lookup (label : Nat) : Ty → Option Ty
  | .record current value rest => if label = current then some value else rest.lookup label
  | _ => none

theorem lookup_size {source : Ty} {label : Nat} {actual : Ty}
    (found : source.lookup label = some actual) : actual.size < source.size := by
  cases shape : source with
  | record current value rest =>
    by_cases same : label = current
    · simp [shape, Ty.lookup, same] at found
      subst actual
      simp [Ty.size]
      omega
    · have smaller := lookup_size (source := rest) (label := label) (actual := actual)
        (by simpa [shape, Ty.lookup, same] using found)
      simp [Ty.size]
      omega
  | _ => simp [shape, Ty.lookup] at found
termination_by source.size
decreasing_by simp_all [Ty.size]; omega

/-- Ordinary compatibility is supplied by a separate type layer. Ground nominal
arguments must be equal; casting them is not a compatibility rule. -/
structure Compatibility where
  Rel : Ty → Ty → Prop
  check : Ty → Ty → Bool
  exact : ∀ source target, check source target = true ↔ Rel source target
  refl : ∀ type, Rel type type
  nominalInvariant : ∀ name args otherName otherArgs,
    Rel (.nominal name args) (.nominal otherName otherArgs) →
      name = otherName ∧ args = otherArgs

/-- Equality is an executable instance, not a claim to solve structural subtyping. -/
def equalityCompatibility : Compatibility where
  Rel := Eq
  check := fun source target => decide (source = target)
  exact := by intro source target; simp
  refl := fun _ => rfl
  nominalInvariant := by intro name args otherName otherArgs equal; cases equal; exact ⟨rfl, rfl⟩

structure ExplicitCasts where
  Rel : Ty → Ty → Prop
  check : Ty → Ty → Bool
  exact : ∀ source target, check source target = true ↔ Rel source target

mutual
  /-- Declarative boundary judgement, independent of the executable checker. -/
  inductive Boundary (fits explicit : Ty → Ty → Prop) : Ty → Ty → Prop where
    | keep : fits source target → Boundary fits explicit source target
    | convert : ¬ fits source target → Conversion fits explicit source target →
        Boundary fits explicit source target

  inductive Conversion (fits explicit : Ty → Ty → Prop) : Ty → Ty → Prop where
    | named : source.isNominal = true → explicit source target →
        Conversion fits explicit source target
    | union : Boundary fits explicit left target → Boundary fits explicit right target →
        Conversion fits explicit (.union left right) target
    | pair : Boundary fits explicit first first' → Boundary fits explicit second second' →
        Conversion fits explicit (.pair first second) (.pair first' second')
    | arrow : Boundary fits explicit input' input → Boundary fits explicit output output' →
        Conversion fits explicit (.arrow input output) (.arrow input' output')
    | variant : Boundary fits explicit payload payload' →
        Conversion fits explicit (.variant label payload) (.variant label payload')
    | record : source.isRecord = true → Fields fits explicit [] source target →
        Conversion fits explicit source target

  /-- Earlier target fields shadow later occurrences of the same label. -/
  inductive Fields (fits explicit : Ty → Ty → Prop) : List Nat → Ty → Ty → Prop where
    | empty : Fields fits explicit seen source .emptyRecord
    | shadow : label ∈ seen → Fields fits explicit seen source rest →
        Fields fits explicit seen source (.record label expected rest)
    | field : label ∉ seen → source.lookup label = some actual →
        Boundary fits explicit actual expected → Fields fits explicit (label :: seen) source rest →
        Fields fits explicit seen source (.record label expected rest)
end

mutual
  def accepts (fits explicit : Ty → Ty → Bool) (source target : Ty) : Bool :=
    if fits source target then true else converts fits explicit source target
  termination_by 3 * (source.size + target.size) + 2
  decreasing_by omega

  def converts (fits explicit : Ty → Ty → Bool) (source target : Ty) : Bool :=
    match source with
    | .base _ | .nominal _ _ => explicit source target
    | .union left right => accepts fits explicit left target && accepts fits explicit right target
    | .pair first second =>
      match target with
      | .pair first' second' => accepts fits explicit first first' && accepts fits explicit second second'
      | _ => false
    | .arrow input output =>
      match target with
      | .arrow input' output' => accepts fits explicit input' input && accepts fits explicit output output'
      | _ => false
    | .variant label payload =>
      match target with
      | .variant other payload' => decide (label = other) && accepts fits explicit payload payload'
      | _ => false
    | .emptyRecord => fields fits explicit [] .emptyRecord target
    | .record label value rest =>
      rest.isRecord && fields fits explicit [] (.record label value rest) target
    | .bottom | .top | .inter _ _ => false
  termination_by 3 * (source.size + target.size) + 1
  decreasing_by all_goals simp_all only [Ty.size] <;> omega

  def fields (fits explicit : Ty → Ty → Bool) (seen : List Nat) (source target : Ty) : Bool :=
    match target with
    | .emptyRecord => true
    | .record label expected rest =>
      if label ∈ seen then fields fits explicit seen source rest
      else
        match _found : source.lookup label with
        | none => false
        | some actual =>
          accepts fits explicit actual expected && fields fits explicit (label :: seen) source rest
    | _ => false
  termination_by 3 * (source.size + target.size)
  decreasing_by
    all_goals try have smaller := lookup_size _found
    all_goals simp_all [Ty.size] <;> omega
end

mutual
  theorem accepts_sound (fits : Compatibility) (explicit : ExplicitCasts)
      (source target : Ty)
      (checked : accepts fits.check explicit.check source target = true) :
      Boundary fits.Rel explicit.Rel source target := by
    by_cases compatible : fits.check source target = true
    · exact .keep ((fits.exact source target).mp compatible)
    · apply Boundary.convert (fun related => compatible ((fits.exact source target).mpr related))
      apply converts_sound fits explicit source target
      simpa [accepts, compatible] using checked
  termination_by 3 * (source.size + target.size) + 2
  decreasing_by omega

  theorem converts_sound (fits : Compatibility) (explicit : ExplicitCasts)
      (source target : Ty)
      (checked : converts fits.check explicit.check source target = true) :
      Conversion fits.Rel explicit.Rel source target := by
    cases sourceShape : source with
    | base base =>
      exact .named rfl ((explicit.exact _ _).mp (by simpa [converts, sourceShape] using checked))
    | nominal name args =>
      exact .named rfl ((explicit.exact _ _).mp (by simpa [converts, sourceShape] using checked))
    | union left right =>
      have parts : accepts fits.check explicit.check left target = true ∧
          accepts fits.check explicit.check right target = true := by
        simpa [converts, sourceShape] using checked
      exact .union (accepts_sound fits explicit left target parts.1)
        (accepts_sound fits explicit right target parts.2)
    | pair first second =>
      cases targetShape : target with
      | pair first' second' =>
        have parts : accepts fits.check explicit.check first first' = true ∧
            accepts fits.check explicit.check second second' = true := by
          simpa [converts, sourceShape, targetShape] using checked
        exact .pair (accepts_sound fits explicit first first' parts.1)
          (accepts_sound fits explicit second second' parts.2)
      | _ => simp [converts, sourceShape, targetShape] at checked
    | arrow input output =>
      cases targetShape : target with
      | arrow input' output' =>
        have parts : accepts fits.check explicit.check input' input = true ∧
            accepts fits.check explicit.check output output' = true := by
          simpa [converts, sourceShape, targetShape] using checked
        exact .arrow (accepts_sound fits explicit input' input parts.1)
          (accepts_sound fits explicit output output' parts.2)
      | _ => simp [converts, sourceShape, targetShape] at checked
    | variant label payload =>
      cases targetShape : target with
      | variant other payload' =>
        have parts : label = other ∧ accepts fits.check explicit.check payload payload' = true := by
          simpa [converts, sourceShape, targetShape] using checked
        cases parts.1
        exact .variant (accepts_sound fits explicit payload payload' parts.2)
      | _ => simp [converts, sourceShape, targetShape] at checked
    | emptyRecord =>
      exact .record rfl (fields_sound fits explicit [] .emptyRecord target
        (by simpa [converts, sourceShape] using checked))
    | record label value rest =>
      have parts : rest.isRecord = true ∧
          fields fits.check explicit.check [] (.record label value rest) target = true := by
        simpa [converts, sourceShape] using checked
      exact .record parts.1 (fields_sound fits explicit [] (.record label value rest) target parts.2)
    | bottom | top | inter _ _ => simp [converts, sourceShape] at checked
  termination_by 3 * (source.size + target.size) + 1
  decreasing_by
    all_goals try rw [sourceShape]
    all_goals try rw [targetShape]
    all_goals try simp only [Ty.size]
    all_goals omega

  theorem fields_sound (fits : Compatibility) (explicit : ExplicitCasts)
      (seen : List Nat) (source target : Ty)
      (checked : fields fits.check explicit.check seen source target = true) :
      Fields fits.Rel explicit.Rel seen source target := by
    cases targetShape : target with
    | emptyRecord => exact .empty
    | record label expected rest =>
      by_cases shadowed : label ∈ seen
      · exact .shadow shadowed (fields_sound fits explicit seen source rest
          (by simpa [fields, targetShape, shadowed] using checked))
      · simp only [fields, targetShape, ite_eq_right shadowed] at checked
        split at checked
        · contradiction
        · rename_i actual found
          have parts : accepts fits.check explicit.check actual expected = true ∧
              fields fits.check explicit.check (label :: seen) source rest = true := by
            simpa using checked
          have smaller := lookup_size found
          exact .field shadowed found (accepts_sound fits explicit actual expected parts.1)
            (fields_sound fits explicit (label :: seen) source rest parts.2)
    | _ => simp [fields, targetShape] at checked
  termination_by 3 * (source.size + target.size)
  decreasing_by
    all_goals try rw [targetShape]
    all_goals try simp only [Ty.size]
    all_goals omega
end

private theorem completeness (fits : Compatibility) (explicit : ExplicitCasts) :
    (∀ source target, Boundary fits.Rel explicit.Rel source target →
      accepts fits.check explicit.check source target = true) ∧
    (∀ source target, Conversion fits.Rel explicit.Rel source target →
      converts fits.check explicit.check source target = true) ∧
    (∀ seen source target, Fields fits.Rel explicit.Rel seen source target →
      fields fits.check explicit.check seen source target = true) := by
  let P := fun source target (_ : Boundary fits.Rel explicit.Rel source target) =>
    accepts fits.check explicit.check source target = true
  let Q := fun source target (_ : Conversion fits.Rel explicit.Rel source target) =>
    converts fits.check explicit.check source target = true
  let R := fun seen source target (_ : Fields fits.Rel explicit.Rel seen source target) =>
    fields fits.check explicit.check seen source target = true
  have keepCase : ∀ {source target}, fits.Rel source target →
      accepts fits.check explicit.check source target = true := by
    intro source target related
    simp [accepts, (fits.exact _ _).mpr related]
  have convertCase : ∀ {source target}, ¬ fits.Rel source target →
      Conversion fits.Rel explicit.Rel source target →
      converts fits.check explicit.check source target = true →
      accepts fits.check explicit.check source target = true := by
    intro source target incompatible _ checked
    have mismatch : fits.check source target ≠ true :=
      fun h => incompatible ((fits.exact _ _).mp h)
    simpa [accepts, mismatch] using checked
  have namedCase : ∀ {source target}, source.isNominal = true →
      explicit.Rel source target → converts fits.check explicit.check source target = true := by
    intro source target sourceNominal registered
    have checked := (explicit.exact _ _).mpr registered
    cases source <;> simp_all [Ty.isNominal, converts]
  have unionCase : ∀ {left target right}, Boundary fits.Rel explicit.Rel left target →
      Boundary fits.Rel explicit.Rel right target →
      accepts fits.check explicit.check left target = true →
      accepts fits.check explicit.check right target = true →
      converts fits.check explicit.check (.union left right) target = true := by
    intro left target right _ _ first second
    simp [converts, first, second]
  have pairCase : ∀ {first first' second second'}, Boundary fits.Rel explicit.Rel first first' →
      Boundary fits.Rel explicit.Rel second second' →
      accepts fits.check explicit.check first first' = true →
      accepts fits.check explicit.check second second' = true →
      converts fits.check explicit.check (.pair first second) (.pair first' second') = true := by
    intro first first' second second' _ _ left right
    simp [converts, left, right]
  have arrowCase : ∀ {input' input output output'}, Boundary fits.Rel explicit.Rel input' input →
      Boundary fits.Rel explicit.Rel output output' →
      accepts fits.check explicit.check input' input = true →
      accepts fits.check explicit.check output output' = true →
      converts fits.check explicit.check (.arrow input output) (.arrow input' output') = true := by
    intro input' input output output' _ _ left right
    simp [converts, left, right]
  have variantCase : ∀ {payload payload' label}, Boundary fits.Rel explicit.Rel payload payload' →
      accepts fits.check explicit.check payload payload' = true →
      converts fits.check explicit.check (.variant label payload) (.variant label payload') = true := by
    intro payload payload' label _ checked
    simp [converts, checked]
  have recordCase : ∀ {source target}, source.isRecord = true →
      Fields fits.Rel explicit.Rel [] source target →
      fields fits.check explicit.check [] source target = true →
      converts fits.check explicit.check source target = true := by
    intro source target recordShape _ checked
    cases source <;> simp_all [Ty.isRecord, converts]
  have emptyCase : ∀ {seen source}, fields fits.check explicit.check seen source .emptyRecord = true := by
    intro seen source
    simp [fields]
  have shadowCase : ∀ {seen label source rest expected}, label ∈ seen →
      Fields fits.Rel explicit.Rel seen source rest →
      fields fits.check explicit.check seen source rest = true →
      fields fits.check explicit.check seen source (.record label expected rest) = true := by
    intro seen label source rest expected shadowed _ checked
    simp [fields, shadowed, checked]
  have fieldCase : ∀ {seen label actual expected source rest}, label ∉ seen →
      source.lookup label = some actual → Boundary fits.Rel explicit.Rel actual expected →
      Fields fits.Rel explicit.Rel (label :: seen) source rest →
      accepts fits.check explicit.check actual expected = true →
      fields fits.check explicit.check (label :: seen) source rest = true →
      fields fits.check explicit.check seen source (.record label expected rest) = true := by
    intro seen label actual expected source rest unshadowed found _ _ headChecked tailChecked
    simp only [fields, ite_eq_right unshadowed]
    split
    · rename_i missing
      have impossible := found.symm.trans missing
      cases impossible
    · rename_i other otherFound
      have same := Option.some.inj (otherFound.symm.trans found)
      cases same
      simp [headChecked, tailChecked]
  exact ⟨fun _ _ typed => Boundary.rec (motive_1 := P) (motive_2 := Q) (motive_3 := R)
      keepCase convertCase namedCase unionCase pairCase arrowCase variantCase recordCase
      emptyCase shadowCase fieldCase typed,
    fun _ _ typed => Conversion.rec (motive_1 := P) (motive_2 := Q) (motive_3 := R)
      keepCase convertCase namedCase unionCase pairCase arrowCase variantCase recordCase
      emptyCase shadowCase fieldCase typed,
    fun _ _ _ typed => Fields.rec (motive_1 := P) (motive_2 := Q) (motive_3 := R)
      keepCase convertCase namedCase unionCase pairCase arrowCase variantCase recordCase
      emptyCase shadowCase fieldCase typed⟩

theorem accepts_complete (fits : Compatibility) (explicit : ExplicitCasts)
    {source target : Ty} (typed : Boundary fits.Rel explicit.Rel source target) :
    accepts fits.check explicit.check source target = true :=
  (completeness fits explicit).1 source target typed

theorem converts_complete (fits : Compatibility) (explicit : ExplicitCasts)
    {source target : Ty} (typed : Conversion fits.Rel explicit.Rel source target) :
    converts fits.check explicit.check source target = true :=
  (completeness fits explicit).2.1 source target typed

theorem fields_complete (fits : Compatibility) (explicit : ExplicitCasts)
    {seen : List Nat} {source target : Ty} (typed : Fields fits.Rel explicit.Rel seen source target) :
    fields fits.check explicit.check seen source target = true :=
  (completeness fits explicit).2.2 seen source target typed

/-- Exact acceptance against the independent boundary judgement. No solver
success, depth limit, or unchecked conversion oracle is assumed. -/
theorem accepts_exact (fits : Compatibility) (explicit : ExplicitCasts) (source target : Ty) :
    accepts fits.check explicit.check source target = true ↔
      Boundary fits.Rel explicit.Rel source target :=
  ⟨accepts_sound fits explicit source target, accepts_complete fits explicit⟩

theorem converts_exact (fits : Compatibility) (explicit : ExplicitCasts) (source target : Ty) :
    converts fits.check explicit.check source target = true ↔
      Conversion fits.Rel explicit.Rel source target :=
  ⟨converts_sound fits explicit source target, converts_complete fits explicit⟩

theorem fields_exact (fits : Compatibility) (explicit : ExplicitCasts)
    (seen : List Nat) (source target : Ty) :
    fields fits.check explicit.check seen source target = true ↔
      Fields fits.Rel explicit.Rel seen source target :=
  ⟨fields_sound fits explicit seen source target, fields_complete fits explicit⟩

/-- A union conversion cannot silently discard a source member. Ordinary
compatibility is deliberately excluded by the explicit mismatch premise. -/
theorem union_mismatch_iff (fits : Compatibility) (explicit : ExplicitCasts)
    (left right target : Ty) (mismatch : ¬ fits.Rel (.union left right) target) :
    Boundary fits.Rel explicit.Rel (.union left right) target ↔
      Boundary fits.Rel explicit.Rel left target ∧ Boundary fits.Rel explicit.Rel right target := by
  constructor
  · intro typed
    cases typed with
    | keep matching => exact False.elim (mismatch matching)
    | convert _ conversion =>
      cases conversion with
      | named sourceNominal _ => simp [Ty.isNominal] at sourceNominal
      | union first second => exact ⟨first, second⟩
      | record sourceRecord _ => simp [Ty.isRecord] at sourceRecord
  · rintro ⟨first, second⟩
    exact .convert mismatch (.union first second)

/-- The unconditional union law additionally requires ordinary compatibility
to respect union elimination; arbitrary compatibility decisions need not do so. -/
theorem union_boundary_iff (fits : Compatibility) (explicit : ExplicitCasts)
    (left right target : Ty)
    (compatibilityEliminates : fits.Rel (.union left right) target →
      fits.Rel left target ∧ fits.Rel right target) :
    Boundary fits.Rel explicit.Rel (.union left right) target ↔
      Boundary fits.Rel explicit.Rel left target ∧ Boundary fits.Rel explicit.Rel right target := by
  by_cases matching : fits.check (.union left right) target = true
  · have related := (fits.exact _ _).mp matching
    have parts := compatibilityEliminates related
    exact ⟨fun _ => ⟨.keep parts.1, .keep parts.2⟩, fun _ => .keep related⟩
  · exact union_mismatch_iff fits explicit left right target
      (fun related => matching ((fits.exact _ _).mpr related))

/-- Whole nominal conversions may return an arbitrary instantiated ground type.
The source remains nominal; the source-union rule still checks every member. -/
theorem nominal_mismatch_iff (fits : Compatibility) (explicit : ExplicitCasts)
    (name : Nat) (args : List Ty) (target : Ty)
    (mismatch : ¬ fits.Rel (.nominal name args) target) :
    Boundary fits.Rel explicit.Rel (.nominal name args) target ↔
      explicit.Rel (.nominal name args) target := by
  constructor
  · intro typed
    cases typed with
    | keep matching => exact False.elim (mismatch matching)
    | convert _ conversion =>
      cases conversion with
      | named _ registered => exact registered
      | record sourceRecord _ => simp [Ty.isRecord] at sourceRecord
  · intro registered
    exact .convert mismatch (.named rfl registered)

/-- Changing a fixed nominal argument requires a rule/path for the entire
outer application. Rules for its argument types alone cannot derive this. -/
theorem nominal_arguments_need_outer_rule (fits : Compatibility) (explicit : ExplicitCasts)
    (name otherName : Nat) (args otherArgs : List Ty) (different : args ≠ otherArgs) :
    Boundary fits.Rel explicit.Rel (.nominal name args) (.nominal otherName otherArgs) ↔
      explicit.Rel (.nominal name args) (.nominal otherName otherArgs) := by
  have mismatch : ¬ fits.Rel (.nominal name args) (.nominal otherName otherArgs) :=
    fun matching => different ((fits.nominalInvariant _ _ _ _ matching).2)
  exact nominal_mismatch_iff fits explicit name args _ mismatch

/-! ## Explicit syntax bridge to the existing effect-free structural carrier -/

def Ty.ofStructural : StructuralBase.Ty Unit → Ty
  | .base atom => .base atom
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (.ofStructural left) (.ofStructural right)
  | .inter left right => .inter (.ofStructural left) (.ofStructural right)
  | .pair first second => .pair (.ofStructural first) (.ofStructural second)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (.ofStructural value) (.ofStructural rest)
  | .variant label payload => .variant label (.ofStructural payload)
  | .arrow input _ output _ => .arrow (.ofStructural input) (.ofStructural output)

def Ty.toStructural : Ty → Option (StructuralBase.Ty Unit)
  | .base atom => some (.base atom)
  | .bottom => some .bottom
  | .top => some .top
  | .union left right => do return .union (← left.toStructural) (← right.toStructural)
  | .inter left right => do return .inter (← left.toStructural) (← right.toStructural)
  | .pair first second => do return .pair (← first.toStructural) (← second.toStructural)
  | .emptyRecord => some .emptyRecord
  | .record label value rest => do return .record label (← value.toStructural) (← rest.toStructural)
  | .variant label payload => do return .variant label (← payload.toStructural)
  | .arrow input output => do return .arrow (← input.toStructural) () (← output.toStructural) ()
  | .nominal _ _ => none

theorem Ty.toStructural_ofStructural (type : StructuralBase.Ty Unit) :
    (Ty.ofStructural type).toStructural = some type := by
  induction type <;> simp_all [Ty.ofStructural, Ty.toStructural]

theorem Ty.ofStructural_injective : Function.Injective Ty.ofStructural := by
  intro left right same
  have reflected := congrArg Ty.toStructural same
  simpa [Ty.toStructural_ofStructural] using reflected

/-- Agreement is an explicit obligation of a future ordinary-subtyping checker,
not an assertion that this module implements such a checker. -/
def Compatibility.StructuralAgreement (fits : Compatibility) : Prop :=
  ∀ source target : StructuralBase.Ty Unit,
    fits.Rel (Ty.ofStructural source) (Ty.ofStructural target) ↔
      StructuralBase.Subtype (fun _ _ : Unit => True) source target

theorem structural_union_boundary_iff (fits : Compatibility) (explicit : ExplicitCasts)
    (agrees : fits.StructuralAgreement) (left right target : StructuralBase.Ty Unit) :
    Boundary fits.Rel explicit.Rel (.union (Ty.ofStructural left) (Ty.ofStructural right))
        (Ty.ofStructural target) ↔
      Boundary fits.Rel explicit.Rel (Ty.ofStructural left) (Ty.ofStructural target) ∧
        Boundary fits.Rel explicit.Rel (Ty.ofStructural right) (Ty.ofStructural target) := by
  apply union_boundary_iff
  intro compatible
  have structural := (agrees (.union left right) target).mp compatible
  have parts := (StructuralBase.union_is_join left right target).mp structural
  exact ⟨(agrees left target).mpr parts.1, (agrees right target).mpr parts.2⟩

end Yulang.Casts
