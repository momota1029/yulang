import Yulang.Inference

/-!
# Transport of the original inference judgment between type models

A model map preserves the actual value/row constructors and sends subtype
proofs to subtype proofs. The original constraint language is positive, so
every satisfying assignment maps to a satisfying assignment, including all
existential witnesses. Consequently every original closed typing, including
record construction and both value-let rules, survives a model extension.

No syntactic record-shape condition is added to `Typing.record`. These are
preservation results, not a solver or a converse completeness assertion.
-/

namespace Yulang.Inference

universe u₁ v₁ u₂ v₂

structure ModelMap (source : Model.{u₁, v₁}) (target : Model.{u₂, v₂}) where
  value : source.Ty → target.Ty
  row : source.Row → target.Row
  base (name : Base) : value (source.base name) = target.base name
  bottom : value source.bottom = target.bottom
  top : value source.top = target.top
  union (left right) : value (source.union left right) = target.union (value left) (value right)
  inter (left right) : value (source.inter left right) = target.inter (value left) (value right)
  pair (left right) : value (source.pair left right) = target.pair (value left) (value right)
  emptyRecord : value source.emptyRecord = target.emptyRecord
  record (label : Nat) (head tail) :
    value (source.record label head tail) = target.record label (value head) (value tail)
  variant (label : Nat) (payload) :
    value (source.variant label payload) = target.variant label (value payload)
  arrow (input inputRow output outputRow) :
    value (source.arrow input inputRow output outputRow) =
      target.arrow (value input) (row inputRow) (value output) (row outputRow)
  empty : row source.empty = target.empty
  join (left right) : row (source.join left right) = target.join (row left) (row right)
  subtype {left right} : source.subTy left right → target.subTy (value left) (value right)
  subrow {left right} : source.subRow left right → target.subRow (row left) (row right)

namespace ModelMap

variable {source : Model.{u₁, v₁}} {target : Model.{u₂, v₂}}

def comp (map : ModelMap source target) (computation : Comp source) : Comp target :=
  (map.value computation.1, map.row computation.2)

def assignment (map : ModelMap source target) (values : α → Comp source) : α → Comp target :=
  fun index => map.comp (values index)

@[simp] theorem assignment_extend (map : ModelMap source target)
    (values : α → Comp source) (computation : Comp source) :
    map.assignment (extend values computation) = extend (map.assignment values) (map.comp computation) := by
  funext index
  cases index <;> rfl

theorem comp_le (map : ModelMap source target) {left right : Comp source}
    (bounded : Comp.le source left right) : Comp.le target (map.comp left) (map.comp right) :=
  ⟨map.subtype bounded.1, map.subrow bounded.2⟩

theorem eval_row (map : ModelMap source target) (values : α → Comp source) (term : RowTerm α) :
    map.row (term.eval source values) = term.eval target (map.assignment values) := by
  induction term with
  | var => rfl
  | empty => exact map.empty
  | join left right ihl ihr =>
      simpa only [RowTerm.eval, ihl, ihr] using
        map.join (left.eval source values) (right.eval source values)

theorem eval_value (map : ModelMap source target) (values : α → Comp source) (term : TyTerm α) :
    map.value (term.eval source values) = term.eval target (map.assignment values) := by
  induction term with
  | var => rfl
  | base name => exact map.base name
  | bottom => exact map.bottom
  | top => exact map.top
  | emptyRecord => exact map.emptyRecord
  | union left right ihl ihr =>
      simpa only [TyTerm.eval, ihl, ihr] using
        map.union (left.eval source values) (right.eval source values)
  | inter left right ihl ihr =>
      simpa only [TyTerm.eval, ihl, ihr] using
        map.inter (left.eval source values) (right.eval source values)
  | pair left right ihl ihr =>
      simpa only [TyTerm.eval, ihl, ihr] using
        map.pair (left.eval source values) (right.eval source values)
  | record label head tail ihh iht =>
      simpa only [TyTerm.eval, ihh, iht] using
        map.record label (head.eval source values) (tail.eval source values)
  | variant label payload ih =>
      simpa only [TyTerm.eval, ih] using map.variant label (payload.eval source values)
  | arrow input inputRow output outputRow ihi iho =>
      simpa only [TyTerm.eval, ihi, iho, map.eval_row] using map.arrow
        (input.eval source values) (inputRow.eval source values)
        (output.eval source values) (outputRow.eval source values)

theorem eval_comp (map : ModelMap source target) (values : α → Comp source) (term : CompTerm α) :
    map.comp (term.eval source values) = term.eval target (map.assignment values) := by
  exact Prod.ext (map.eval_value values term.ty) (map.eval_row values term.row)

/-- Every formula witness is retained, with its value and row mapped together.
The theorem quantifies over arbitrary formulas, free slots and assignments. -/
theorem formula_preserved (map : ModelMap source target) (formula : Formula α)
    (values : α → Comp source) (held : formula.Holds source values) :
    formula.Holds target (map.assignment values) := by
  induction formula with
  | top => trivial
  | bot => exact held
  | and left right ihl ihr => exact ⟨ihl values held.1, ihr values held.2⟩
  | or left right ihl ihr =>
      exact held.elim (fun proof => Or.inl (ihl values proof))
        (fun proof => Or.inr (ihr values proof))
  | tyLe left right =>
      simpa only [Formula.Holds, map.eval_value] using map.subtype held
  | rowLe left right =>
      simpa only [Formula.Holds, map.eval_row] using map.subrow held
  | existsSlot body ih =>
      obtain ⟨witness, proof⟩ := held
      exact ⟨map.comp witness, by simpa only [map.assignment_extend] using ih _ proof⟩

/-- The original generator and declarative judgment are unchanged. Every
closed expression, every result value type and every result row is covered;
there is no `RecordFree`, monomorphism or solver-success premise. -/
theorem closed_typing_preserved (map : ModelMap source target) (expression : Expr)
    (result : Comp source) (typed : Typing source [] expression result) :
    Typing target [] expression (map.comp result) := by
  have original := (principal_exact source expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) result).mpr typed
  have moved := map.formula_preserved (principal ([] : SchemeEnv Empty) expression)
    (extend Empty.elim result) original
  have emptyAssignment : map.assignment (Empty.elim : Empty → Comp source) = Empty.elim := by
    funext index
    exact Empty.elim index
  rw [map.assignment_extend, emptyAssignment] at moved
  exact (principal_exact target expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) (map.comp result)).mp moved

/-- Reflection requires exact atomic comparisons and coverage of all target
computations. In particular existential witnesses cannot escape the image. -/
theorem formula_reflected (map : ModelMap source target)
    (valueReflect : ∀ {left right}, target.subTy (map.value left) (map.value right) → source.subTy left right)
    (rowReflect : ∀ {left right}, target.subRow (map.row left) (map.row right) → source.subRow left right)
    (onto : ∀ computation : Comp target, ∃ original : Comp source, map.comp original = computation)
    (formula : Formula α) (values : α → Comp source)
    (held : formula.Holds target (map.assignment values)) : formula.Holds source values := by
  induction formula with
  | top => trivial
  | bot => exact held
  | and left right ihl ihr => exact ⟨ihl values held.1, ihr values held.2⟩
  | or left right ihl ihr =>
      exact held.elim (fun proof => Or.inl (ihl values proof))
        (fun proof => Or.inr (ihr values proof))
  | tyLe left right =>
      apply valueReflect
      simpa only [Formula.Holds, map.eval_value] using held
  | rowLe left right =>
      apply rowReflect
      simpa only [Formula.Holds, map.eval_row] using held
  | existsSlot body ih =>
      obtain ⟨witness, proof⟩ := held
      obtain ⟨original, same⟩ := onto witness
      refine ⟨original, ih (extend values original) ?_⟩
      simpa only [map.assignment_extend, same] using proof

theorem formula_exact (map : ModelMap source target)
    (valueReflect : ∀ {left right}, target.subTy (map.value left) (map.value right) → source.subTy left right)
    (rowReflect : ∀ {left right}, target.subRow (map.row left) (map.row right) → source.subRow left right)
    (onto : ∀ computation : Comp target, ∃ original : Comp source, map.comp original = computation)
    (formula : Formula α) (values : α → Comp source) :
    formula.Holds target (map.assignment values) ↔ formula.Holds source values :=
  ⟨map.formula_reflected valueReflect rowReflect onto formula values,
    map.formula_preserved formula values⟩

/-- Exactness of the original closed judgment under a surjective map that
preserves and reflects its atomic comparisons. No source syntax is excluded. -/
theorem closed_typing_exact (map : ModelMap source target)
    (valueReflect : ∀ {left right}, target.subTy (map.value left) (map.value right) → source.subTy left right)
    (rowReflect : ∀ {left right}, target.subRow (map.row left) (map.row right) → source.subRow left right)
    (onto : ∀ computation : Comp target, ∃ original : Comp source, map.comp original = computation)
    (expression : Expr) (result : Comp source) :
    Typing target [] expression (map.comp result) ↔ Typing source [] expression result := by
  constructor
  · intro typed
    have targetHeld := (principal_exact target expression ([] : SchemeEnv Empty) [] Empty.elim
      (by intro index value; simp [SchemeLookup, BindingLookup]) (map.comp result)).mpr typed
    have emptyAssignment : map.assignment (Empty.elim : Empty → Comp source) = Empty.elim := by
      funext index
      exact Empty.elim index
    have mappedHeld : (principal ([] : SchemeEnv Empty) expression).Holds target
        (map.assignment (extend Empty.elim result)) := by
      simpa only [map.assignment_extend, emptyAssignment] using targetHeld
    have original := map.formula_reflected valueReflect rowReflect onto
      (principal ([] : SchemeEnv Empty) expression) (extend Empty.elim result) mappedHeld
    exact (principal_exact source expression ([] : SchemeEnv Empty) [] Empty.elim
      (by intro index value; simp [SchemeLookup, BindingLookup]) result).mp original
  · exact map.closed_typing_preserved expression result

end ModelMap
end Yulang.Inference
