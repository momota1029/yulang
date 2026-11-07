import Yulang.CommonBoundCoalescing

/-!
# Invariant nominal heads over arbitrary common arguments

A nominal head retains its declaration identity, the ordered argument list,
and the distinction between value and row arguments. Its independent demands
inspect the head and both directions of every argument. Value arguments range
over all of `Common.Ty`, including regular blocks and negative occurrences;
row arguments range over arbitrary occurrence sets.

This is not yet an extension of every `CommonSyntax.Layer` constructor.
Nesting a nominal head under a common arrow/record, compiling nominal regular
graphs, and preserving the full source solver are separate obligations.
-/

namespace Yulang.CommonNominalHeads

inductive Argument where
  | value : Common.Ty → Argument
  | row : Common.Row → Argument

def Argument.Le : Argument → Argument → Prop
  | .value first, .value last => Common.Subtype first last
  | .row first, .row last => Common.rowLe first last
  | _, _ => False

def Argument.Equivalent (first last : Argument) : Prop :=
  first.Le last ∧ last.Le first

theorem Argument.le_refl (argument : Argument) : argument.Le argument := by
  cases argument with
  | value type => exact Common.subtype_refl type
  | row row => exact Common.rowLe_refl row

theorem Argument.le_trans {first middle last : Argument}
    (before : first.Le middle) (after : middle.Le last) : first.Le last := by
  cases first <;> cases middle <;> cases last <;>
    simp only [Argument.Le] at before after ⊢
  all_goals first
    | exact False.elim before
    | exact False.elim after
    | exact Common.subtype_trans before after
    | exact Common.rowLe_trans before after

@[simp] theorem Argument.equivalent_value (first last : Common.Ty) :
    Argument.Equivalent (.value first) (.value last) ↔ Common.Equivalent first last := Iff.rfl

@[simp] theorem Argument.equivalent_row (first last : Common.Row) :
    Argument.Equivalent (.row first) (.row last) ↔ first = last := by
  constructor
  · rintro ⟨forward, backward⟩
    exact Common.rowLe_antisymm forward backward
  · rintro rfl
    exact ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩

@[simp] theorem Argument.equivalent_value_row (first : Common.Ty) (last : Common.Row) :
    ¬ Argument.Equivalent (.value first) (.row last) := fun same => same.1

@[simp] theorem Argument.equivalent_row_value (first : Common.Row) (last : Common.Ty) :
    ¬ Argument.Equivalent (.row first) (.value last) := fun same => same.1

def ArgumentsEquivalent : List Argument → List Argument → Prop
  | [], [] => True
  | first :: rest, last :: tail => first.Equivalent last ∧ ArgumentsEquivalent rest tail
  | _, _ => False

theorem argumentsEquivalent_iff (first last : List Argument) :
    ArgumentsEquivalent first last ↔
      first.length = last.length ∧
      ∀ (index : Nat) (a b : Argument),
        first[index]? = some a → last[index]? = some b → a.Equivalent b := by
  induction first generalizing last with
  | nil => cases last <;> simp [ArgumentsEquivalent]
  | cons first rest ih =>
      cases last with
      | nil => simp [ArgumentsEquivalent]
      | cons last tail =>
          simp only [ArgumentsEquivalent, ih, List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨head, size, pointwise⟩
            refine ⟨size, ?_⟩
            intro index a b left right
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
                subst a
                subst b
                exact head
            | succ index => exact pointwise index a b left right
          · rintro ⟨size, pointwise⟩
            exact ⟨pointwise 0 first last rfl rfl, size,
              fun index a b left right => pointwise (index + 1) a b left right⟩

structure Head where
  name : Nat
  arguments : List Argument

inductive Demand where
  | head : Nat → Nat → Demand
  | lower : Nat → Argument → Demand
  | upper : Nat → Argument → Demand

def Accept (head : Head) : Demand → Prop
  | .head name arity => head.name = name ∧ head.arguments.length = arity
  | .lower index expected =>
      ∃ actual, head.arguments[index]? = some actual ∧ expected.Le actual
  | .upper index expected =>
      ∃ actual, head.arguments[index]? = some actual ∧ actual.Le expected

def Subtype (first last : Head) : Prop :=
  ∀ demand, Accept last demand → Accept first demand

theorem subtype_refl (head : Head) : Subtype head head := fun _ accepted => accepted

theorem subtype_trans {first middle last : Head}
    (before : Subtype first middle) (after : Subtype middle last) : Subtype first last :=
  fun demand accepted => before demand (after demand accepted)

/-- Arbitrary IDs, arbitrary arities, and arbitrary common value/row arguments.
No normalization, finite observation bound, solver success, or supplied
argument-equivalence premise is used. -/
theorem nominal_head_invariant_exact (first last : Head) :
    Subtype first last ↔ first.name = last.name ∧
      first.arguments.length = last.arguments.length ∧
      ArgumentsEquivalent first.arguments last.arguments := by
  constructor
  · intro below
    have identity := below (.head last.name last.arguments.length) ⟨rfl, rfl⟩
    refine ⟨identity.1, identity.2, (argumentsEquivalent_iff _ _).mpr ⟨identity.2, ?_⟩⟩
    intro index a b left right
    obtain ⟨upper, upperAt, upperLe⟩ := below (.upper index b) ⟨b, right, b.le_refl⟩
    obtain ⟨lower, lowerAt, lowerLe⟩ := below (.lower index b) ⟨b, right, b.le_refl⟩
    have upperSame : upper = a := Option.some.inj (upperAt.symm.trans left)
    have lowerSame : lower = a := Option.some.inj (lowerAt.symm.trans left)
    subst upper
    subst lower
    exact ⟨upperLe, lowerLe⟩
  · rintro ⟨identity, size, same⟩ demand accepted
    have pointwise := (argumentsEquivalent_iff _ _).mp same |>.2
    cases demand with
    | head name arity => exact ⟨identity.trans accepted.1, size.trans accepted.2⟩
    | upper index expected =>
        obtain ⟨actual, found, below⟩ := accepted
        obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp found
        have firstBound : index < first.arguments.length := by omega
        let previous := first.arguments[index]
        have previousAt : first.arguments[index]? = some previous := by simp [previous, firstBound]
        have currentAt : last.arguments[index]? = some actual := List.getElem?_eq_some_iff.mpr ⟨bound, found⟩
        exact ⟨previous, previousAt, Argument.le_trans
          (pointwise index previous actual previousAt currentAt).1 below⟩
    | lower index expected =>
        obtain ⟨actual, found, below⟩ := accepted
        obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp found
        have firstBound : index < first.arguments.length := by omega
        let previous := first.arguments[index]
        have previousAt : first.arguments[index]? = some previous := by simp [previous, firstBound]
        have currentAt : last.arguments[index]? = some actual := List.getElem?_eq_some_iff.mpr ⟨bound, found⟩
        exact ⟨previous, previousAt, Argument.le_trans below
          (pointwise index previous actual previousAt currentAt).2⟩

theorem nominal_head_subtype_symmetric {first last : Head} (below : Subtype first last) :
    Subtype last first := by
  obtain ⟨identity, size, same⟩ := (nominal_head_invariant_exact first last).mp below
  apply (nominal_head_invariant_exact last first).mpr
  refine ⟨identity.symm, size.symm, (argumentsEquivalent_iff _ _).mpr ⟨size.symm, ?_⟩⟩
  intro index a b left right
  have pair := (argumentsEquivalent_iff _ _).mp same |>.2 index b a right left
  exact ⟨pair.2, pair.1⟩

end Yulang.CommonNominalHeads
