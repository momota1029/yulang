import Yulang.CommonNominalHeads

/-!
# Declaration-directed nominal comparisons on the existing head metadata

A declaration supplies an already computed variance for each argument. This
module filters the EXISTING nominal demand vocabulary; it defines no new type
carrier or recursive demand interpreter. Covariant and contravariant positions
observe one direction, invariant positions both. The source verifier deriving
this table and its recursive-parameter cost analysis remain separate.

Point arguments here describe collapsed instances. Open invariant arguments
use the centre-less reconciliation modules, not unconditional point equality.
-/

namespace Yulang.CommonDeclaredNominalVariance

open CommonNominalHeads (Argument Head Demand Accept)

/-- Declaration metadata, fixed before expression inference. -/
inductive Variance where
  | covariant
  | contravariant
  | invariant
  | unused
  deriving DecidableEq, Repr

def Variance.Rel : Variance → Argument → Argument → Prop
  | .covariant, first, last => first.Le last
  | .contravariant, first, last => last.Le first
  | .invariant, first, last => first.Equivalent last
  | .unused, _, _ => True

def Variance.lowerVisible : Variance → Bool
  | .contravariant | .invariant => true
  | _ => false

def Variance.upperVisible : Variance → Bool
  | .covariant | .invariant => true
  | _ => false

private theorem upper_of_relation (mode : Variance) (first last : Argument)
    (visible : mode.upperVisible = true) (related : mode.Rel first last) : first.Le last := by
  cases mode <;> simp_all [Variance.upperVisible, Variance.Rel, CommonNominalHeads.Argument.Equivalent]

private theorem lower_of_relation (mode : Variance) (first last : Argument)
    (visible : mode.lowerVisible = true) (related : mode.Rel first last) : last.Le first := by
  cases mode <;> simp_all [Variance.lowerVisible, Variance.Rel, CommonNominalHeads.Argument.Equivalent]

def modeAt (modes : List Variance) (index : Nat) : Variance := modes[index]?.getD .unused

def Allowed (modes : List Variance) : Demand → Prop
  | .head _ _ => True
  | .lower index _ => (modeAt modes index).lowerVisible = true
  | .upper index _ => (modeAt modes index).upperVisible = true

def Subtype (modes : List Variance) (first last : Head) : Prop :=
  ∀ demand, Allowed modes demand → Accept last demand → Accept first demand

/-- Every ID/arity, arbitrary Common type/row arguments, and every fixed
variance table. Missing entries are unobserved; the actual declaration
verifier must check that the table arity and argument kinds are valid. -/
theorem nominal_head_variance_exact (modes : List Variance) (first last : Head) :
    Subtype modes first last ↔ first.name = last.name ∧
      first.arguments.length = last.arguments.length ∧
        ∀ (index : Nat) (a b : Argument),
          first.arguments[index]? = some a → last.arguments[index]? = some b →
            (modeAt modes index).Rel a b := by
  constructor
  · intro below
    have identity := below (.head last.name last.arguments.length) trivial ⟨rfl, rfl⟩
    refine ⟨identity.1, identity.2, ?_⟩
    intro index a b left right
    have upper (visible : (modeAt modes index).upperVisible = true) : a.Le b := by
      obtain ⟨actual, found, bounded⟩ := below (.upper index b) visible ⟨b, right, b.le_refl⟩
      have same := Option.some.inj (found.symm.trans left)
      subst actual
      exact bounded
    have lower (visible : (modeAt modes index).lowerVisible = true) : b.Le a := by
      obtain ⟨actual, found, bounded⟩ := below (.lower index b) visible ⟨b, right, b.le_refl⟩
      have same := Option.some.inj (found.symm.trans left)
      subst actual
      exact bounded
    cases mode : modeAt modes index with
    | covariant => exact upper (by simp [mode, Variance.upperVisible])
    | contravariant => exact lower (by simp [mode, Variance.lowerVisible])
    | invariant => exact ⟨upper (by simp [mode, Variance.upperVisible]),
        lower (by simp [mode, Variance.lowerVisible])⟩
    | unused => trivial
  · rintro ⟨identity, size, pointwise⟩ demand visible accepted
    cases demand with
    | head name arity => exact ⟨identity.trans accepted.1, size.trans accepted.2⟩
    | upper index expected =>
        obtain ⟨actual, found, bounded⟩ := accepted
        obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp found
        have firstBound : index < first.arguments.length := by omega
        let previous := first.arguments[index]
        have previousAt : first.arguments[index]? = some previous := by simp [previous, firstBound]
        have currentAt : last.arguments[index]? = some actual :=
          List.getElem?_eq_some_iff.mpr ⟨bound, found⟩
        exact ⟨previous, previousAt, Argument.le_trans
          (upper_of_relation _ _ _ visible (pointwise index previous actual previousAt currentAt)) bounded⟩
    | lower index expected =>
        obtain ⟨actual, found, bounded⟩ := accepted
        obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp found
        have firstBound : index < first.arguments.length := by omega
        let previous := first.arguments[index]
        have previousAt : first.arguments[index]? = some previous := by simp [previous, firstBound]
        have currentAt : last.arguments[index]? = some actual :=
          List.getElem?_eq_some_iff.mpr ⟨bound, found⟩
        exact ⟨previous, previousAt, Argument.le_trans bounded
          (lower_of_relation _ _ _ visible (pointwise index previous actual previousAt currentAt))⟩

theorem singleton_variance_exact (mode : Variance) (name other : Nat) (first last : Argument) :
    Subtype [mode] ⟨name, [first]⟩ ⟨other, [last]⟩ ↔ name = other ∧ mode.Rel first last := by
  rw [nominal_head_variance_exact]
  constructor
  · rintro ⟨identity, _, related⟩
    exact ⟨identity, related 0 first last rfl rfl⟩
  · rintro ⟨identity, related⟩
    refine ⟨identity, rfl, ?_⟩
    intro index a b left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst a; subst b
        exact related
    | succ index => simp at left

/-- In particular a plain covariant box compares by subtype, not equivalence. -/
theorem covariant_box_subtype_exact (name other : Nat) (first last : Common.Ty) :
    Subtype [.covariant] ⟨name, [.value first]⟩ ⟨other, [.value last]⟩ ↔
      name = other ∧ Common.Subtype first last :=
  singleton_variance_exact .covariant name other (.value first) (.value last)

theorem contravariant_singleton_exact (name other : Nat) (first last : Common.Ty) :
    Subtype [.contravariant] ⟨name, [.value first]⟩ ⟨other, [.value last]⟩ ↔
      name = other ∧ Common.Subtype last first :=
  singleton_variance_exact .contravariant name other (.value first) (.value last)

/-- The old whole point iff is retained exactly for all-invariant tables. -/
theorem all_invariant_special_case (first last : Head) :
    Subtype (List.replicate last.arguments.length .invariant) first last ↔
      CommonNominalHeads.Subtype first last := by
  constructor
  · intro below
    obtain ⟨identity, size, related⟩ := (nominal_head_variance_exact _ first last).mp below
    apply (CommonNominalHeads.nominal_head_invariant_exact first last).mpr
    refine ⟨identity, size, (CommonNominalHeads.argumentsEquivalent_iff _ _).mpr ⟨size, ?_⟩⟩
    intro index a b left right
    have within : index < last.arguments.length := (List.getElem?_eq_some_iff.mp right).1
    simpa [modeAt, within, Variance.Rel] using related index a b left right
  · intro below demand _ accepted
    exact below demand accepted

/-- Head-demand grouping is a separate property from modewise subtype.
The full source branch/readback and nesting bridges remain separate. -/
theorem covariant_box_union_grouping (name : Nat) (first last : Common.Ty) (demand : Demand)
    (visible : Allowed [.covariant] demand) :
    Accept ⟨name, [.value (.union first last)]⟩ demand ↔
      Accept ⟨name, [.value first]⟩ demand ∧ Accept ⟨name, [.value last]⟩ demand := by
  cases demand with
  | head expected arity => simp [Accept]
  | lower index expected =>
      cases index <;> simp [Allowed, modeAt, Variance.lowerVisible] at visible
  | upper index expected =>
      cases index with
      | zero =>
          cases expected <;>
            simp [Accept, CommonNominalHeads.Argument.Le, Common.common_union_is_join]
      | succ index => simp [Accept]

end Yulang.CommonDeclaredNominalVariance
