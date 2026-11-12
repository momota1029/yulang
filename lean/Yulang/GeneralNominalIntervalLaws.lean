import Yulang.GeneralNominalState
import Yulang.CommonRecursiveNominalIntervals

/-! Centreless interval laws on the existing full nominal carrier. The four
ordinary inequalities express consistency of a shared argument. Equality of
arguments belonging to distinct nominal occurrences is a separate obligation;
it is not inferred from overlapping bounds. No nominal body is unfolded. -/
namespace Yulang.GeneralNominalIntervalLaws

open CommonNominalFullCarrier
open GeneralNominalState (Parameter Fits FitsAll)
open PresenceNormalForm (Atom All)

abbrev Bounds := Ty × Ty

def Holds (bounds : Bounds) (value : Ty) : Prop :=
  Subtype bounds.1 value ∧ Subtype value bounds.2

def merge (first last : Bounds) : Bounds :=
  (.union first.1 last.1, .inter first.2 last.2)

def Checks (first last : Bounds) : Prop :=
  Subtype first.1 first.2 ∧ Subtype last.1 last.2 ∧
    Subtype first.1 last.2 ∧ Subtype last.1 first.2

theorem merge_holds (first last : Bounds) (value : Ty) :
    Holds (merge first last) value ↔ Holds first value ∧ Holds last value := by
  simp only [Holds, merge, common_union_is_join, common_inter_is_meet]
  exact ⟨fun ⟨⟨a,b⟩,c,d⟩ => ⟨⟨a,c⟩,b,d⟩,
    fun ⟨⟨a,b⟩,c,d⟩ => ⟨⟨a,c⟩,b,d⟩⟩

theorem merge_consistent (first last : Bounds) :
    Subtype (merge first last).1 (merge first last).2 ↔ Checks first last := by
  simp only [merge, common_union_is_join, common_inter_is_meet, Checks]
  exact ⟨fun ⟨⟨a,b⟩,c,d⟩ => ⟨a,d,c,b⟩,
    fun ⟨a,b,c,d⟩ => ⟨⟨a,d⟩,c,b⟩⟩

theorem shared_value_checks (first last : Bounds) (value : Ty)
    (one : Holds first value) (two : Holds last value) : Checks first last :=
  ⟨subtype_trans one.1 one.2, subtype_trans two.1 two.2,
    subtype_trans one.1 two.2, subtype_trans two.1 one.2⟩

def checks (state : GeneralSourceState.State) :
    Parameter state.slots → Parameter state.slots → Option (List (Atom Nat))
  | .type a, .type b => some
      ((CommonRecursiveNominalIntervals.Bounds.interval a.1 a.2).checks
        (.interval b.1 b.2) |>.map fun p =>
          .tyLe (.var (state.source p.1)) (.var (state.source p.2)))
  | .row a, .row b => some
      ((CommonRecursiveNominalIntervals.Bounds.interval a.1 a.2).checks
        (.interval b.1 b.2) |>.map fun p =>
          .rowLe (.var (state.rowSource p.1)) (.var (state.rowSource p.2)))
  | _, _ => none

def ParameterChecks (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) :
    Parameter state.slots → Parameter state.slots → Prop
  | .type a, .type b => Checks
      ((model (state.source a.1)).1, (model (state.source a.2)).1)
      ((model (state.source b.1)).1, (model (state.source b.2)).1)
  | .row a, .row b =>
      Common.rowLe (model (state.rowSource a.1)).2 (model (state.rowSource a.2)).2 ∧
      Common.rowLe (model (state.rowSource b.1)).2 (model (state.rowSource b.2)).2 ∧
      Common.rowLe (model (state.rowSource a.1)).2 (model (state.rowSource b.2)).2 ∧
      Common.rowLe (model (state.rowSource b.1)).2 (model (state.rowSource a.2)).2
  | _, _ => False

theorem checks_exact (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (first last : Parameter state.slots) :
    (∃ atoms, checks state first last = some atoms ∧ All CommonNominalFullCarrier.model model atoms) ↔
      ParameterChecks state model first last := by
  cases first <;> cases last <;>
    simp [checks, ParameterChecks, Checks, CommonRecursiveNominalIntervals.Bounds.checks,
      CommonRecursiveNominalIntervals.Bounds.lower, CommonRecursiveNominalIntervals.Bounds.upper,
      All, Atom.Holds, Core.PresenceGeneration.TyTerm.eval, Core.PresenceGeneration.RowTerm.eval,
      CommonNominalFullCarrier.model, and_assoc, and_left_comm, and_comm]

theorem fits_equivalent (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bounds : Parameter state.slots)
    (first last : Argument) (same : ArgumentEquivalent first last) :
    Fits state model bounds first ↔ Fits state model bounds last := by
  cases bounds <;> cases first <;> cases last <;> simp only [ArgumentEquivalent] at same
  all_goals try exact False.elim same
  · exact ⟨fun h => ⟨subtype_trans h.1 same.1, subtype_trans same.2 h.2⟩,
      fun h => ⟨subtype_trans h.1 same.2, subtype_trans same.1 h.2⟩⟩
  · cases same; rfl
  · rfl
  · cases same; rfl

theorem fits_checks (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (first last : Parameter state.slots)
    (value : Argument) (one : Fits state model first value) (two : Fits state model last value) :
    ParameterChecks state model first last := by
  cases first <;> cases last <;> cases value <;> simp only [Fits] at one two
  all_goals try exact False.elim one
  all_goals try exact False.elim two
  · exact shared_value_checks _ _ _ one two
  · exact ⟨Common.rowLe_trans one.1 one.2, Common.rowLe_trans two.1 two.2,
      Common.rowLe_trans one.1 two.2, Common.rowLe_trans two.1 one.2⟩

theorem fitsAll_at (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bounds : List (Parameter state.slots))
    (values : List Argument) (fits : FitsAll state model bounds values)
    (index : Nat) (parameter : Parameter state.slots) (found : bounds[index]? = some parameter) :
    ∃ value, values[index]? = some value ∧ Fits state model parameter value := by
  induction fits generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst parameter; exact ⟨_,rfl,head⟩
      | succ index => exact ih index found

/-- Same-head nominal endpoints force equality of their actual parameters.
The recorded intervals may have different identities and different values. -/
theorem nominal_endpoint_checks (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (lower upper : Fin state.base.slots)
    (left right : GeneralNominalState.Descriptor state.base.slots)
    (first : state.nominals lower = some left) (last : state.nominals upper = some right)
    (below : Subtype (model (state.base.source lower)).1 (model (state.base.source upper)).1) :
    left.declaration.name = right.declaration.name ∧
      ∀ (index : Nat) (a b : Parameter state.base.slots), left.arguments[index]? = some a → right.arguments[index]? = some b →
        ParameterChecks state.base model a b := by
  obtain ⟨xs,xf,xe⟩ := models.2.1 lower left first
  obtain ⟨ys,yf,ye⟩ := models.2.1 upper right last
  have relation := (nominal_regular_invariant_exact _ _ _ _).mp
    (subtype_trans xe.2 (subtype_trans below ye.1))
  refine ⟨relation.1, ?_⟩
  intro index a b ha hb
  obtain ⟨x,hx,fx⟩ := fitsAll_at _ _ _ _ xf index a ha
  obtain ⟨y,hy,fy⟩ := fitsAll_at _ _ _ _ yf index b hb
  exact fits_checks _ _ a b y
    ((fits_equivalent _ _ a x y (relation.2.2 index x y hx hy)).mp fx) fy

theorem nominal_subtype_equivalent (name other : Nat) (first last : List Argument)
    (below : Subtype (nominal name first) (nominal other last)) :
    Equivalent (nominal name first) (nominal other last) := by
  have same := (nominal_regular_invariant_exact _ _ _ _).mp below
  refine ⟨below, (nominal_regular_invariant_exact _ _ _ _).mpr ⟨same.1.symm, same.2.1.symm, ?_⟩⟩
  intro index b a hb ha
  have equal := same.2.2 index a b ha hb
  cases a <;> cases b <;> simp only [ArgumentEquivalent] at *
  · exact ⟨equal.2,equal.1⟩
  · exact equal.symm

/-- No chosen representative is needed: invariance itself identifies any
actual value between two nominal endpoints with the lower endpoint. -/
theorem nominal_sandwich (name other : Nat) (first last : List Argument) (value : Ty)
    (lower : Subtype (nominal name first) value)
    (upper : Subtype value (nominal other last)) :
    Equivalent value (nominal name first) ∧ Equivalent value (nominal other last) := by
  have equal := nominal_subtype_equivalent name other first last (subtype_trans lower upper)
  exact ⟨⟨subtype_trans upper equal.2, lower⟩, upper, subtype_trans equal.2 lower⟩

theorem pair_interval (first last : Bounds) (a b : Ty) :
    Holds (pair first.1 last.1, pair first.2 last.2) (pair a b) ↔
      Holds first a ∧ Holds last b := by
  have lower : Subtype (pair first.1 last.1) (pair a b) ↔
      Subtype first.1 a ∧ Subtype last.1 b := common_pair_iff _ _ _ _
  have upper : Subtype (pair a b) (pair first.2 last.2) ↔
      Subtype a first.2 ∧ Subtype b last.2 := common_pair_iff _ _ _ _
  simp only [Holds, lower, upper]
  exact ⟨fun ⟨⟨x,y⟩,z,w⟩ => ⟨⟨x,z⟩,y,w⟩,
    fun ⟨⟨x,y⟩,z,w⟩ => ⟨⟨x,z⟩,y,w⟩⟩

theorem variant_interval (tag : Nat) (bounds : Bounds) (value : Ty) :
    Holds (variant tag bounds.1, variant tag bounds.2) (variant tag value) ↔ Holds bounds value := by
  exact and_congr (common_variant_iff tag bounds.1 value) (common_variant_iff tag value bounds.2)

end Yulang.GeneralNominalIntervalLaws
