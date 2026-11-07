import Yulang.CommonNominalSyntax
import Yulang.CommonNominalFullDemand
import Yulang.Common

/-!
# Regular nominal carrier with full unknown role heads

The carrier retains dedicated nominal layers in all constructor positions and
finite mutually recursive blocks. Subtyping quantifies every constructor depth,
negative rank, independent environment and demand. No finite depth or solver
success is an input. The underlying syntax is shared with the earlier nominal candidate, but
full unknown-role environments distinguish mixed nominal/Float unions from
top. Old Common conservativity and transfer of source/solver results remain
separate obligations; the earlier candidate is not silently redefined.
-/

namespace Yulang.CommonNominalFullCarrier

abbrev Row := Common.Row
abbrev Ty := CommonNominalSyntax.Ty Row
abbrev Argument := Ty ⊕ Row
abbrev FiniteArgument := CommonNominalFullDemand.Ty Row ⊕ Row

def observeTy (depth : Nat) (type : Ty) : CommonNominalFullDemand.Ty Row :=
  type.evalAt depth (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth)

def Subtype (source target : Ty) : Prop :=
  ∀ depth, CommonNominalFullDemand.ProducerLe Common.rowLe (observeTy depth source) (observeTy depth target)

def Equivalent (source target : Ty) : Prop := Subtype source target ∧ Subtype target source

def nominal (name : Nat) (arguments : List Argument) : Ty :=
  .nominal name (arguments.map (Sum.map CommonNominalSyntax.State.node id))

def argumentAt (depth : Nat) : Argument → FiniteArgument :=
  Sum.map (fun type => CommonNominalSyntax.observe (CommonNominalSyntax.graph Row)
    depth (.node type)) id

def ArgumentEquivalent : Argument → Argument → Prop
  | .inl first, .inl last => Equivalent first last
  | .inr first, .inr last => first = last
  | _, _ => False

def ArgumentsEquivalent (first last : List Argument) : Prop :=
  ∀ (index : Nat) (a b : Argument), first[index]? = some a → last[index]? = some b →
    ArgumentEquivalent a b

theorem subtype_refl (type : Ty) : Subtype type type :=
  fun _ => CommonNominalFullDemand.producerLe_refl _

theorem subtype_trans {first middle last : Ty}
    (before : Subtype first middle) (after : Subtype middle last) : Subtype first last :=
  fun depth => CommonNominalFullDemand.producerLe_trans (before depth) (after depth)

@[simp] theorem observe_nominal (depth : Nat) (name : Nat) (arguments : List Argument) :
    observeTy depth (nominal name arguments) =
      .nominal name (arguments.map (argumentAt depth)) := by
  simp only [observeTy, nominal, CommonNominalSyntax.Layer.evalAt, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  cases argument <;> rfl

theorem argument_equivalent_exact (first last : Argument) :
    (∀ depth, CommonNominalFullDemand.ArgumentEquivalent (leRow := Common.rowLe)
      (argumentAt depth first) (argumentAt depth last)) ↔ ArgumentEquivalent first last := by
  cases first with
  | inl first =>
      cases last with
      | inl last =>
          constructor
          · intro allDepths
            exact ⟨fun depth => (allDepths (depth + 1)).1,
              fun depth => (allDepths (depth + 1)).2⟩
          · intro same depth
            cases depth with
            | zero => exact CommonNominalFullDemand.producerEq_refl _
            | succ depth => exact ⟨same.1 depth, same.2 depth⟩
      | inr last =>
          constructor
          · intro impossible; exact impossible 0
          · exact False.elim
  | inr first =>
      cases last with
      | inl last =>
          constructor
          · intro impossible; exact impossible 0
          · exact False.elim
      | inr last =>
          constructor
          · intro orders
            exact Common.rowLe_antisymm (orders 0).1 (orders 0).2
          · rintro rfl depth
            exact ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩

/-- Every declaration identity, every arity, and arbitrary values of this same
regular carrier as arguments (including nested and mutually recursive nominal
blocks). Rows are arbitrary occurrence sets, and invariant row equivalence is
literal row equality. This is the carrier theorem; source and solver
conservativity are not asserted by its name. -/
theorem nominal_regular_invariant_exact (name other : Nat) (first last : List Argument) :
    Subtype (nominal name first) (nominal other last) ↔
      name = other ∧ first.length = last.length ∧ ArgumentsEquivalent first last := by
  have finite (depth : Nat) := CommonNominalFullDemand.nominal_finite_invariant_exact
    Common.rowLe_refl Common.rowLe_trans name other
    (first.map (argumentAt depth)) (last.map (argumentAt depth))
  constructor
  · intro below
    have atDepth (depth : Nat) := (finite depth).mp (by
      simpa only [observe_nominal] using below depth)
    refine ⟨(atDepth 0).1, ?_, ?_⟩
    · simpa only [List.length_map] using (atDepth 0).2.1
    · intro index a b left right
      apply (argument_equivalent_exact a b).mp
      intro depth
      apply (atDepth depth).2.2 index (argumentAt depth a) (argumentAt depth b)
      · simp [List.getElem?_map, left]
      · simp [List.getElem?_map, right]
  · rintro ⟨identity, size, same⟩ depth
    rw [observe_nominal, observe_nominal]
    apply (finite depth).mpr
    refine ⟨identity, by simpa only [List.length_map] using size, ?_⟩
    intro index a b left right
    obtain ⟨originalA, originalLeft, rfl⟩ := Option.map_eq_some_iff.mp
      (show (first[index]?).map (argumentAt depth) = some a by
        simpa only [List.getElem?_map] using left)
    obtain ⟨originalB, originalRight, rfl⟩ := Option.map_eq_some_iff.mp
      (show (last[index]?).map (argumentAt depth) = some b by
        simpa only [List.getElem?_map] using right)
    exact (argument_equivalent_exact originalA originalB).mpr
      (same index originalA originalB originalLeft originalRight) depth

theorem nominal_union_not_top (first last : Nat) :
    ¬ Subtype .top (.union (nominal first []) (nominal last [])) := by
  intro below
  apply CommonNominalFullDemand.nominal_union_not_top first last
  simpa only [observeTy, nominal, CommonNominalSyntax.Layer.evalAt, List.map_nil] using below 0

theorem boxed_nominal_union_not_top (box first last : Nat) :
    ¬ Subtype (nominal box [.inl (.union (nominal first []) (nominal last []))]) (nominal box [.inl .top]) := by
  intro below
  have same := (nominal_regular_invariant_exact _ _ _ _).mp below |>.2.2
  have invariant := same 0 (.inl (.union (nominal first []) (nominal last []))) (.inl .top) rfl rfl
  exact nominal_union_not_top first last invariant.2

end Yulang.CommonNominalFullCarrier
