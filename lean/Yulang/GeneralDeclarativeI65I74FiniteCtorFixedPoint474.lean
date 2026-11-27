import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
namespace Yulang.G04FiniteConstructorSemantics473
open CommonNominalFullCarrier
open CommonNominalSyntax (State Layer)
open CommonNominalFullDemand (ProducerEq producerEq_refl producerEq_trans producerEq_symm
  producerLe_pair_iff producerLe_variant_iff producerLe_record_mono nominal_finite_invariant_exact)

abbrev FT := CommonNominalFullDemand.Ty Common.Row
abbrev EqF := ProducerEq Common.rowLe

inductive Shell (α : Type) where
  | scalar (base : Inference.Base)
  | pair (first last : α)
  | row (fields : List (Nat × α))
  | exactEmpty
  | variant (tag : Nat) (payload : α)
  | unaryNominal (name : Nat) (argument : α)

def rowLayer : List (Nat × α) → Layer Row α
  | [] => .emptyRecord
  | (name,child)::rest => .record name child (rowLayer rest)

def shellLayer : Shell α → Layer Row α
  | .scalar b => .base b
  | .pair a b => .pair a b
  | .row fs => rowLayer fs
  | .exactEmpty => .exactEmpty
  | .variant k a => .variant k a
  | .unaryNominal name x => .nominal name [.inl x]

theorem evaluate_row_layer_congruent (depth : Nat) (a b : α → FT)
    (children : ∀ i, EqF (a i) (b i)) (fields : List (Nat × α)) :
    EqF ((rowLayer fields).evalAt depth a) ((rowLayer fields).evalAt depth b) := by
  induction fields with
  | nil => exact producerEq_refl _
  | cons head rest ih =>
    rcases head with ⟨tag,child⟩
    exact ⟨producerLe_record_mono tag (children child).1 ih.1,
      producerLe_record_mono tag (children child).2 ih.2⟩

theorem evaluate_unary_nominal_layer_congruent (k : Nat) {a b : FT}
    (related : EqF a b) :
    EqF (.nominal k [.inl a]) (.nominal k [.inl b]) := by
  have monotone {x y : FT} (eq : EqF x y) :
      CommonNominalFullDemand.ProducerLe Common.rowLe (.nominal k [.inl x]) (.nominal k [.inl y]) := by
    apply (nominal_finite_invariant_exact Common.rowLe_refl Common.rowLe_trans _ _ _ _).mpr
    refine ⟨rfl,rfl,?_⟩
    intro i left right fromL fromR
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at fromL fromR
      subst left
      subst right
      exact eq
    | succ i => cases i <;> simp at fromL
  exact ⟨monotone related,monotone (producerEq_symm related)⟩

theorem every_shell_is_congruent_in_its_actual_children_only
    (depth : Nat) (a b : α → FT) (children : ∀ i, EqF (a i) (b i)) (shell : Shell α) :
    EqF ((shellLayer shell).evalAt depth a) ((shellLayer shell).evalAt depth b) := by
  cases shell with
  | scalar | exactEmpty => exact producerEq_refl _
  | pair first last =>
    exact ⟨(producerLe_pair_iff ..).mpr ⟨(children first).1,(children last).1⟩,
      (producerLe_pair_iff ..).mpr ⟨(children first).2,(children last).2⟩⟩
  | row fields => exact evaluate_row_layer_congruent _ _ _ children fields
  | variant tag child =>
    exact ⟨(producerLe_variant_iff ..).mpr (children child).1,
      (producerLe_variant_iff ..).mpr (children child).2⟩
  | unaryNominal name child =>
    exact evaluate_unary_nominal_layer_congruent name (children child)

def body (g : Fin n → Shell (Fin n)) (i : Fin n) : Layer Row (Fin n ⊕ State Row) :=
  (shellLayer (g i)).map Sum.inl

def value (g : Fin n → Shell (Fin n)) (i : Fin n) : Ty :=
  CommonNominalSyntax.graph Row (CommonNominalSyntax.closeBlock (body g) i)

def formed (s : Shell α) (valueAt : α → Ty) : Ty :=
  (shellLayer s).map (State.node ∘ valueAt)

theorem block_value_replays_its_constructor_row
    (g : Fin n → Shell (Fin n)) (i : Fin n) (depth : Nat) :
    observeTy depth (value g i) =
      (shellLayer (g i)).evalAt depth (fun j =>
        CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth
          (CommonNominalSyntax.closeBlock (body g) j)) := by
  simp [value,observeTy,body,Function.comp_def,CommonNominalSyntax.blockRef]

theorem all_satisfying_assignments_have_the_same_regular_constructor_value
    (g : Fin n → Shell (Fin n)) (m : Fin n → Ty)
    (equations : ∀ i, Equivalent (m i) (formed (g i) m)) :
    ∀ i, Equivalent (m i) (value g i) := by
  have finite : ∀ d i, EqF (observeTy d (m i)) (observeTy d (value g i)) := by
    intro d
    induction d with
    | zero =>
      intro i
      have prior : EqF (observeTy 0 (m i)) (observeTy 0 (formed (g i) m)) :=
        ⟨(equations i).1 0,(equations i).2 0⟩
      apply producerEq_trans prior
      rw [block_value_replays_its_constructor_row]
      unfold formed observeTy
      rw [CommonNominalSyntax.Layer.evalAt_map]
      apply every_shell_is_congruent_in_its_actual_children_only
      intro j
      exact producerEq_refl _
    | succ d inductionHyp =>
      intro i
      have prior : EqF (observeTy (d+1) (m i)) (observeTy (d+1) (formed (g i) m)) :=
        ⟨(equations i).1 _,(equations i).2 _⟩
      apply producerEq_trans prior
      rw [block_value_replays_its_constructor_row]
      unfold formed observeTy
      rw [CommonNominalSyntax.Layer.evalAt_map]
      apply every_shell_is_congruent_in_its_actual_children_only
      intro j
      exact inductionHyp j
  exact fun i => ⟨fun d => (finite d i).1,fun d => (finite d i).2⟩

end Yulang.G04FiniteConstructorSemantics473
