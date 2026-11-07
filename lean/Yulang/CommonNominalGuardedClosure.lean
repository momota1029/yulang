import Yulang.CommonNominalLayerCongruence
import Yulang.CommonNominalConstructors

/-!
# All-parameter regular closure for mixed nominal constructor equations

Every reference crosses a payload guard in the finite Layer syntax. Inline
record tails, default sources, lattice nodes and masks retain their existing
same-depth interpretation. Nominal arguments are dedicated guarded references
and invariant rows. No graph equation is moved into a parameter condition.
-/

namespace Yulang.CommonNominalGuardedClosure

open CommonNominalCarrier

abbrev Body (nodes parameters : Nat) := Fin nodes → CommonNominalSyntax.Layer Row (Fin nodes ⊕ Fin parameters)

def instantiatedBody (body : Body nodes parameters) (arguments : Fin parameters → Ty) :=
  fun index => (body index).map (Sum.map id (fun parameter => CommonNominalSyntax.State.node (arguments parameter)))

def node (body : Body nodes parameters) (arguments : Fin parameters → Ty) (index : Fin nodes) :
    CommonNominalSyntax.State Row :=
  CommonNominalSyntax.closeBlock (instantiatedBody body arguments) index

def instantiate (body : Body nodes parameters) (arguments : Fin parameters → Ty) (index : Fin nodes) : Ty :=
  CommonNominalSyntax.graph Row (node body arguments index)

def closedReference (body : Body nodes parameters) (arguments : Fin parameters → Ty) :
    Fin nodes ⊕ Fin parameters → CommonNominalSyntax.State Row :=
  Sum.elim (node body arguments) (fun parameter => .node (arguments parameter))

def valueReference (values : Fin nodes → Ty) (arguments : Fin parameters → Ty) :
    Fin nodes ⊕ Fin parameters → CommonNominalSyntax.State Row :=
  Sum.elim (fun index => .node (values index)) (fun parameter => .node (arguments parameter))

def equation (body : Body nodes parameters) (arguments : Fin parameters → Ty)
    (values : Fin nodes → Ty) (index : Fin nodes) : Ty :=
  (body index).map (valueReference values arguments)

def Models (body : Body nodes parameters) (arguments : Fin parameters → Ty) (values : Fin nodes → Ty) : Prop :=
  ∀ index, Equivalent (values index) (equation body arguments values index)

theorem instantiate_graph (body : Body nodes parameters) (arguments : Fin parameters → Ty) (index : Fin nodes) :
    instantiate body arguments index = (body index).map (closedReference body arguments) := by
  simp only [instantiate, node, CommonNominalSyntax.graph_closeBlock, instantiatedBody,
    CommonNominalSyntax.Layer.map_comp]
  congr 1
  funext reference
  cases reference <;> rfl

private theorem reference_observe (body : Body nodes parameters) (arguments : Fin parameters → Ty)
    (depth : Nat) (reference : Fin nodes ⊕ Fin parameters) :
    CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (closedReference body arguments reference) =
      CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth
        (valueReference (instantiate body arguments) arguments reference) := by
  cases reference with
  | inl index => exact (CommonNominalSyntax.quote_graph_observe_exact depth (node body arguments index)).symm
  | inr parameter => rfl

/-- Every actual argument vector, with no constraints or residual predicate. -/
theorem all_parameter_sound (body : Body nodes parameters) (arguments : Fin parameters → Ty) :
    Models body arguments (instantiate body arguments) := by
  intro index
  have same (depth : Nat) : observeTy depth (instantiate body arguments index) =
      observeTy depth (equation body arguments (instantiate body arguments) index) := by
    rw [instantiate_graph]
    simp only [observeTy, equation, CommonNominalSyntax.Layer.evalAt_map]
    congr 1
    funext reference
    exact reference_observe body arguments depth reference
  exact ⟨fun depth => by rw [same]; exact CommonNominalFinite.producerLe_refl _,
    fun depth => by rw [same]; exact CommonNominalFinite.producerLe_refl _⟩

private theorem recover_observation (body : Body nodes parameters) (arguments : Fin parameters → Ty)
    (values : Fin nodes → Ty) (models : Models body arguments values)
    (depth : Nat) (index : Fin nodes) :
    CommonNominalFinite.ProducerEq Common.rowLe
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (node body arguments index))
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node (values index))) := by
  induction depth generalizing index with
  | zero => exact CommonNominalFinite.producerEq_refl _
  | succ depth ih =>
      change CommonNominalFinite.ProducerEq Common.rowLe
        ((instantiate body arguments index).evalAt depth (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth))
        (observeTy depth (values index))
      rw [instantiate_graph]
      simp only [CommonNominalSyntax.Layer.evalAt_map]
      have pointwise : ∀ reference,
          CommonNominalFinite.ProducerEq Common.rowLe
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (closedReference body arguments reference))
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (valueReference values arguments reference)) := by
        intro reference
        cases reference with
        | inl index => exact ih index
        | inr parameter => exact CommonNominalFinite.producerEq_refl _
      have substituted := CommonNominalSyntax.Layer.evalAt_congr Common.rowLe
        Common.rowLe_refl Common.rowLe_trans depth _ _ pointwise (body index)
      have original : CommonNominalFinite.ProducerEq Common.rowLe
          (observeTy depth (values index))
          ((body index).evalAt depth
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth ∘ valueReference values arguments)) := by
        simpa only [equation, observeTy, CommonNominalSyntax.Layer.evalAt_map, CommonNominalFinite.ProducerEq] using
          And.intro ((models index).1 depth) ((models index).2 depth)
      exact CommonNominalFinite.producerEq_trans substituted (CommonNominalFinite.producerEq_symm original)

/-- Any original solution is recovered simultaneously at every node,
including mutually recursive nominal/arrow/record/default/mask components. -/
theorem all_models_recovered (body : Body nodes parameters) (arguments : Fin parameters → Ty)
    (values : Fin nodes → Ty) (models : Models body arguments values) :
    ∀ index, Equivalent (instantiate body arguments index) (values index) := by
  intro index
  exact ⟨fun depth => (recover_observation body arguments values models (depth + 1) index).1,
    fun depth => (recover_observation body arguments values models (depth + 1) index).2⟩

private theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩

private theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

private theorem equation_congr (body : Body nodes parameters) (arguments : Fin parameters → Ty)
    (first last : Fin nodes → Ty) (same : ∀ index, Equivalent (first index) (last index))
    (index : Fin nodes) : Equivalent (equation body arguments first index) (equation body arguments last index) := by
  have finite (depth : Nat) : CommonNominalFinite.ProducerEq Common.rowLe
      (observeTy depth (equation body arguments first index))
      (observeTy depth (equation body arguments last index)) := by
    simp only [equation, observeTy, CommonNominalSyntax.Layer.evalAt_map]
    apply CommonNominalSyntax.Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans
    intro reference
    cases reference with
    | inl index =>
        cases depth with
        | zero => exact CommonNominalFinite.producerEq_refl _
        | succ depth => exact ⟨(same index).1 depth, (same index).2 depth⟩
    | inr parameter => exact CommonNominalFinite.producerEq_refl _
  exact ⟨fun depth => (finite depth).1, fun depth => (finite depth).2⟩

theorem models_exact (body : Body nodes parameters) (arguments : Fin parameters → Ty) (values : Fin nodes → Ty) :
    Models body arguments values ↔ ∀ index, Equivalent (instantiate body arguments index) (values index) := by
  constructor
  · exact all_models_recovered body arguments values
  · intro recovered index
    exact equivalent_trans (equivalent_symm (recovered index))
      (equivalent_trans (all_parameter_sound body arguments index)
        (equation_congr body arguments _ _ recovered index))

end Yulang.CommonNominalGuardedClosure

namespace Yulang.CommonNominalGuardedClosure

open CommonNominalCarrier

private theorem equation_parameter_congr (body : Body nodes parameters)
    (first last : Fin parameters → Ty) (same : ∀ index, Equivalent (first index) (last index))
    (values : Fin nodes → Ty) (index : Fin nodes) :
    Equivalent (equation body first values index) (equation body last values index) := by
  have finite (depth : Nat) : CommonNominalFinite.ProducerEq Common.rowLe
      (observeTy depth (equation body first values index))
      (observeTy depth (equation body last values index)) := by
    simp only [equation, observeTy, CommonNominalSyntax.Layer.evalAt_map]
    apply CommonNominalSyntax.Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans
    intro reference
    cases reference with
    | inl index => exact CommonNominalFinite.producerEq_refl _
    | inr parameter =>
        cases depth with
        | zero => exact CommonNominalFinite.producerEq_refl _
        | succ depth => exact ⟨(same parameter).1 depth, (same parameter).2 depth⟩
  exact ⟨fun depth => (finite depth).1, fun depth => (finite depth).2⟩

/-- The entire recursive closure respects demand-equivalent shared free type
parameters, including parameters appearing in nominal arguments or arrows. -/
theorem parameter_congr (body : Body nodes parameters) (first last : Fin parameters → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) :
    ∀ index, Equivalent (instantiate body first index) (instantiate body last index) := by
  have original := all_parameter_sound body first
  have moved : Models body last (instantiate body first) := by
    intro index
    exact equivalent_trans (original index) (equation_parameter_congr body first last same _ index)
  intro index
  exact equivalent_symm (all_models_recovered body last _ moved index)

end Yulang.CommonNominalGuardedClosure
