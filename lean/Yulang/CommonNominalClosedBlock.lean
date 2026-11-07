import Yulang.CommonNominalPresenceTailRegular

/-!
# Exact guarded blocks with arbitrary external regular states

External states are retained literally; they need not be a separately chosen
finite family of type arguments. This supports field templates that inline
whole shared parameters at positive same-depth positions. Internal block
references still cross their original payload guards.
-/

namespace Yulang.CommonNominalClosedBlock

open CommonNominalCarrier
open CommonNominalSyntax (Layer State)

abbrev Body (nodes : Nat) := Fin nodes → Layer Row (Fin nodes ⊕ State Row)

def node (body : Body nodes) (index : Fin nodes) : State Row := CommonNominalSyntax.closeBlock body index

def instantiate (body : Body nodes) (index : Fin nodes) : Ty := CommonNominalSyntax.graph Row (node body index)

def closedReference (body : Body nodes) : Fin nodes ⊕ State Row → State Row := Sum.elim (node body) id

def valueReference (values : Fin nodes → Ty) : Fin nodes ⊕ State Row → State Row :=
  Sum.elim (fun index => State.node (values index)) id

def equation (body : Body nodes) (values : Fin nodes → Ty) (index : Fin nodes) : Ty :=
  (body index).map (valueReference values)

def Models (body : Body nodes) (values : Fin nodes → Ty) : Prop :=
  ∀ index, Equivalent (equation body values index) (values index)

theorem instantiate_graph (body : Body nodes) (index : Fin nodes) :
    instantiate body index = (body index).map (closedReference body) := by
  rw [instantiate, node, CommonNominalSyntax.graph_closeBlock]
  rfl

theorem all_parameter_sound (body : Body nodes) : Models body (instantiate body) := by
  intro index
  have same (depth : Nat) : observeTy depth (instantiate body index) =
      observeTy depth (equation body (instantiate body) index) := by
    rw [instantiate_graph]
    simp only [observeTy, equation, CommonNominalSyntax.Layer.evalAt_map]
    congr 1
    funext reference
    cases reference with
    | inr state => rfl
    | inl index => exact (CommonNominalSyntax.quote_graph_observe_exact depth (node body index)).symm
  constructor <;> intro depth <;> rw [← same] <;> exact CommonNominalFinite.producerLe_refl _

private theorem recover_observation (body : Body nodes) (values : Fin nodes → Ty) (model : Models body values)
    (depth : Nat) (index : Fin nodes) :
    CommonNominalFinite.ProducerEq Common.rowLe
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (node body index))
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node (values index))) := by
  induction depth generalizing index with
  | zero => exact CommonNominalFinite.producerEq_refl _
  | succ depth ih =>
      change CommonNominalFinite.ProducerEq Common.rowLe
        ((instantiate body index).evalAt depth (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth))
        (observeTy depth (values index))
      rw [instantiate_graph]
      simp only [CommonNominalSyntax.Layer.evalAt_map]
      have pointwise : ∀ reference,
          CommonNominalFinite.ProducerEq Common.rowLe
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (closedReference body reference))
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (valueReference values reference)) := by
        intro reference
        cases reference with
        | inl index => exact ih index
        | inr state => exact CommonNominalFinite.producerEq_refl _
      have substituted := CommonNominalSyntax.Layer.evalAt_congr Common.rowLe
        Common.rowLe_refl Common.rowLe_trans depth _ _ pointwise (body index)
      have original : CommonNominalFinite.ProducerEq Common.rowLe
          ((body index).evalAt depth
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth ∘ valueReference values))
          (observeTy depth (values index)) := by
        simpa only [equation, observeTy, CommonNominalSyntax.Layer.evalAt_map, CommonNominalFinite.ProducerEq] using
          And.intro ((model index).1 depth) ((model index).2 depth)
      exact CommonNominalFinite.producerEq_trans substituted original

/-- Every original model is the same regular closure at all original nodes,
up to demand equivalence. External states are not truncated or normalized. -/
theorem all_models_recovered (body : Body nodes) (values : Fin nodes → Ty) (model : Models body values) :
    ∀ index, Equivalent (instantiate body index) (values index) := by
  intro index
  exact ⟨fun depth => (recover_observation body values model (depth + 1) index).1,
    fun depth => (recover_observation body values model (depth + 1) index).2⟩

theorem models_congr (body : Body nodes) (first last : Fin nodes → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) : Models body first ↔ Models body last := by
  have equations (index : Fin nodes) : Equivalent (equation body first index) (equation body last index) := by
    have finite (depth : Nat) : CommonNominalFinite.ProducerEq Common.rowLe
        (observeTy depth (equation body first index)) (observeTy depth (equation body last index)) := by
      simp only [equation, observeTy, CommonNominalSyntax.Layer.evalAt_map]
      apply CommonNominalSyntax.Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans
      intro reference
      cases reference with
      | inr state => exact CommonNominalFinite.producerEq_refl _
      | inl index =>
          cases depth with
          | zero => exact CommonNominalFinite.producerEq_refl _
          | succ depth => exact ⟨(same index).1 depth, (same index).2 depth⟩
    exact ⟨fun depth => (finite depth).1, fun depth => (finite depth).2⟩
  constructor
  · intro model index
    exact equivalent_trans (equivalent_symm (equations index)) (equivalent_trans (model index) (same index))
  · intro model index
    exact equivalent_trans (equations index) (equivalent_trans (model index) (equivalent_symm (same index)))

theorem models_exact (body : Body nodes) (values : Fin nodes → Ty) :
    Models body values ↔ ∀ index, Equivalent (instantiate body index) (values index) := by
  constructor
  · exact all_models_recovered body values
  · intro recovered
    exact (models_congr body (instantiate body) values recovered).mp (all_parameter_sound body)

end Yulang.CommonNominalClosedBlock
