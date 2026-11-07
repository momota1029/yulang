import Yulang.CommonNominalPresenceTailLayers
import Yulang.CommonNominalLayerCongruence

/-!
# Closing guarded payloads and same-depth presence tails together

One finite graph shares its slot identities between guarded payloads and
same-depth tail/default-source references. Guarded references may occur in
either arrow argument or result, under masks, and inside arbitrary layers.
The same-depth eliminator first produces ordinary finite layers; a concrete
common regular block then closes their remaining payload references.

Original equations are interpreted by substituting the same independent
common assignment in both positions. Parameters are unrestricted common
types, with no solution certificate or residual constraint. The retraction
proof uses induction on constructor depth, and equivalence rather than
monotonicity at negative payload positions. The special depth-zero default
interpretation is retained by the existing layer interpreter and congruence.
-/

namespace Yulang.CommonNominalPresenceTailRegular

open CommonNominalCarrier (Ty Row)
open CommonNominalSyntax (Layer State)
open CommonNominalPresenceTailLayers (Body quoteLayer quoteGraph quoteFamily solveLayers)

variable {slots labels : Nat} {Index : Type}

private theorem equivalent_of_observe_eq {first last : Ty}
    (same : ∀ depth, CommonNominalCarrier.observeTy depth first = CommonNominalCarrier.observeTy depth last) :
    CommonNominalCarrier.Equivalent first last := by
  constructor <;> intro depth
  · rw [same depth]
    exact CommonNominalFinite.producerLe_refl _
  · rw [same depth]
    exact CommonNominalFinite.producerLe_refl _

private theorem finite_same_at (same : CommonNominalCarrier.Equivalent first last) (depth : Nat) :
    CommonNominalFinite.ProducerEq Common.rowLe (CommonNominalCarrier.observeTy depth first) (CommonNominalCarrier.observeTy depth last) :=
  ⟨same.1 depth, same.2 depth⟩

private theorem quote_same_at (same : CommonNominalCarrier.Equivalent first last) (depth : Nat) :
    CommonNominalFinite.ProducerEq Common.rowLe
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node first))
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node last)) :=
  ⟨CommonNominalCarrier.quote_observe_le same.1 depth, CommonNominalCarrier.quote_observe_le same.2 depth⟩

/-- Replacing a shared state reference by a quoted copy of its actual root
layer changes no finite observation and does not add a guard. -/
theorem map_quote_observe (layer : Layer Row Index) (references : Index → State Row) (depth : Nat) :
    CommonNominalCarrier.observeTy depth (layer.map references) =
      CommonNominalCarrier.observeTy depth (quoteLayer (fun index => CommonNominalSyntax.graph Row (references index)) layer) := by
  simp only [CommonNominalCarrier.observeTy, quoteLayer, Layer.evalAt_map]
  congr 1
  funext index
  exact (CommonNominalSyntax.quote_graph_observe_exact depth (references index)).symm

theorem map_quote_equivalent (layer : Layer Row Index) (references : Index → State Row) :
    CommonNominalCarrier.Equivalent (layer.map references)
      (quoteLayer (fun index => CommonNominalSyntax.graph Row (references index)) layer) :=
  equivalent_of_observe_eq (map_quote_observe layer references)

theorem quoteLayer_congr (layer : Layer Row Index) (first last : Index → Ty)
    (same : ∀ index, CommonNominalCarrier.Equivalent (first index) (last index)) :
    CommonNominalCarrier.Equivalent (quoteLayer first layer) (quoteLayer last layer) := by
  have finite (depth : Nat) : CommonNominalFinite.ProducerEq Common.rowLe
      (CommonNominalCarrier.observeTy depth (quoteLayer first layer))
      (CommonNominalCarrier.observeTy depth (quoteLayer last layer)) := by
    simp only [CommonNominalCarrier.observeTy, quoteLayer, Layer.evalAt_map]
    exact Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans depth _ _
      (fun index => quote_same_at (same index) depth) layer
  exact ⟨fun depth => (finite depth).1, fun depth => (finite depth).2⟩

/-- Congruence is needed rather than covariance: guarded input references
can occur contravariantly in an arrow atom. -/
theorem Body.quote_eval_congr (body : Body slots labels Index)
    (firstPayload lastPayload : Index → Ty) (firstTail lastTail : Fin slots → Ty)
    (payloads : ∀ index, CommonNominalCarrier.Equivalent (firstPayload index) (lastPayload index))
    (tails : ∀ index, CommonNominalCarrier.Equivalent (firstTail index) (lastTail index)) :
    CommonNominalCarrier.Equivalent ((body.quote firstPayload).eval firstTail)
      ((body.quote lastPayload).eval lastTail) := by
  induction body with
  | atom layer => exact quoteLayer_congr layer firstPayload lastPayload payloads
  | ref index => exact tails index
  | union first last ihf ihl =>
      exact ⟨fun depth => (CommonNominalFinite.producerEq_union (finite_same_at ihf depth) (finite_same_at ihl depth)).1,
        fun depth => (CommonNominalFinite.producerEq_union (finite_same_at ihf depth) (finite_same_at ihl depth)).2⟩
  | inter first last ihf ihl =>
      exact ⟨fun depth => (CommonNominalFinite.producerEq_inter (finite_same_at ihf depth) (finite_same_at ihl depth)).1,
        fun depth => (CommonNominalFinite.producerEq_inter (finite_same_at ihf depth) (finite_same_at ihl depth)).2⟩
  | mask hidden body ih => exact CommonNominalCarrier.common_mask_type_congr hidden.names ih
  | record label payload tail ih =>
      exact ⟨fun depth => (CommonNominalFinite.producerEq_record label
          (quote_same_at (payloads payload) depth) (finite_same_at ih depth)).1,
        fun depth => (CommonNominalFinite.producerEq_record label
          (quote_same_at (payloads payload) depth) (finite_same_at ih depth)).2⟩
  | recordDefault label source fallback ih =>
      exact CommonNominalCarrier.common_default_congr label ih (payloads fallback)

theorem tail_solve_congr (graph : CommonNominalPresenceTailElimination.Graph slots labels)
    (first last : Fin slots → Ty) (same : ∀ index, CommonNominalCarrier.Equivalent (first index) (last index))
    (index : Fin slots) :
    CommonNominalCarrier.Equivalent (CommonNominalPresenceTailElimination.solve graph first index)
      (CommonNominalPresenceTailElimination.solve graph last index) := by
  apply CommonNominalTailElimination.maskedEquivalent_common
    (CommonNominalPresenceTailElimination.solve graph first) (CommonNominalPresenceTailElimination.solve graph last) _ index
  intro depth rank env outer actual obs
  have observed : CommonNominalPresenceTailElimination.observeFamily (labels := labels) depth rank env outer obs
      (CommonNominalPresenceTailElimination.solve graph first) =
        CommonNominalPresenceTailElimination.observeFamily depth rank env outer obs
          (CommonNominalPresenceTailElimination.solve graph last) := by
    rw [CommonNominalPresenceTailElimination.observe_solve, CommonNominalPresenceTailElimination.observe_solve,
      CommonNominalPresenceTailElimination.observeFamily_equivalent first last same]
  have atIndex := congrFun observed ((actual, PresenceTailElimination.Mask.empty),
    CommonNominalPresenceTailElimination.Mode.keep)
  simpa only [CommonNominalPresenceTailElimination.observeFamily, PresenceTailElimination.Mask.names_empty,
    List.append_nil, CommonNominalPresenceTailElimination.Mode.observe] using Iff.of_eq atIndex

/-- Internal guarded references and external shared common states are syntax,
not semantic functions or chosen solutions. -/
abbrev Payload (slots : Nat) := Fin slots ⊕ State Row
abbrev Graph (slots labels : Nat) := CommonNominalPresenceTailLayers.Graph slots labels (Payload slots)

def payload (solution : Fin slots → Ty) : Payload slots → Ty :=
  Sum.elim solution (CommonNominalSyntax.graph Row)

def atSolution (graph : Graph slots labels) (solution : Fin slots → Ty) :
    CommonNominalPresenceTailElimination.Graph slots labels := quoteGraph (payload solution) graph

/-- Independent original equations. The very same solution substitutes all
guarded payload references, including negative ones, and all same-depth tails. -/
def Models (graph : Graph slots labels) (solution : Fin slots → Ty) : Prop :=
  ∀ index, CommonNominalCarrier.Equivalent
    (((graph index).quote (payload solution)).eval solution) (solution index)

theorem models_congr (graph : Graph slots labels) (first last : Fin slots → Ty)
    (same : ∀ index, CommonNominalCarrier.Equivalent (first index) (last index)) :
    Models graph first ↔ Models graph last := by
  have payloads : ∀ index, CommonNominalCarrier.Equivalent (payload first index) (payload last index) := by
    intro index
    cases index with
    | inl index => exact same index
    | inr state => exact CommonNominalCarrier.equivalent_refl _
  have bodies := fun index => Body.quote_eval_congr (graph index) (payload first) (payload last)
    first last payloads same
  constructor
  · intro valid index
    exact CommonNominalCarrier.equivalent_trans (CommonNominalCarrier.equivalent_symm (bodies index))
      (CommonNominalCarrier.equivalent_trans (valid index) (same index))
  · intro valid index
    exact CommonNominalCarrier.equivalent_trans (bodies index)
      (CommonNominalCarrier.equivalent_trans (valid index) (CommonNominalCarrier.equivalent_symm (same index)))

def liftParameters (parameters : Fin slots → Ty) : Fin slots → Layer Row (Payload slots) :=
  fun index => (parameters index).map Sum.inr

def solvedBody (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Fin slots → Layer Row (Payload slots) := solveLayers graph (liftParameters parameters)

def references (graph : Graph slots labels) (parameters : Fin slots → Ty) : Payload slots → State Row :=
  CommonNominalSyntax.blockRef (solvedBody graph parameters)

def solveBlock (graph : Graph slots labels) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  fun index => CommonNominalSyntax.graph Row (references graph parameters (.inl index))

theorem solveBlock_unfold (graph : Graph slots labels) (parameters : Fin slots → Ty) (index : Fin slots) :
    solveBlock graph parameters index = (solvedBody graph parameters index).map (references graph parameters) :=
  CommonNominalSyntax.graph_closeBlock (solvedBody graph parameters) index

theorem payload_solveBlock (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    payload (solveBlock graph parameters) =
      fun index => CommonNominalSyntax.graph Row (references graph parameters index) := by
  funext index
  cases index <;> rfl

theorem quoted_parameters_observe (solution parameters : Fin slots → Ty) (depth : Nat) (index : Fin slots) :
    CommonNominalCarrier.observeTy depth (quoteFamily (payload solution) (liftParameters parameters) index) =
      CommonNominalCarrier.observeTy depth (parameters index) := by
  simp only [quoteFamily, liftParameters, quoteLayer, Layer.map_comp, CommonNominalCarrier.observeTy, Layer.evalAt_map]
  congr 1
  funext state
  exact CommonNominalSyntax.quote_graph_observe_exact depth state

theorem quoted_parameters_equivalent (solution parameters : Fin slots → Ty) (index : Fin slots) :
    CommonNominalCarrier.Equivalent (quoteFamily (payload solution) (liftParameters parameters) index) (parameters index) :=
  equivalent_of_observe_eq (fun depth => quoted_parameters_observe solution parameters depth index)

/-- For every original graph and every unrestricted common parameter family,
closing the shared payload block yields a model of the original equations. -/
theorem solveBlock_models (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Models graph (solveBlock graph parameters) := by
  let solution := solveBlock graph parameters
  let quotedParameters := quoteFamily (payload solution) (liftParameters parameters)
  have same (index : Fin slots) : CommonNominalCarrier.Equivalent
      (CommonNominalPresenceTailElimination.solve (atSolution graph solution) quotedParameters index)
      (solution index) := by
    change CommonNominalCarrier.Equivalent
      (CommonNominalPresenceTailElimination.solve (quoteGraph (payload solution) graph)
        (quoteFamily (payload solution) (liftParameters parameters)) index) _
    rw [← CommonNominalPresenceTailLayers.solveLayers_quote graph (liftParameters parameters) (payload solution) index]
    change CommonNominalCarrier.Equivalent (quoteLayer (payload solution) (solvedBody graph parameters index)) _
    rw [payload_solveBlock]
    exact CommonNominalCarrier.equivalent_symm (by
      change CommonNominalCarrier.Equivalent (solveBlock graph parameters index) _
      rw [solveBlock_unfold]
      exact map_quote_equivalent _ _)
  exact (CommonNominalPresenceTailElimination.models_congr (atSolution graph solution) _ solution same).mp
    (CommonNominalPresenceTailElimination.solve_models (atSolution graph solution) quotedParameters)

private theorem map_quote_at_congr (layer : Layer Row Index) (refs : Index → State Row)
    (types : Index → Ty) (depth : Nat)
    (same : ∀ index, CommonNominalFinite.ProducerEq Common.rowLe
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (refs index))
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node (types index)))) :
    CommonNominalFinite.ProducerEq Common.rowLe (CommonNominalCarrier.observeTy depth (layer.map refs))
      (CommonNominalCarrier.observeTy depth (quoteLayer types layer)) := by
  simp only [CommonNominalCarrier.observeTy, quoteLayer, Layer.evalAt_map]
  exact Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans depth _ _ same layer

/-- Every independent regular solution is recovered by choosing its original
root layers as parameters. The depth induction permits negative payload refs. -/
theorem solveBlock_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (valid : Models graph solution) (index : Fin slots) :
    CommonNominalCarrier.Equivalent (solveBlock graph solution index) (solution index) := by
  let quotedParameters := quoteFamily (payload solution) (liftParameters solution)
  have concrete (index : Fin slots) : CommonNominalCarrier.Equivalent
      (CommonNominalPresenceTailElimination.solve (atSolution graph solution) quotedParameters index)
      (solution index) :=
    CommonNominalCarrier.equivalent_trans
      (tail_solve_congr (atSolution graph solution) quotedParameters solution
        (quoted_parameters_equivalent solution solution) index)
      (CommonNominalPresenceTailElimination.solve_retract (atSolution graph solution) solution valid index)
  have finite (depth : Nat) : ∀ index,
      CommonNominalFinite.ProducerEq Common.rowLe
        (CommonNominalCarrier.observeTy depth (solveBlock graph solution index))
        (CommonNominalCarrier.observeTy depth (solution index)) := by
    induction depth with
    | zero =>
        intro index
        have payloads : ∀ item, CommonNominalFinite.ProducerEq Common.rowLe
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) 0 (references graph solution item))
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) 0 (.node (payload solution item))) :=
          fun _ => CommonNominalFinite.producerEq_refl _
        have compared := map_quote_at_congr (solvedBody graph solution index)
          (references graph solution) (payload solution) 0 payloads
        rw [← solveBlock_unfold] at compared
        have quoted := CommonNominalPresenceTailLayers.solveLayers_quote graph (liftParameters solution)
          (payload solution) index
        rw [show quoteLayer (payload solution) (solvedBody graph solution index) =
          CommonNominalPresenceTailElimination.solve (atSolution graph solution) quotedParameters index from quoted] at compared
        exact CommonNominalFinite.producerEq_trans compared (finite_same_at (concrete index) 0)
    | succ depth ih =>
        intro index
        have payloads : ∀ item, CommonNominalFinite.ProducerEq Common.rowLe
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (depth + 1) (references graph solution item))
            (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (depth + 1) (.node (payload solution item))) := by
          intro item
          cases item with
          | inl child => exact ih child
          | inr state =>
              rw [show references graph solution (.inr state) = state from rfl,
                show payload solution (.inr state) = CommonNominalSyntax.graph Row state from rfl,
                CommonNominalSyntax.quote_graph_observe_exact]
              exact CommonNominalFinite.producerEq_refl _
        have compared := map_quote_at_congr (solvedBody graph solution index)
          (references graph solution) (payload solution) (depth + 1) payloads
        rw [← solveBlock_unfold] at compared
        have quoted := CommonNominalPresenceTailLayers.solveLayers_quote graph (liftParameters solution)
          (payload solution) index
        rw [show quoteLayer (payload solution) (solvedBody graph solution index) =
          CommonNominalPresenceTailElimination.solve (atSolution graph solution) quotedParameters index from quoted] at compared
        exact CommonNominalFinite.producerEq_trans compared (finite_same_at (concrete index) (depth + 1))
  exact ⟨fun depth => (finite depth index).1, fun depth => (finite depth index).2⟩

/-- Exact common regular instances for every finite graph and independent
assignment. Guarded payloads and unguarded tails share their slot IDs. The
existential family has only unrestricted common types as parameters. -/
theorem guarded_solved_instances_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Models graph solution ↔
      ∃ parameters : Fin slots → Ty,
        ∀ index, CommonNominalCarrier.Equivalent (solveBlock graph parameters index) (solution index) := by
  constructor
  · intro valid
    exact ⟨solution, solveBlock_retract graph solution valid⟩
  · rintro ⟨parameters, same⟩
    exact (models_congr graph (solveBlock graph parameters) solution same).mp (solveBlock_models graph parameters)

end Yulang.CommonNominalPresenceTailRegular
