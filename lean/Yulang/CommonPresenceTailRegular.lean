import Yulang.CommonPresenceTailLayers
import Yulang.CommonLayerCongruence

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

namespace Yulang.CommonPresenceTailRegular

open Common (Ty Row)
open CommonSyntax (Layer State)
open CommonPresenceTailLayers (Body quoteLayer quoteGraph quoteFamily solveLayers)

variable {slots labels : Nat} {Index : Type}

private theorem equivalent_of_observe_eq {first last : Ty}
    (same : ∀ depth, Common.observeTy depth first = Common.observeTy depth last) :
    Common.Equivalent first last := by
  constructor <;> intro depth
  · rw [same depth]
    exact CommonFinite.producerLe_refl _
  · rw [same depth]
    exact CommonFinite.producerLe_refl _

private theorem finite_same_at (same : Common.Equivalent first last) (depth : Nat) :
    CommonFinite.ProducerEq Common.rowLe (Common.observeTy depth first) (Common.observeTy depth last) :=
  ⟨same.1 depth, same.2 depth⟩

private theorem quote_same_at (same : Common.Equivalent first last) (depth : Nat) :
    CommonFinite.ProducerEq Common.rowLe
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node first))
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node last)) :=
  ⟨Common.quote_observe_le same.1 depth, Common.quote_observe_le same.2 depth⟩

/-- Replacing a shared state reference by a quoted copy of its actual root
layer changes no finite observation and does not add a guard. -/
theorem map_quote_observe (layer : Layer Row Index) (references : Index → State Row) (depth : Nat) :
    Common.observeTy depth (layer.map references) =
      Common.observeTy depth (quoteLayer (fun index => CommonSyntax.graph Row (references index)) layer) := by
  simp only [Common.observeTy, quoteLayer, Layer.evalAt_map]
  congr 1
  funext index
  exact (CommonSyntax.quote_graph_observe_exact depth (references index)).symm

theorem map_quote_equivalent (layer : Layer Row Index) (references : Index → State Row) :
    Common.Equivalent (layer.map references)
      (quoteLayer (fun index => CommonSyntax.graph Row (references index)) layer) :=
  equivalent_of_observe_eq (map_quote_observe layer references)

theorem quoteLayer_congr (layer : Layer Row Index) (first last : Index → Ty)
    (same : ∀ index, Common.Equivalent (first index) (last index)) :
    Common.Equivalent (quoteLayer first layer) (quoteLayer last layer) := by
  have finite (depth : Nat) : CommonFinite.ProducerEq Common.rowLe
      (Common.observeTy depth (quoteLayer first layer))
      (Common.observeTy depth (quoteLayer last layer)) := by
    simp only [Common.observeTy, quoteLayer, Layer.evalAt_map]
    exact Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans depth _ _
      (fun index => quote_same_at (same index) depth) layer
  exact ⟨fun depth => (finite depth).1, fun depth => (finite depth).2⟩

/-- Congruence is needed rather than covariance: guarded input references
can occur contravariantly in an arrow atom. -/
theorem Body.quote_eval_congr (body : Body slots labels Index)
    (firstPayload lastPayload : Index → Ty) (firstTail lastTail : Fin slots → Ty)
    (payloads : ∀ index, Common.Equivalent (firstPayload index) (lastPayload index))
    (tails : ∀ index, Common.Equivalent (firstTail index) (lastTail index)) :
    Common.Equivalent ((body.quote firstPayload).eval firstTail)
      ((body.quote lastPayload).eval lastTail) := by
  induction body with
  | atom layer => exact quoteLayer_congr layer firstPayload lastPayload payloads
  | ref index => exact tails index
  | union first last ihf ihl =>
      exact ⟨fun depth => (CommonFinite.producerEq_union (finite_same_at ihf depth) (finite_same_at ihl depth)).1,
        fun depth => (CommonFinite.producerEq_union (finite_same_at ihf depth) (finite_same_at ihl depth)).2⟩
  | inter first last ihf ihl =>
      exact ⟨fun depth => (CommonFinite.producerEq_inter (finite_same_at ihf depth) (finite_same_at ihl depth)).1,
        fun depth => (CommonFinite.producerEq_inter (finite_same_at ihf depth) (finite_same_at ihl depth)).2⟩
  | mask hidden body ih => exact Common.common_mask_type_congr hidden.names ih
  | record label payload tail ih =>
      exact ⟨fun depth => (CommonFinite.producerEq_record label
          (quote_same_at (payloads payload) depth) (finite_same_at ih depth)).1,
        fun depth => (CommonFinite.producerEq_record label
          (quote_same_at (payloads payload) depth) (finite_same_at ih depth)).2⟩
  | recordDefault label source fallback ih =>
      exact Common.common_default_congr label ih (payloads fallback)

theorem tail_solve_congr (graph : CommonPresenceTailElimination.Graph slots labels)
    (first last : Fin slots → Ty) (same : ∀ index, Common.Equivalent (first index) (last index))
    (index : Fin slots) :
    Common.Equivalent (CommonPresenceTailElimination.solve graph first index)
      (CommonPresenceTailElimination.solve graph last index) := by
  apply CommonTailElimination.maskedEquivalent_common
    (CommonPresenceTailElimination.solve graph first) (CommonPresenceTailElimination.solve graph last) _ index
  intro depth rank env outer actual obs
  have observed : CommonPresenceTailElimination.observeFamily (labels := labels) depth rank env outer obs
      (CommonPresenceTailElimination.solve graph first) =
        CommonPresenceTailElimination.observeFamily depth rank env outer obs
          (CommonPresenceTailElimination.solve graph last) := by
    rw [CommonPresenceTailElimination.observe_solve, CommonPresenceTailElimination.observe_solve,
      CommonPresenceTailElimination.observeFamily_equivalent first last same]
  have atIndex := congrFun observed ((actual, PresenceTailElimination.Mask.empty),
    CommonPresenceTailElimination.Mode.keep)
  simpa only [CommonPresenceTailElimination.observeFamily, PresenceTailElimination.Mask.names_empty,
    List.append_nil, CommonPresenceTailElimination.Mode.observe] using Iff.of_eq atIndex

/-- Internal guarded references and external shared common states are syntax,
not semantic functions or chosen solutions. -/
abbrev Payload (slots : Nat) := Fin slots ⊕ State Row
abbrev Graph (slots labels : Nat) := CommonPresenceTailLayers.Graph slots labels (Payload slots)

def payload (solution : Fin slots → Ty) : Payload slots → Ty :=
  Sum.elim solution (CommonSyntax.graph Row)

def atSolution (graph : Graph slots labels) (solution : Fin slots → Ty) :
    CommonPresenceTailElimination.Graph slots labels := quoteGraph (payload solution) graph

/-- Independent original equations. The very same solution substitutes all
guarded payload references, including negative ones, and all same-depth tails. -/
def Models (graph : Graph slots labels) (solution : Fin slots → Ty) : Prop :=
  ∀ index, Common.Equivalent
    (((graph index).quote (payload solution)).eval solution) (solution index)

theorem models_congr (graph : Graph slots labels) (first last : Fin slots → Ty)
    (same : ∀ index, Common.Equivalent (first index) (last index)) :
    Models graph first ↔ Models graph last := by
  have payloads : ∀ index, Common.Equivalent (payload first index) (payload last index) := by
    intro index
    cases index with
    | inl index => exact same index
    | inr state => exact Common.equivalent_refl _
  have bodies := fun index => Body.quote_eval_congr (graph index) (payload first) (payload last)
    first last payloads same
  constructor
  · intro valid index
    exact Common.equivalent_trans (Common.equivalent_symm (bodies index))
      (Common.equivalent_trans (valid index) (same index))
  · intro valid index
    exact Common.equivalent_trans (bodies index)
      (Common.equivalent_trans (valid index) (Common.equivalent_symm (same index)))

def liftParameters (parameters : Fin slots → Ty) : Fin slots → Layer Row (Payload slots) :=
  fun index => (parameters index).map Sum.inr

def solvedBody (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Fin slots → Layer Row (Payload slots) := solveLayers graph (liftParameters parameters)

def references (graph : Graph slots labels) (parameters : Fin slots → Ty) : Payload slots → State Row :=
  CommonSyntax.blockRef (solvedBody graph parameters)

def solveBlock (graph : Graph slots labels) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  fun index => CommonSyntax.graph Row (references graph parameters (.inl index))

theorem solveBlock_unfold (graph : Graph slots labels) (parameters : Fin slots → Ty) (index : Fin slots) :
    solveBlock graph parameters index = (solvedBody graph parameters index).map (references graph parameters) :=
  CommonSyntax.graph_closeBlock (solvedBody graph parameters) index

theorem payload_solveBlock (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    payload (solveBlock graph parameters) =
      fun index => CommonSyntax.graph Row (references graph parameters index) := by
  funext index
  cases index <;> rfl

theorem quoted_parameters_observe (solution parameters : Fin slots → Ty) (depth : Nat) (index : Fin slots) :
    Common.observeTy depth (quoteFamily (payload solution) (liftParameters parameters) index) =
      Common.observeTy depth (parameters index) := by
  simp only [quoteFamily, liftParameters, quoteLayer, Layer.map_comp, Common.observeTy, Layer.evalAt_map]
  congr 1
  funext state
  exact CommonSyntax.quote_graph_observe_exact depth state

theorem quoted_parameters_equivalent (solution parameters : Fin slots → Ty) (index : Fin slots) :
    Common.Equivalent (quoteFamily (payload solution) (liftParameters parameters) index) (parameters index) :=
  equivalent_of_observe_eq (fun depth => quoted_parameters_observe solution parameters depth index)

/-- For every original graph and every unrestricted common parameter family,
closing the shared payload block yields a model of the original equations. -/
theorem solveBlock_models (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Models graph (solveBlock graph parameters) := by
  let solution := solveBlock graph parameters
  let quotedParameters := quoteFamily (payload solution) (liftParameters parameters)
  have same (index : Fin slots) : Common.Equivalent
      (CommonPresenceTailElimination.solve (atSolution graph solution) quotedParameters index)
      (solution index) := by
    change Common.Equivalent
      (CommonPresenceTailElimination.solve (quoteGraph (payload solution) graph)
        (quoteFamily (payload solution) (liftParameters parameters)) index) _
    rw [← CommonPresenceTailLayers.solveLayers_quote graph (liftParameters parameters) (payload solution) index]
    change Common.Equivalent (quoteLayer (payload solution) (solvedBody graph parameters index)) _
    rw [payload_solveBlock]
    exact Common.equivalent_symm (by
      change Common.Equivalent (solveBlock graph parameters index) _
      rw [solveBlock_unfold]
      exact map_quote_equivalent _ _)
  exact (CommonPresenceTailElimination.models_congr (atSolution graph solution) _ solution same).mp
    (CommonPresenceTailElimination.solve_models (atSolution graph solution) quotedParameters)

private theorem map_quote_at_congr (layer : Layer Row Index) (refs : Index → State Row)
    (types : Index → Ty) (depth : Nat)
    (same : ∀ index, CommonFinite.ProducerEq Common.rowLe
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (refs index))
      (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node (types index)))) :
    CommonFinite.ProducerEq Common.rowLe (Common.observeTy depth (layer.map refs))
      (Common.observeTy depth (quoteLayer types layer)) := by
  simp only [Common.observeTy, quoteLayer, Layer.evalAt_map]
  exact Layer.evalAt_congr Common.rowLe Common.rowLe_refl Common.rowLe_trans depth _ _ same layer

/-- Every independent regular solution is recovered by choosing its original
root layers as parameters. The depth induction permits negative payload refs. -/
theorem solveBlock_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (valid : Models graph solution) (index : Fin slots) :
    Common.Equivalent (solveBlock graph solution index) (solution index) := by
  let quotedParameters := quoteFamily (payload solution) (liftParameters solution)
  have concrete (index : Fin slots) : Common.Equivalent
      (CommonPresenceTailElimination.solve (atSolution graph solution) quotedParameters index)
      (solution index) :=
    Common.equivalent_trans
      (tail_solve_congr (atSolution graph solution) quotedParameters solution
        (quoted_parameters_equivalent solution solution) index)
      (CommonPresenceTailElimination.solve_retract (atSolution graph solution) solution valid index)
  have finite (depth : Nat) : ∀ index,
      CommonFinite.ProducerEq Common.rowLe
        (Common.observeTy depth (solveBlock graph solution index))
        (Common.observeTy depth (solution index)) := by
    induction depth with
    | zero =>
        intro index
        have payloads : ∀ item, CommonFinite.ProducerEq Common.rowLe
            (CommonSyntax.observe (CommonSyntax.graph Row) 0 (references graph solution item))
            (CommonSyntax.observe (CommonSyntax.graph Row) 0 (.node (payload solution item))) :=
          fun _ => CommonFinite.producerEq_refl _
        have compared := map_quote_at_congr (solvedBody graph solution index)
          (references graph solution) (payload solution) 0 payloads
        rw [← solveBlock_unfold] at compared
        have quoted := CommonPresenceTailLayers.solveLayers_quote graph (liftParameters solution)
          (payload solution) index
        rw [show quoteLayer (payload solution) (solvedBody graph solution index) =
          CommonPresenceTailElimination.solve (atSolution graph solution) quotedParameters index from quoted] at compared
        exact CommonFinite.producerEq_trans compared (finite_same_at (concrete index) 0)
    | succ depth ih =>
        intro index
        have payloads : ∀ item, CommonFinite.ProducerEq Common.rowLe
            (CommonSyntax.observe (CommonSyntax.graph Row) (depth + 1) (references graph solution item))
            (CommonSyntax.observe (CommonSyntax.graph Row) (depth + 1) (.node (payload solution item))) := by
          intro item
          cases item with
          | inl child => exact ih child
          | inr state =>
              rw [show references graph solution (.inr state) = state from rfl,
                show payload solution (.inr state) = CommonSyntax.graph Row state from rfl,
                CommonSyntax.quote_graph_observe_exact]
              exact CommonFinite.producerEq_refl _
        have compared := map_quote_at_congr (solvedBody graph solution index)
          (references graph solution) (payload solution) (depth + 1) payloads
        rw [← solveBlock_unfold] at compared
        have quoted := CommonPresenceTailLayers.solveLayers_quote graph (liftParameters solution)
          (payload solution) index
        rw [show quoteLayer (payload solution) (solvedBody graph solution index) =
          CommonPresenceTailElimination.solve (atSolution graph solution) quotedParameters index from quoted] at compared
        exact CommonFinite.producerEq_trans compared (finite_same_at (concrete index) (depth + 1))
  exact ⟨fun depth => (finite depth index).1, fun depth => (finite depth index).2⟩

/-- Exact common regular instances for every finite graph and independent
assignment. Guarded payloads and unguarded tails share their slot IDs. The
existential family has only unrestricted common types as parameters. -/
theorem guarded_solved_instances_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Models graph solution ↔
      ∃ parameters : Fin slots → Ty,
        ∀ index, Common.Equivalent (solveBlock graph parameters index) (solution index) := by
  constructor
  · intro valid
    exact ⟨solution, solveBlock_retract graph solution valid⟩
  · rintro ⟨parameters, same⟩
    exact (models_congr graph (solveBlock graph parameters) solution same).mp (solveBlock_models graph parameters)

end Yulang.CommonPresenceTailRegular
