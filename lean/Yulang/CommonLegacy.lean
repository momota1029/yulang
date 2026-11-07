import Yulang.Common
import Yulang.CommonFiniteEmbedding
import Yulang.ProducerContextualRegular

/-!
# Exact embedding of every old regular contextual type

The graph translation preserves each finite constructor observation literally.
The finite embedding theorem then gives both directions of the demand order,
including arbitrary new finite/regular demand parameters and negative arrow
positions. Old types are not restricted to proper record spines.
-/

namespace Yulang.CommonSyntax

universe u v

theorem ofOldLayer_evalAt {Row : Type u} {Index : Type v}
    (depth : Nat) (assignment : Index → StructuralBase.Ty Row)
    (type : RegularValueTypes.Layer Row Index) :
    (ofOldLayer type).evalAt depth (fun index => CommonFiniteEmbedding.embedOld (assignment index)) =
      CommonFiniteEmbedding.embedOld (type.eval assignment) := by
  induction type <;> simp [ofOldLayer, Layer.evalAt,
    RegularValueTypes.Layer.eval, CommonFiniteEmbedding.embedOld, *]

theorem legacy_observe_exact {Row : Type u} (depth : Nat)
    (state : RegularInferenceModel.State Row) :
    observe (graph Row) depth (.legacy state) =
      CommonFiniteEmbedding.embedOld
        (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth state) := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [observe, graph, Layer.evalAt_map, RegularValueTypes.observe]
      have lifted : (observe (graph Row) depth ∘ State.legacy) =
          fun state => CommonFiniteEmbedding.embedOld
            (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth state) := by
        funext state
        exact ih state
      rw [lifted]
      exact ofOldLayer_evalAt depth _ _

end Yulang.CommonSyntax

namespace Yulang.Common

theorem embedOld_observe_exact (depth : Nat) (type : RegularInferenceModel.Ty Row) :
    observeTy depth (embedOld type) =
      CommonFiniteEmbedding.embedOld
        (type.eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth)) := by
  unfold observeTy embedOld CommonSyntax.embedOld
  rw [CommonSyntax.Layer.evalAt_map]
  have lifted : (CommonSyntax.observe (CommonSyntax.graph Row) depth ∘ CommonSyntax.State.legacy) =
      fun state => CommonFiniteEmbedding.embedOld
        (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth state) := by
    funext state
    exact CommonSyntax.legacy_observe_exact depth state
  rw [lifted]
  exact CommonSyntax.ofOldLayer_evalAt depth _ _

theorem contextual_embedding_exact (source target : RegularInferenceModel.Ty Row) :
    model.subTy (embedOld source) (embedOld target) ↔
      ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) rowLe source target := by
  constructor
  · intro below depth
    have atDepth := below depth
    rw [embedOld_observe_exact, embedOld_observe_exact] at atDepth
    exact (CommonFiniteEmbedding.contextual_embedding_exact rowLe _ _).mp atDepth
  · intro below depth
    change CommonFinite.ProducerLe rowLe (observeTy depth (embedOld source))
      (observeTy depth (embedOld target))
    rw [embedOld_observe_exact, embedOld_observe_exact]
    exact (CommonFiniteEmbedding.contextual_embedding_exact rowLe _ _).mpr (below depth)

theorem contextual_equivalence_exact (source target : RegularInferenceModel.Ty Row) :
    Equivalent (embedOld source) (embedOld target) ↔
      ProducerContextualRegular.ProducerEq (RegularInferenceModel.graph Row) rowLe source target := by
  exact and_congr (contextual_embedding_exact source target) (contextual_embedding_exact target source)

end Yulang.Common
