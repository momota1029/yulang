import Yulang.CommonLegacyLayerErasure

/-! A regular legacy interpretation of arbitrary Common witnesses. -/

namespace Yulang.CommonLegacyRegularErasure

universe u v
open CommonSyntax (Layer)
open CommonPayloadProjection (Payload)
open CommonLegacyLayerErasure (erase evalOld evalLayer payloadRefs)
open CommonLegacyGraphSupport (refs oldRefs FiniteAt Closed)
open CommonLegacyTruncation (truncate)

def graph (source : CommonSyntax.Graph Row Index) : RegularValueTypes.Graph Row (Payload Index) :=
  fun payload => evalLayer (fun index => erase [] (source index)) payload

/-- The regular erasure observes the original graph one constructor step
later and then truncates to the requested old depth. All masks, defaults,
negative children and arbitrary graphs are included. -/
theorem observe_erasure (source : CommonSyntax.Graph Row Index) (depth : Nat)
    (layer : Layer Row Index) (hidden : List Nat) :
    (erase hidden layer).eval (RegularValueTypes.observe (graph source) depth) =
      truncate depth (CommonLegacyFiniteErasure.erase hidden
        (layer.evalAt (depth + 1) (CommonSyntax.observe source (depth + 1)))) := by
  have truncateEval (depth : Nat) (layer : RegularValueTypes.Layer Row (Payload Index))
      (values : Payload Index → StructuralBase.Ty Row) :
      truncate depth (layer.eval values) = layer.eval (fun index =>
        match depth with | 0 => .bottom | d + 1 => truncate d (values index)) := by
    induction layer <;> simp_all [truncate, RegularValueTypes.Layer.eval]
    all_goals cases depth <;> simp
  induction depth generalizing layer hidden with
  | zero =>
      rw [CommonLegacyLayerErasure.eval_erasure, truncateEval]
      rfl
  | succ depth ih =>
      rw [CommonLegacyLayerErasure.eval_erasure, truncateEval]
      apply congrArg (fun values => (erase hidden layer).eval values)
      funext payload
      change (evalLayer (fun index => erase [] (source index)) payload).eval
          (RegularValueTypes.observe (graph source) depth) =
        truncate depth (evalOld (fun index => CommonLegacyFiniteErasure.erase []
          (CommonSyntax.observe source (depth + 2) index)) payload)
      induction payload with
      | ref index => exact ih (source index) []
      | bottom | top => rfl
      | union first last ihf ihl =>
          simp only [evalLayer, evalOld, RegularValueTypes.Layer.eval, truncate, ihf, ihl]
      | inter first last ihf ihl =>
          simp only [evalLayer, evalOld, RegularValueTypes.Layer.eval, truncate, ihf, ihl]

/-- Erasure preserves finite closed support. Its payload states need no
additional closure under arbitrary lattice expressions. -/
theorem graph_finite_support (source : CommonSyntax.Graph Row Index) (root : Index)
    (supported : FiniteAt (fun state => refs (source state)) root) :
    FiniteAt (fun payload => oldRefs (graph source payload)) (.ref root) := by
  obtain ⟨states, member, closed⟩ := supported
  let payloads := Payload.ref root :: states.flatMap (fun state => oldRefs (erase [] (source state)))
  have contained (payload : Payload Index) (included : payload ∈ payloads) :
      ∀ index ∈ payloadRefs payload, index ∈ states := by
    rcases List.mem_cons.mp included with rfl | included
    · simpa [payloadRefs] using member
    · obtain ⟨state, stateMember, payloadMember⟩ := List.mem_flatMap.mp included
      exact (CommonLegacyLayerErasure.erase_support (fun index => index ∈ states)
        (source state) (closed state stateMember) []).1 payload payloadMember
  have references (payload : Payload Index) :
      oldRefs (graph source payload) =
        (payloadRefs payload).flatMap (fun index => oldRefs (erase [] (source index))) := by
    induction payload <;> simp_all [graph, evalLayer, payloadRefs, oldRefs,
      CommonSyntax.ofOldLayer, refs]
  refine ⟨payloads, List.mem_cons_self, ?_⟩
  intro payload included child childMember
  change child ∈ oldRefs (graph source payload) at childMember
  rw [references] at childMember
  obtain ⟨index, indexMember, childMember⟩ := List.mem_flatMap.mp childMember
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨index, contained payload included index indexMember, childMember⟩)

/-- An actual old regular type, chosen from the proved finite graph
representation. It is not an assumed interpolation witness. -/
noncomputable def eraseType (type : CommonSyntax.Ty Row) : RegularInferenceModel.Ty Row :=
  Classical.choose (CommonLegacyGraphSupport.old_representative
    (graph (CommonSyntax.graph Row)) (.ref (.node type))
    (graph_finite_support (CommonSyntax.graph Row) (.node type)
      (CommonLegacyGraphSupport.common_finite_support (.node type))))

/-- Every chosen old value retains exactly the observations of the erased
graph. Both the old value and finite support were constructed above. -/
theorem eraseType_observe (type : CommonSyntax.Ty Row) (depth : Nat) :
    (eraseType type).eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth) =
      (erase [] type).eval (RegularValueTypes.observe (graph (CommonSyntax.graph Row)) depth) :=
  Classical.choose_spec (CommonLegacyGraphSupport.old_representative
    (graph (CommonSyntax.graph Row)) (.ref (.node type))
    (graph_finite_support (CommonSyntax.graph Row) (.node type)
      (CommonLegacyGraphSupport.common_finite_support (.node type)))) depth

/-- Arbitrary Common comparisons map to old contextual comparisons. The
construction retains all rows, permits every regular witness, and needs no
source restriction or extra comparison premises. -/
theorem eraseType_mono (leRow : Row → Row → Prop) (source target : CommonSyntax.Ty Row)
    (below : ∀ depth, CommonFinite.ProducerLe leRow
      (source.evalAt depth (CommonSyntax.observe (CommonSyntax.graph Row) depth))
      (target.evalAt depth (CommonSyntax.observe (CommonSyntax.graph Row) depth))) :
    ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow
      (eraseType source) (eraseType target) := by
  intro depth
  apply (ProducerContextual.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  change ProducerContextual.ProbeAt leRow rank env
    ((eraseType source).eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth)) obs
  rw [eraseType_observe, observe_erasure]
  change ProducerContextual.ProbeAt leRow rank env
    ((eraseType target).eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth)) obs at accepted
  rw [eraseType_observe, observe_erasure] at accepted
  exact CommonLegacyTruncation.truncate_compare leRow rank depth _ _
    (CommonLegacyFiniteErasure.erase_compare leRow rank _ _
      ((CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) rank)) env obs accepted

/-- Embedding an old regular type and erasing it recovers every old
observation literally, including arbitrarily nested negative positions. -/
theorem eraseType_embed_observe (type : RegularInferenceModel.Ty Row) (depth : Nat) :
    (eraseType (CommonSyntax.embedOld type)).eval
        (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth) =
      type.eval (RegularValueTypes.observe (RegularInferenceModel.graph Row) depth) := by
  have eraseOld (layer : RegularValueTypes.Layer Row (RegularInferenceModel.State Row)) :
      erase [] ((CommonSyntax.ofOldLayer layer).map CommonSyntax.State.legacy) =
        layer.map (fun state => Payload.ref (CommonSyntax.State.legacy state)) := by
    induction layer <;> simp_all [erase, CommonSyntax.ofOldLayer, Layer.map,
      RegularValueTypes.Layer.map]
  have morphism (state : RegularInferenceModel.State Row) :
      (RegularInferenceModel.graph Row state).map (fun state => Payload.ref (CommonSyntax.State.legacy state)) =
        graph (CommonSyntax.graph Row) (.ref (.legacy state)) :=
    (eraseOld (RegularInferenceModel.graph Row state)).symm
  rw [eraseType_observe]
  change (erase [] ((CommonSyntax.ofOldLayer type).map CommonSyntax.State.legacy)).eval _ = _
  rw [eraseOld, RegularValueTypes.Layer.eval_map]
  apply congrArg (fun values => type.eval values)
  funext state
  exact RegularValueTypes.observe_morphism (graph := RegularInferenceModel.graph Row)
    (graph (CommonSyntax.graph Row)) (fun state => Payload.ref (CommonSyntax.State.legacy state))
    morphism depth state

end Yulang.CommonLegacyRegularErasure
