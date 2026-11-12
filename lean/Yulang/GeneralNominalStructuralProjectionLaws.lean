import Yulang.GeneralNominalRecursiveInspection

/-! Structural payload projection remains exact with arbitrary nominal and
recursive children in the full carrier. -/
namespace Yulang.GeneralNominalStructuralProjectionLaws

open CommonNominalFullCarrier GeneralNominalRecursiveInspection

theorem finite_record_payload (label : Nat) (a b rest tail : CommonNominalFullDemand.Ty Row)
    (below : CommonNominalFullDemand.ProducerLe Common.rowLe (.record label a rest) (.record label b tail)) :
    CommonNominalFullDemand.ProducerLe Common.rowLe a b := by
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env observation accepted
  have lifted : CommonNominalFullDemand.ProbeAt Common.rowLe rank env (.record label b tail) (.field label observation) := by
    simpa using accepted
  have valid := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp below rank env (.field label observation) lifted
  simpa using valid

theorem record_payload (label : Nat) (a b rest tail : Ty)
    (below : Subtype (record label a rest) (record label b tail)) : Subtype a b :=
  fun depth => finite_record_payload label _ _ _ _ (below (depth+1))

theorem required_equivalent (label : Nat) (first last : Ty) :
    Equivalent (required label first) (required label last) ↔ Equivalent first last := by
  constructor
  · intro equal
    exact ⟨record_payload label _ _ _ _ equal.1,record_payload label _ _ _ _ equal.2⟩
  · intro equal
    exact ⟨common_record_mono label equal.1 (subtype_refl _),common_record_mono label equal.2 (subtype_refl _)⟩

theorem singleton_shape (label : Nat) (payload : Ty) :
    shapeValue (.record [label]) [payload] = required label payload := by
  simp [shapeValue,GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,List.ofFn_succ]
  rfl

theorem record_observation (model : GeneralNominalCommonBridge.Assignment) (parent : Origin)
    (label : Nat) (actual payload : Ty)
    (source : ∀ value, Observes model parent value → Equivalent value (required label payload))
    (seen : Observes model (.structural parent (.record [label]) 0) actual) : Equivalent actual payload := by
  cases seen with
  | structural seen size equal found =>
      obtain ⟨head,rest⟩ := List.length_eq_one_iff.mp size
      subst rest
      have same : head = actual := Option.some.inj found
      subst head
      rw [singleton_shape] at equal
      have original := source _ seen
      exact (required_equivalent label actual payload).mp
        ⟨subtype_trans equal.2 original.1,subtype_trans original.2 equal.1⟩

end Yulang.GeneralNominalStructuralProjectionLaws
