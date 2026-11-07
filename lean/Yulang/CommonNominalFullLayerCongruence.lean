import Yulang.CommonNominalLayerCongruence
import Yulang.CommonNominalFullFinitePresence
import Yulang.CommonNominalFullFiniteMaskOrder

/-!
# Payload congruence for a guarded common layer

Every payload assignment is arbitrary finite common syntax. Pointwise
equivalence quantifies all negative ranks and environments, so substitution
is valid also in an arrow domain. No monotonicity in negative payloads is
assumed. Record tails and default sources retain the current constructor
depth; the special depth-zero default approximation is handled explicitly.

This is the local congruence needed by a constructor-depth induction for
guarded regular closure. It does not construct that closure or assert that
the existing same-depth solver already accepts symbolic payload references.
-/

namespace Yulang.CommonNominalFullLayer

open CommonNominalSyntax

universe u v
variable {Row : Type u} {Index : Type v}

theorem evalAt_congr (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFullDemand.Ty Row)
    (same : ∀ index, CommonNominalFullDemand.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) :
    CommonNominalFullDemand.ProducerEq leRow (layer.evalAt depth first) (layer.evalAt depth last) := by
  induction layer with
  | base | float | bottom | top | emptyRecord | exactEmpty => exact CommonNominalFullDemand.producerEq_refl _
  | union left right ihl ihr => exact CommonNominalFullDemand.producerEq_union ihl ihr
  | inter left right ihl ihr => exact CommonNominalFullDemand.producerEq_inter ihl ihr
  | pair left right => exact CommonNominalFullDemand.producerEq_pair (same left) (same right)
  | record label payload tail ih => exact CommonNominalFullDemand.producerEq_record label (same payload) ih
  | recordDefault label source fallback ih =>
      cases depth with
      | zero => exact CommonNominalFullDemand.producerEq_record label (CommonNominalFullDemand.producerEq_refl .bottom) ih
      | succ previous => exact CommonNominalFullDemand.producerEq_recordDefault label ih (same fallback)
  | variant label payload => exact CommonNominalFullDemand.producerEq_variant label (same payload)
  | arrow input incoming output outgoing =>
      exact CommonNominalFullDemand.producerEq_arrow rowRefl rowTrans incoming outgoing (same input) (same output)
  | mask hidden source ih => exact CommonNominalFullDemand.producerEq_mask hidden ih
  | nominal name arguments =>
      have comparison (first last : Index → CommonNominalFullDemand.Ty Row)
          (same : ∀ index, CommonNominalFullDemand.ProducerEq leRow (first index) (last index)) :
          CommonNominalFullDemand.ProducerLe leRow
            (.nominal name (arguments.map (Sum.map first id)))
            (.nominal name (arguments.map (Sum.map last id))) := by
        apply CommonNominalFullDemand.nominal_invariant_backward (leRow := leRow) rowTrans rfl
          (by simp only [List.length_map])
        intro index a b left right
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp left
        have within : index < arguments.length := by simpa only [List.length_map] using bound
        have firstAt : (arguments.map (Sum.map first id))[index]? =
            some (Sum.map first id arguments[index]) := by simp [within]
        have lastAt : (arguments.map (Sum.map last id))[index]? =
            some (Sum.map last id arguments[index]) := by simp [within]
        have aEq := Option.some.inj (left.symm.trans firstAt)
        have bEq := Option.some.inj (right.symm.trans lastAt)
        subst a; subst b
        simp only [List.getElem_map]
        cases original : arguments[index] with
        | inl parameter => exact same parameter
        | inr row => exact ⟨rowRefl row, rowRefl row⟩
      exact ⟨comparison first last same, comparison last first (fun index => ⟨(same index).2, (same index).1⟩)⟩

theorem evalAt_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFullDemand.Ty Row)
    (same : ∀ index, CommonNominalFullDemand.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonNominalFullDemand.Environment Row)
    (observation : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.ProbeAt leRow rank environment (layer.evalAt depth first) observation ↔
      CommonNominalFullDemand.ProbeAt leRow rank environment (layer.evalAt depth last) observation :=
  (CommonNominalFullDemand.producerEq_iff_probe _ _).mp
    (evalAt_congr leRow rowRefl rowTrans depth first last same layer) rank environment observation

theorem evalAt_masked_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFullDemand.Ty Row)
    (same : ∀ index, CommonNominalFullDemand.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonNominalFullDemand.Environment Row)
    (hidden : List Nat) (observation : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth first) observation ↔
      CommonNominalFullDemand.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth last) observation := by
  simpa only [CommonNominalFullDemand.probeAt_mask] using
    (CommonNominalFullDemand.producerEq_iff_probe _ _).mp
      (CommonNominalFullDemand.producerEq_mask hidden (evalAt_congr leRow rowRefl rowTrans depth first last same layer))
      rank environment observation

end Yulang.CommonNominalFullLayer
